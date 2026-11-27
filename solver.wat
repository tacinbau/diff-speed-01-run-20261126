;; Full-WASM Myers diff — written in this session for the
;; make.fun diff-speed-01-run-20261126 entry.
;;
;; Unlike the v1 prototype (WASM search only, JS tokenize/intern/format),
;; this module does the WHOLE pipeline in WebAssembly: the JS side only
;; UTF-8-encodes the two texts into linear memory, calls solve() once per
;; case, and UTF-8-decodes the patch out. That removes the ~150-200 ms of
;; JS string/Map work per set that v1 still paid.
;;
;; Pipeline inside solve(oldPtr, oldLen, newPtr, newLen, outPtr, dMaxHint):
;;   1. tokenize both texts in memory (scan for \n) and intern every
;;      distinct line to an integer id with an open-addressing hash table
;;      (FxHash over the line bytes, full byte-compare on hash hit, so
;;      interning is exact, never probabilistic).
;;   2. common prefix / suffix trim on the id arrays.
;;   3. banded forward Myers search over the id arrays (same compact
;;      triangular rows as v1), unbanded restart on a band miss.
;;   4. backtrack to runs, reverse + merge, add the prefix/suffix keeps.
;;   5. format the makefun-diff/1 patch straight into the output buffer.
;;
;; Fixed memory layout (initial memory 4096 pages = 256 MiB; the V region
;; grows with memory.grow if an unbanded retry ever needs it):
;;   0x000000  scratch (itoa temp, 4 KiB)
;;   0x001000  IN_OLD    old text bytes (up to ~2 MiB)
;;   0x200000  IN_NEW    new text bytes (up to ~2 MiB)
;;   0x400000  SPANS_OLD line-start offsets, i32 each (+1 sentinel)
;;   0x500000  IDS_OLD   line ids, i32 each
;;   0x600000  SPANS_NEW line-start offsets, i32 each (+1 sentinel)
;;   0x700000  IDS_NEW   line ids, i32 each
;;   0x800000  TABLE     intern hash table, 131072 entries x 24 B
;;   0xC00000  RUNS      backtrack output, (kind,count) i32 pairs, reversed
;;   0xC20000  RUNS_FINAL forward merged runs (+ prefix/suffix keeps)
;;   0xC40000  CHANGES   (o,p,dels,ins) i32 quads for the formatter
;;   0xD00000  OUT       patch bytes (8 MiB)
;;   0x2000000 V         triangular furthest-x rows (grows as needed)
;;
;; solve() returns one i64: (outLen << 32) | D, where D is the edit
;; distance of the middle slice (0 when the texts are identical after the
;; trim). The JS side keeps lastD and passes the next dMaxHint.

(module
  (memory (export "memory") 4096)

  ;; ---- layout constants (kept in sync with the JS loader) ----
  (global $SCRATCH i32 (i32.const 0))
  (global $IN_OLD i32 (i32.const 4096))
  (global $IN_NEW i32 (i32.const 2097152))
  (global $SPANS_OLD i32 (i32.const 4194304))
  (global $IDS_OLD i32 (i32.const 5242880))
  (global $SPANS_NEW i32 (i32.const 6291456))
  (global $IDS_NEW i32 (i32.const 7340032))
  (global $TABLE i32 (i32.const 8388608))
  (global $TABLE_CAP i32 (i32.const 131072))
  (global $TABLE_MASK i32 (i32.const 131071))
  (global $RUNS i32 (i32.const 12582912))
  (global $RUNS_FINAL i32 (i32.const 12648448))
  (global $CHANGES i32 (i32.const 12713984))
  (global $OUT i32 (i32.const 13631488))
  (global $V i32 (i32.const 33554432))

  ;; v4: per-id COUNTS (countOld, countNew, firstPosNew) i32 x3, cap 262144.
  (global $COUNTS i32 (i32.const 30408704))

  ;; v4b anchor scratch (all in the free 0x1500000-0x1D00000 region):
  ;;   CANDS: candidate (i, j) pairs, cap 65534. ANCHORS: the LIS.
  ;;   TAILS: patience tails (j, candIdx). PREV: LIS predecessor index.
  ;;   WAYPOINTS: (d, k) pairs for the anchor band.
  (global $CANDS i32 (i32.const 22020096))
  (global $ANCHORS i32 (i32.const 22544384))
  (global $TAILS i32 (i32.const 23068672))
  (global $PREV i32 (i32.const 23592960))
  (global $WAYPOINTS i32 (i32.const 23855104))
  (global $WP_PTR i32 (i32.const 23855104))
  (global $WP_MARGIN i32 (i32.const 32))
  (global $WP_COUNT (mut i32) (i32.const 0))
  (global $D_ANCHOR (mut i32) (i32.const 0))
  (global $N_ANCHORS (mut i32) (i32.const 0))

  ;; v5 patience scratch (free 0x1B00000-0x1D00000 region):
  ;;   KPAT: patience-path k(d) table, i32 per depth, cap ~262k depths.
  ;;   DP_TBL: per-gap DP table, (DP_CAP+1)^2 i32 entries max.
  ;;   KP_MARGIN: half-width of the patience band (2x the measured max
  ;;   DP deviation of 12). DP_CAP: largest gap side the DP handles.
  (global $KPAT i32 (i32.const 28311552))
  (global $DP_TBL i32 (i32.const 29360128))
  (global $KP_MARGIN i32 (i32.const 24))
  (global $DP_CAP i32 (i32.const 200))

  ;; Next interned id within the current solve (reset per solve).
  (global $next_id (mut i32) (i32.const 0))

  ;; tri(d) = d*(d+1)/2, computed in i64 so the intermediate cannot wrap.
  (func $tri (param $d i32) (result i32)
    (local $t i64)
    local.get $d
    i64.extend_i32_u
    local.tee $t
    i64.const 1
    i64.add
    local.get $t
    i64.mul
    i64.const 2
    i64.div_u
    i32.wrap_i64)

  ;; Grow linear memory so that `bytes` total bytes exist.
  (func $ensure_mem (param $bytes i32)
    (local $have i32)
    (local $need i32)
    memory.size
    i32.const 16
    i32.shl
    local.set $have
    local.get $bytes
    local.get $have
    i32.gt_s
    if
      local.get $bytes
      local.get $have
      i32.sub
      i32.const 65535
      i32.add
      i32.const 16
      i32.shr_u
      local.set $need
      local.get $need
      memory.grow
      i32.const -1
      i32.eq
      if unreachable end
    end)

  ;; ---- hashing / interning -------------------------------------------
  ;; FxHash over bytes: 8-byte chunks, then the tail byte by byte.
  ;; h starts at the FxHash seed so even an empty line hashes non-zero
  ;; (0 marks an empty table slot).
  (func $hash_bytes (param $ptr i32) (param $len i32) (result i64)
    (local $h i64)
    (local $p i32)
    (local $n i32)
    i64.const 0x517cc1b727220a95
    local.set $h
    local.get $ptr
    local.set $p
    local.get $len
    local.set $n
    (block $done8
      (loop $l8
        local.get $n
        i32.const 8
        i32.lt_s
        br_if $done8
        local.get $h
        i64.const 5
        i64.rotl
        local.get $p
        i64.load
        i64.xor
        i64.const 0x517cc1b727220a95
        i64.mul
        local.set $h
        local.get $p
        i32.const 8
        i32.add
        local.set $p
        local.get $n
        i32.const 8
        i32.sub
        local.set $n
        br $l8))
    (block $done1
      (loop $l1
        local.get $n
        i32.const 0
        i32.le_s
        br_if $done1
        local.get $h
        i64.const 5
        i64.rotl
        local.get $p
        i32.load8_u
        i64.extend_i32_u
        i64.xor
        i64.const 0x517cc1b727220a95
        i64.mul
        local.set $h
        local.get $p
        i32.const 1
        i32.add
        local.set $p
        local.get $n
        i32.const 1
        i32.sub
        local.set $n
        br $l1))
    local.get $h)

  ;; Byte-exact line equality (1 if equal, 0 otherwise).
  (func $line_equals (param $p1 i32) (param $l1 i32) (param $p2 i32) (param $l2 i32) (result i32)
    (local $n i32)
    (local $a i32)
    (local $b i32)
    local.get $l1
    local.get $l2
    i32.ne
    if
      i32.const 0
      return
    end
    local.get $l1
    local.set $n
    local.get $p1
    local.set $a
    local.get $p2
    local.set $b
    (block $done8
      (loop $l8
        local.get $n
        i32.const 8
        i32.lt_s
        br_if $done8
        local.get $a
        i64.load
        local.get $b
        i64.load
        i64.ne
        if
          i32.const 0
          return
        end
        local.get $a
        i32.const 8
        i32.add
        local.set $a
        local.get $b
        i32.const 8
        i32.add
        local.set $b
        local.get $n
        i32.const 8
        i32.sub
        local.set $n
        br $l8))
    (block $done1
      (loop $l1
        local.get $n
        i32.const 0
        i32.le_s
        br_if $done1
        local.get $a
        i32.load8_u
        local.get $b
        i32.load8_u
        i32.ne
        if
          i32.const 0
          return
        end
        local.get $a
        i32.const 1
        i32.add
        local.set $a
        local.get $b
        i32.const 1
        i32.add
        local.set $b
        local.get $n
        i32.const 1
        i32.sub
        local.set $n
        br $l1))
    i32.const 1)

  ;; Intern one line: src 0 = old text, 1 = new text; the line is the byte
  ;; range [textBase(src)+off, +len). Returns its shared integer id.
  ;; Table entry (24 bytes): +0 hash i64, +8 id i32, +12 src i32,
  ;; +16 off i32, +20 len i32. A zero hash marks an empty slot.
  (func $intern (param $src i32) (param $off i32) (param $len i32) (result i32)
    (local $h i64)
    (local $idx i32)
    (local $base i32)
    (local $e i32)
    (local $eh i64)
    (local $text i32)
    local.get $src
    if (result i32)
      global.get $IN_NEW
    else
      global.get $IN_OLD
    end
    local.set $text
    local.get $text
    local.get $off
    i32.add
    local.get $len
    call $hash_bytes
    local.set $h
    local.get $h
    i32.wrap_i64
    global.get $TABLE_MASK
    i32.and
    local.set $idx
    (loop $probe
      global.get $TABLE
      local.get $idx
      i32.const 24
      i32.mul
      i32.add
      local.set $e
      local.get $e
      i64.load
      local.set $eh
      ;; Empty slot: claim it.
      local.get $eh
      i64.const 0
      i64.eq
      if
        local.get $e
        local.get $h
        i64.store
        local.get $e
        i32.const 8
        i32.add
        global.get $next_id
        i32.store
        local.get $e
        i32.const 12
        i32.add
        local.get $src
        i32.store
        local.get $e
        i32.const 16
        i32.add
        local.get $off
        i32.store
        local.get $e
        i32.const 20
        i32.add
        local.get $len
        i32.store
        global.get $next_id
        global.get $next_id
        i32.const 1
        i32.add
        global.set $next_id
        return
      end
      ;; Same hash: confirm with a full byte compare.
      local.get $eh
      local.get $h
      i64.eq
      if
        local.get $e
        i32.const 12
        i32.add
        i32.load
        if (result i32)
          global.get $IN_NEW
        else
          global.get $IN_OLD
        end
        local.get $e
        i32.const 16
        i32.add
        i32.load
        i32.add
        local.get $e
        i32.const 20
        i32.add
        i32.load
        local.get $text
        local.get $off
        i32.add
        local.get $len
        call $line_equals
        if
          local.get $e
          i32.const 8
          i32.add
          i32.load
          return
        end
      end
      ;; Collision: linear probe.
      local.get $idx
      i32.const 1
      i32.add
      global.get $TABLE_MASK
      i32.and
      local.set $idx
      br $probe)
    unreachable)

  ;; Split one text into lines (a line ends at \n, kept; a final line with
  ;; no trailing \n is kept as-is), intern each line, write its start offset
  ;; into spans[] and its id into ids[]. Returns the line count; spans[count]
  ;; is the text length (sentinel).
  ;; ---- Find the next newline (SIMD128 scan) ---------------------------
  ;; Returns the absolute pointer of the next 0x0A byte at or after $p, or
  ;; $end if there is none. Technique taken from seams' AVX2 newline scan
  ;; (32 bytes at a time, vpmovmskb + tzcnt), adapted to WASM SIMD128
  ;; (16 bytes at a time, i8x16.bitmask + i32.ctz): one loop round per
  ;; newline instead of one per byte. The tail (<16 bytes left) is scalar.
  ;; Never reads past $end.
  (func $find_nl (param $p i32) (param $end i32) (result i32)
    (local $mask i32)
    (loop $chunk
      local.get $p
      i32.const 16
      i32.add
      local.get $end
      i32.le_s
      if
        local.get $p
        v128.load
        i32.const 10
        i8x16.splat
        i8x16.eq
        i8x16.bitmask
        local.set $mask
        local.get $mask
        i32.eqz
        if
          local.get $p
          i32.const 16
          i32.add
          local.set $p
          br $chunk
        end
        ;; Lowest set bit is the next newline.
        local.get $p
        local.get $mask
        i32.ctz
        i32.add
        return
      end
      (loop $tail
        local.get $p
        local.get $end
        i32.ge_s
        if
          local.get $end
          return
        end
        local.get $p
        i32.load8_u
        i32.const 10
        i32.eq
        if
          local.get $p
          return
        end
        local.get $p
        i32.const 1
        i32.add
        local.set $p
        br $tail))
    unreachable)

  ;; ---- Tokenize + intern ------------------------------------------------
  ;; Splits one text into lines (a line ends at each \n; a trailing
  ;; unterminated run is one final line), interns every distinct line to a
  ;; small integer id, and writes the span starts (plus a sentinel = $len)
  ;; and the per-line ids. Returns the line count. Semantics identical to
  ;; the scalar version: no empty trailing line when the text ends in \n,
  ;; empty text gives 0 lines.
  ;; ---- Scan + hash-intern (v4b) -----------------------------------------
  ;; Scan one text into lines: a single inlined SIMD pass that writes the
  ;; span starts (plus a sentinel = $len) and returns the line count. No
  ;; per-line function call: each 16-byte chunk yields a \n bitmask
  ;; (i8x16.bitmask) and every set bit records one line boundary. The
  ;; tail (<16 bytes) is scalar. Semantics identical to the v3 $tokenize
  ;; (no empty trailing line when the text ends in \n, empty text gives
  ;; 0 lines).

  ;; ---- v5: fused tokenize -------------------------------------------
  ;; Intern one line (bytes [text+off, +len)) and return its id. Also
  ;; writes ids[idx] = id and updates COUNTS. $src 0=old, 1=new.
  ;; FxHash + table probe + byte compare are all inlined here (no
  ;; $intern/$hash_bytes/$line_equals calls), so the per-line cost is
  ;; one call instead of three, and the spans round-trip + the separate
  ;; $count_ids pass are gone. The COUNTS entry for a fresh id is
  ;; initialised (0,0,-1) at claim time.
  (func $intern_line (param $src i32) (param $text i32) (param $off i32) (param $len i32)
        (param $idx i32) (param $ids i32) (result i32)
    (local $h i64) (local $p i32) (local $n i32)
    (local $tidx i32) (local $e i32) (local $eh i64) (local $id i32)
    (local $cp i32) (local $cq i32) (local $cn i32) (local $eq i32)
    i64.const 0x517cc1b727220a95
    local.set $h
    local.get $text
    local.get $off
    i32.add
    local.set $p
    local.get $len
    local.set $n
    (block $done8
      (loop $l8
        local.get $n
        i32.const 8
        i32.lt_s
        br_if $done8
        local.get $h
        i64.const 5
        i64.rotl
        local.get $p
        i64.load
        i64.xor
        i64.const 0x517cc1b727220a95
        i64.mul
        local.set $h
        local.get $p
        i32.const 8
        i32.add
        local.set $p
        local.get $n
        i32.const 8
        i32.sub
        local.set $n
        br $l8))
    (block $done1
      (loop $l1
        local.get $n
        i32.const 0
        i32.le_s
        br_if $done1
        local.get $h
        i64.const 5
        i64.rotl
        local.get $p
        i32.load8_u
        i64.extend_i32_u
        i64.xor
        i64.const 0x517cc1b727220a95
        i64.mul
        local.set $h
        local.get $p
        i32.const 1
        i32.add
        local.set $p
        local.get $n
        i32.const 1
        i32.sub
        local.set $n
        br $l1))
    local.get $h
    i32.wrap_i64
    global.get $TABLE_MASK
    i32.and
    local.set $tidx
    (block $found
      (loop $probe
        global.get $TABLE
        local.get $tidx
        i32.const 24
        i32.mul
        i32.add
        local.set $e
        local.get $e
        i64.load
        local.set $eh
        local.get $eh
        i64.const 0
        i64.eq
        if
          local.get $e
          local.get $h
          i64.store
          local.get $e
          i32.const 8
          i32.add
          global.get $next_id
          i32.store
          local.get $e
          i32.const 12
          i32.add
          local.get $src
          i32.store
          local.get $e
          i32.const 16
          i32.add
          local.get $off
          i32.store
          local.get $e
          i32.const 20
          i32.add
          local.get $len
          i32.store
          global.get $COUNTS
          global.get $next_id
          i32.const 12
          i32.mul
          i32.add
          i32.const 0
          i32.store
          global.get $COUNTS
          global.get $next_id
          i32.const 12
          i32.mul
          i32.add
          i32.const 4
          i32.add
          i32.const 0
          i32.store
          global.get $COUNTS
          global.get $next_id
          i32.const 12
          i32.mul
          i32.add
          i32.const 8
          i32.add
          i32.const -1
          i32.store
          global.get $next_id
          local.set $id
          global.get $next_id
          i32.const 1
          i32.add
          global.set $next_id
          br $found
        end
        local.get $eh
        local.get $h
        i64.eq
        if
          local.get $e
          i32.const 12
          i32.add
          i32.load
          if (result i32)
            global.get $IN_NEW
          else
            global.get $IN_OLD
          end
          local.get $e
          i32.const 16
          i32.add
          i32.load
          i32.add
          local.set $cp
          local.get $e
          i32.const 20
          i32.add
          i32.load
          local.set $cn
          local.get $cn
          local.get $len
          i32.eq
          if
            local.get $text
            local.get $off
            i32.add
            local.set $cq
            local.get $len
            local.set $n
            i32.const 1
            local.set $eq
            (block $cmp8_done
              (loop $cmp8
                local.get $n
                i32.const 8
                i32.lt_s
                br_if $cmp8_done
                local.get $cp
                i64.load
                local.get $cq
                i64.load
                i64.ne
                if
                  i32.const 0
                  local.set $eq
                  br $cmp8_done
                end
                local.get $cp
                i32.const 8
                i32.add
                local.set $cp
                local.get $cq
                i32.const 8
                i32.add
                local.set $cq
                local.get $n
                i32.const 8
                i32.sub
                local.set $n
                br $cmp8))
            local.get $eq
            if
              (block $cmp1_done
                (loop $cmp1
                  local.get $n
                  i32.const 0
                  i32.le_s
                  br_if $cmp1_done
                  local.get $cp
                  i32.load8_u
                  local.get $cq
                  i32.load8_u
                  i32.ne
                  if
                    i32.const 0
                    local.set $eq
                    br $cmp1_done
                  end
                  local.get $cp
                  i32.const 1
                  i32.add
                  local.set $cp
                  local.get $cq
                  i32.const 1
                  i32.add
                  local.set $cq
                  local.get $n
                  i32.const 1
                  i32.sub
                  local.set $n
                  br $cmp1))
            end
            local.get $eq
            if
              local.get $e
              i32.const 8
              i32.add
              i32.load
              local.set $id
              br $found
            end
          end
        end
        local.get $tidx
        i32.const 1
        i32.add
        global.get $TABLE_MASK
        i32.and
        local.set $tidx
        br $probe))
    local.get $ids
    local.get $idx
    i32.const 2
    i32.shl
    i32.add
    local.get $id
    i32.store
    local.get $src
    i32.const 0
    i32.eq
    if
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.load
      i32.const 1
      i32.add
      i32.store
    else
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.const 4
      i32.add
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.const 4
      i32.add
      i32.load
      i32.const 1
      i32.add
      i32.store
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.const 8
      i32.add
      i32.load
      i32.const 0
      i32.lt_s
      if
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 8
        i32.add
        local.get $idx
        i32.store
      end
    end
    local.get $id)

  ;; Tokenize one text into lines and intern each line in a single pass
  ;; (SIMD newline scan + $intern_line per line). $src: 0 = old, 1 = new.
  ;; Writes line-start offsets into spans[] (spans[count] = text length
  ;; sentinel) and line ids into ids[]. Returns the line count.
  (func $tokenize_text (param $src i32) (param $text i32) (param $len i32)
        (param $spans i32) (param $ids i32) (result i32)
    (local $count i32) (local $p i32) (local $end i32) (local $chunkEnd i32)
    (local $v v128) (local $mask i32) (local $b i32)
    (local $lineStart i32) (local $e i32)
    local.get $spans
    i32.const 0
    i32.store
    i32.const 0
    local.set $count
    i32.const 0
    local.set $lineStart
    local.get $text
    local.set $p
    local.get $text
    local.get $len
    i32.add
    local.set $end
    local.get $text
    local.get $len
    i32.const -16
    i32.and
    i32.add
    local.set $chunkEnd
    (block $chunks_done
      (loop $chunks
        local.get $p
        local.get $chunkEnd
        i32.ge_s
        br_if $chunks_done
        local.get $p
        v128.load
        local.set $v
        local.get $v
        i32.const 10
        i8x16.splat
        i8x16.eq
        i8x16.bitmask
        local.set $mask
        (block $bits_done
          (loop $bits
            local.get $mask
            i32.eqz
            br_if $bits_done
            local.get $mask
            i32.ctz
            local.set $b
            local.get $p
            local.get $b
            i32.add
            i32.const 1
            i32.add
            local.get $text
            i32.sub
            local.set $e
            local.get $src
            local.get $text
            local.get $lineStart
            local.get $e
            local.get $lineStart
            i32.sub
            local.get $count
            local.get $ids
            call $intern_line
            drop
            local.get $spans
            local.get $count
            i32.const 1
            i32.add
            i32.const 2
            i32.shl
            i32.add
            local.get $e
            i32.store
            local.get $e
            local.set $lineStart
            local.get $count
            i32.const 1
            i32.add
            local.set $count
            local.get $mask
            i32.const 1
            i32.sub
            local.get $mask
            i32.and
            local.set $mask
            br $bits))
        local.get $p
        i32.const 16
        i32.add
        local.set $p
        br $chunks))
    (block $tail_done
      (loop $tail
        local.get $p
        local.get $end
        i32.ge_s
        br_if $tail_done
        local.get $p
        i32.load8_u
        i32.const 10
        i32.eq
        if
          local.get $p
          i32.const 1
          i32.add
          local.get $text
          i32.sub
          local.set $e
          local.get $src
          local.get $text
          local.get $lineStart
          local.get $e
          local.get $lineStart
          i32.sub
          local.get $count
          local.get $ids
          call $intern_line
          drop
          local.get $spans
          local.get $count
          i32.const 1
          i32.add
          i32.const 2
          i32.shl
          i32.add
          local.get $e
          i32.store
          local.get $e
          local.set $lineStart
          local.get $count
          i32.const 1
          i32.add
          local.set $count
        end
        local.get $p
        i32.const 1
        i32.add
        local.set $p
        br $tail))
    local.get $lineStart
    local.get $len
    i32.lt_s
    if
      local.get $len
      local.set $e
      local.get $src
      local.get $text
      local.get $lineStart
      local.get $e
      local.get $lineStart
      i32.sub
      local.get $count
      local.get $ids
      call $intern_line
      drop
      local.get $spans
      local.get $count
      i32.const 1
      i32.add
      i32.const 2
      i32.shl
      i32.add
      local.get $e
      i32.store
      local.get $count
      i32.const 1
      i32.add
      local.set $count
    end
    local.get $spans
    local.get $count
    i32.const 2
    i32.shl
    i32.add
    local.get $len
    i32.store
    local.get $count)

  (func $scan_lines (param $ptr i32) (param $len i32) (param $spans i32) (result i32)
    (local $count i32)
    (local $p i32)
    (local $end i32)
    (local $chunkEnd i32)
    (local $v v128)
    (local $mask i32)
    (local $b i32)
    local.get $spans
    i32.const 0
    i32.store
    i32.const 0
    local.set $count
    local.get $ptr
    local.set $p
    local.get $ptr
    local.get $len
    i32.add
    local.set $end
    local.get $ptr
    local.get $len
    i32.const -16
    i32.and
    i32.add
    local.set $chunkEnd
    (block $chunks_done
      (loop $chunks
        local.get $p
        local.get $chunkEnd
        i32.ge_s
        br_if $chunks_done
        local.get $p
        v128.load
        local.set $v
        local.get $v
        i32.const 10
        i8x16.splat
        i8x16.eq
        i8x16.bitmask
        local.set $mask
        (block $bits_done
          (loop $bits
            local.get $mask
            i32.eqz
            br_if $bits_done
            local.get $mask
            i32.ctz
            local.set $b
            local.get $count
            i32.const 1
            i32.add
            local.set $count
            local.get $spans
            local.get $count
            i32.const 2
            i32.shl
            i32.add
            local.get $p
            local.get $b
            i32.add
            i32.const 1
            i32.add
            local.get $ptr
            i32.sub
            i32.store
            local.get $mask
            i32.const 1
            i32.sub
            local.get $mask
            i32.and
            local.set $mask
            br $bits))
        local.get $p
        i32.const 16
        i32.add
        local.set $p
        br $chunks))
    (block $tail_done
      (loop $tail
        local.get $p
        local.get $end
        i32.ge_s
        br_if $tail_done
        local.get $p
        i32.load8_u
        i32.const 10
        i32.eq
        if
          local.get $count
          i32.const 1
          i32.add
          local.set $count
          local.get $spans
          local.get $count
          i32.const 2
          i32.shl
          i32.add
          local.get $p
          i32.const 1
          i32.add
          local.get $ptr
          i32.sub
          i32.store
        end
        local.get $p
        i32.const 1
        i32.add
        local.set $p
        br $tail))
    local.get $spans
    local.get $count
    i32.const 2
    i32.shl
    i32.add
    i32.load
    local.get $len
    i32.lt_s
    if
      local.get $count
      i32.const 1
      i32.add
      local.set $count
    end
    local.get $spans
    local.get $count
    i32.const 2
    i32.shl
    i32.add
    local.get $len
    i32.store
    local.get $count)

  ;; Record one line's contribution to its id's COUNTS (countOld@0,
  ;; countNew@4, firstPosNew@8). On a fresh id, initialise; otherwise
  ;; increment the side's count (and set firstPosNew on its first new
  ;; occurrence).
  (func $count_line (param $id i32) (param $idx i32) (param $src i32) (param $isNew i32)
    local.get $isNew
    if
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      local.get $src
      i32.eqz
      if (result i32)
        i32.const 1
      else
        i32.const 0
      end
      i32.store
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.const 4
      i32.add
      local.get $src
      if (result i32)
        i32.const 1
      else
        i32.const 0
      end
      i32.store
      global.get $COUNTS
      local.get $id
      i32.const 12
      i32.mul
      i32.add
      i32.const 8
      i32.add
      local.get $src
      if (result i32)
        local.get $idx
      else
        i32.const -1
      end
      i32.store
    else
      local.get $src
      if
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        i32.load
        i32.const 1
        i32.add
        i32.store
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 8
        i32.add
        i32.load
        i32.const 0
        i32.lt_s
        if
          global.get $COUNTS
          local.get $id
          i32.const 12
          i32.mul
          i32.add
          i32.const 8
          i32.add
          local.get $idx
          i32.store
        end
      else
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.load
        i32.const 1
        i32.add
        i32.store
      end
    end)

  ;; Build per-id COUNTS (countOld, countNew, firstPosNew) in a separate
  ;; pass over the id arrays, after interning. Kept out of the hot
  ;; $hash_intern loop so that loop stays tight (no extra call per line).
  (func $count_ids (param $n i32) (param $m i32)
    (local $i i32) (local $id i32)
    ;; initialise ids 0..next_id-1: (0, 0, -1)
    i32.const 0
    local.set $i
    (block $init_done
      (loop $init
        local.get $i
        global.get $next_id
        i32.ge_s
        br_if $init_done
        global.get $COUNTS
        local.get $i
        i32.const 12
        i32.mul
        i32.add
        i32.const 0
        i32.store
        global.get $COUNTS
        local.get $i
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        i32.const 0
        i32.store
        global.get $COUNTS
        local.get $i
        i32.const 12
        i32.mul
        i32.add
        i32.const 8
        i32.add
        i32.const -1
        i32.store
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $init))
    ;; old lines: countOld++
    i32.const 0
    local.set $i
    (block $o_done
      (loop $o
        local.get $i
        local.get $n
        i32.ge_s
        br_if $o_done
        global.get $IDS_OLD
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $id
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.load
        i32.const 1
        i32.add
        i32.store
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $o))
    ;; new lines: countNew++, firstPosNew if unset
    i32.const 0
    local.set $i
    (block $nn_done
      (loop $nn
        local.get $i
        local.get $m
        i32.ge_s
        br_if $nn_done
        global.get $IDS_NEW
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $id
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        i32.load
        i32.const 1
        i32.add
        i32.store
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 8
        i32.add
        i32.load
        i32.const 0
        i32.lt_s
        if
          global.get $COUNTS
          local.get $id
          i32.const 12
          i32.mul
          i32.add
          i32.const 8
          i32.add
          local.get $i
          i32.store
        end
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $nn)))

  ;; Hash+intern every line of both texts: one sequential pass over the
  ;; spans, calling the proven $intern (hash-table probe + full byte
  ;; compare) per line and writing IDS_OLD/IDS_NEW. Also records per-id
  ;; COUNTS via $count_line, using the $next_id step to detect a freshly
  ;; created id.
  (func $hash_intern (param $n i32) (param $m i32)
    (local $i i32) (local $off i32) (local $len i32) (local $id i32)
    i32.const 0
    local.set $i
    (block $o_done
      (loop $o
        local.get $i
        local.get $n
        i32.ge_s
        br_if $o_done
        global.get $SPANS_OLD
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $off
        global.get $SPANS_OLD
        local.get $i
        i32.const 1
        i32.add
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.get $off
        i32.sub
        local.set $len
        i32.const 0
        local.get $off
        local.get $len
        call $intern
        local.set $id
        global.get $IDS_OLD
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        local.get $id
        i32.store
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $o))
    i32.const 0
    local.set $i
    (block $nn_done
      (loop $nn
        local.get $i
        local.get $m
        i32.ge_s
        br_if $nn_done
        global.get $SPANS_NEW
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $off
        global.get $SPANS_NEW
        local.get $i
        i32.const 1
        i32.add
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.get $off
        i32.sub
        local.set $len
        i32.const 1
        local.get $off
        local.get $len
        call $intern
        local.set $id
        global.get $IDS_NEW
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        local.get $id
        i32.store
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $nn)))

  ;; ---- Anchor-guided band (v4b) ---------------------------------------
  ;; Exact edit distance of the gap IDS_OLD[px..ai) vs IDS_NEW[py..aj).
  ;; Fast paths: empty gap, identical slices, one side empty; otherwise a
  ;; small full Myers search on the gap slice (reusing $search, which
  ;; only needs the D value here). Returns -1 for a gap > 500 lines
  ;; (caller aborts the anchor attempt; the gap is too large for the
  ;; anchor decomposition to be useful).
  (func $gap_d (param $px i32) (param $ai i32) (param $py i32) (param $aj i32) (result i32)
    (local $gn i32) (local $gm i32) (local $i i32) (local $eq i32)
    local.get $ai
    local.get $px
    i32.sub
    local.set $gn
    local.get $aj
    local.get $py
    i32.sub
    local.set $gm
    local.get $gn
    local.get $gm
    i32.add
    i32.const 500
    i32.gt_s
    if
      i32.const -1
      return
    end
    local.get $gn
    i32.const 0
    i32.eq
    local.get $gm
    i32.const 0
    i32.eq
    i32.and
    if
      i32.const 0
      return
    end
    local.get $gn
    i32.const 0
    i32.eq
    if
      local.get $gm
      return
    end
    local.get $gm
    i32.const 0
    i32.eq
    if
      local.get $gn
      return
    end
    local.get $gn
    local.get $gm
    i32.eq
    if
      i32.const 1
      local.set $eq
      i32.const 0
      local.set $i
      (block $cmp_done
        (loop $cmp
          local.get $i
          local.get $gn
          i32.ge_s
          br_if $cmp_done
          global.get $IDS_OLD
          local.get $px
          local.get $i
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $IDS_NEW
          local.get $py
          local.get $i
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.ne
          if
            i32.const 0
            local.set $eq
            br $cmp_done
          end
          local.get $i
          i32.const 1
          i32.add
          local.set $i
          br $cmp))
      local.get $eq
      if
        i32.const 0
        return
      end
    end
    global.get $IDS_OLD
    local.get $px
    i32.const 2
    i32.shl
    i32.add
    global.get $IDS_NEW
    local.get $py
    i32.const 2
    i32.shl
    i32.add
    i32.const 0
    local.get $gn
    local.get $gm
    local.get $gn
    local.get $gm
    i32.add
    global.get $V
    i32.const -1
    call $search)


  ;; ---- v5: per-gap DP (patience path), OPTIMISED ----------------------
  ;; Same contract as the original $dp_gap (exact D + fills $KPAT), but
  ;; the table uses a FIXED stride of 256 columns (row = 1024 bytes, so
  ;; row offsets are shifts, not multiplies) and the inner loop uses
  ;; running pointers + carried values instead of re-addressing three
  ;; cells per step:
  ;;   p -> dp[i][j] (store target), q -> dp[i-1][j] (vDel source)
  ;;   prevBest = dp[i][j-1] (vIns source), prevUp = dp[i-1][j-1] (vSub)
  ;; Per cell: 1 bId load + 1 q load + 1 store + ~10 ALU ops.
  (func $dp_gap (param $px i32) (param $ai i32) (param $py i32) (param $aj i32) (param $dCum i32) (result i32)
    (local $gn i32) (local $gm i32) (local $D i32)
    (local $i i32) (local $j i32) (local $t i32)
    (local $aId i32) (local $bId i32) (local $cost i32)
    (local $up i32) (local $vDel i32) (local $vIns i32) (local $vSub i32) (local $best i32)
    (local $prevBest i32) (local $prevUp i32)
    (local $p i32) (local $q i32) (local $e i32)
    local.get $ai
    local.get $px
    i32.sub
    local.set $gn
    local.get $aj
    local.get $py
    i32.sub
    local.set $gm
    local.get $gn
    global.get $DP_CAP
    i32.gt_s
    local.get $gm
    global.get $DP_CAP
    i32.gt_s
    i32.or
    if
      i32.const -1
      return
    end
    local.get $gn
    i32.const 0
    i32.eq
    local.get $gm
    i32.const 0
    i32.eq
    i32.and
    if
      global.get $KPAT
      local.get $dCum
      i32.const 2
      i32.shl
      i32.add
      local.get $px
      local.get $py
      i32.sub
      i32.store
      i32.const 0
      return
    end
    local.get $gn
    i32.const 0
    i32.eq
    if
      i32.const 0
      local.set $t
      (block $ins_done
        (loop $ins
          local.get $t
          local.get $gm
          i32.gt_s
          br_if $ins_done
          global.get $KPAT
          local.get $dCum
          local.get $t
          i32.add
          i32.const 2
          i32.shl
          i32.add
          local.get $px
          local.get $py
          local.get $t
          i32.add
          i32.sub
          i32.store
          local.get $t
          i32.const 1
          i32.add
          local.set $t
          br $ins))
      local.get $gm
      return
    end
    local.get $gm
    i32.const 0
    i32.eq
    if
      i32.const 0
      local.set $t
      (block $del_done
        (loop $del
          local.get $t
          local.get $gn
          i32.gt_s
          br_if $del_done
          global.get $KPAT
          local.get $dCum
          local.get $t
          i32.add
          i32.const 2
          i32.shl
          i32.add
          local.get $px
          local.get $t
          i32.add
          local.get $py
          i32.sub
          i32.store
          local.get $t
          i32.const 1
          i32.add
          local.set $t
          br $del))
      local.get $gn
      return
    end
    local.get $gn
    local.get $gm
    i32.eq
    if
      i32.const 1
      local.set $t
      i32.const 0
      local.set $i
      (block $cmp_done
        (loop $cmp
          local.get $i
          local.get $gn
          i32.ge_s
          br_if $cmp_done
          global.get $IDS_OLD
          local.get $px
          local.get $i
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $IDS_NEW
          local.get $py
          local.get $i
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.ne
          if
            i32.const 0
            local.set $t
            br $cmp_done
          end
          local.get $i
          i32.const 1
          i32.add
          local.set $i
          br $cmp))
      local.get $t
      if
        global.get $KPAT
        local.get $dCum
        i32.const 2
        i32.shl
        i32.add
        local.get $px
        local.get $py
        i32.sub
        i32.store
        i32.const 0
        return
      end
    end
    ;; General case: fixed stride 256 cols (row = 1024 bytes).
    ;; Row 0: dp[0][j] = j.
    i32.const 0
    local.set $j
    (block $r0_done
      (loop $r0
        local.get $j
        local.get $gm
        i32.gt_s
        br_if $r0_done
        global.get $DP_TBL
        local.get $j
        i32.const 2
        i32.shl
        i32.add
        local.get $j
        i32.store
        local.get $j
        i32.const 1
        i32.add
        local.set $j
        br $r0))
    ;; Rows 1..gn.
    i32.const 1
    local.set $i
    (block $rows_done
      (loop $rows
        local.get $i
        local.get $gn
        i32.gt_s
        br_if $rows_done
        ;; dp[i][0] = i  (address $DP_TBL + (i<<10))
        global.get $DP_TBL
        local.get $i
        i32.const 10
        i32.shl
        i32.add
        local.get $i
        i32.store
        global.get $IDS_OLD
        local.get $px
        local.get $i
        i32.const 1
        i32.sub
        i32.add
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $aId
        ;; p = &dp[i][1], q = &dp[i-1][1]; prevBest = dp[i][0] = i;
        ;; prevUp = dp[i-1][0] = i-1.
        global.get $DP_TBL
        local.get $i
        i32.const 10
        i32.shl
        i32.add
        i32.const 4
        i32.add
        local.set $p
        global.get $DP_TBL
        local.get $i
        i32.const 1
        i32.sub
        i32.const 10
        i32.shl
        i32.add
        i32.const 4
        i32.add
        local.set $q
        local.get $i
        local.set $prevBest
        local.get $i
        i32.const 1
        i32.sub
        local.set $prevUp
        i32.const 1
        local.set $j
        (block $cols_done
          (loop $cols
            local.get $j
            local.get $gm
            i32.gt_s
            br_if $cols_done
            global.get $IDS_NEW
            local.get $py
            local.get $j
            i32.const 1
            i32.sub
            i32.add
            i32.const 2
            i32.shl
            i32.add
            i32.load
            local.set $bId
            local.get $aId
            local.get $bId
            i32.eq
            if (result i32)
              i32.const 0
            else
              i32.const 2
            end
            local.set $cost
            local.get $q
            i32.load
            local.set $up
            local.get $up
            i32.const 1
            i32.add
            local.set $vDel
            local.get $prevBest
            i32.const 1
            i32.add
            local.set $vIns
            local.get $prevUp
            local.get $cost
            i32.add
            local.set $vSub
            local.get $vDel
            local.set $best
            local.get $vIns
            local.get $best
            i32.lt_s
            if
              local.get $vIns
              local.set $best
            end
            local.get $vSub
            local.get $best
            i32.lt_s
            if
              local.get $vSub
              local.set $best
            end
            local.get $p
            local.get $best
            i32.store
            local.get $up
            local.set $prevUp
            local.get $best
            local.set $prevBest
            local.get $p
            i32.const 4
            i32.add
            local.set $p
            local.get $q
            i32.const 4
            i32.add
            local.set $q
            local.get $j
            i32.const 1
            i32.add
            local.set $j
            br $cols))
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $rows))
    ;; D = dp[gn][gm]  (address $DP_TBL + (gn<<10) + (gm<<2))
    global.get $DP_TBL
    local.get $gn
    i32.const 10
    i32.shl
    i32.add
    local.get $gm
    i32.const 2
    i32.shl
    i32.add
    i32.load
    local.set $D
    ;; Backtrack from (gn, gm), filling $KPAT. $e = edits undone so far.
    ;; dp[i][j] is at $DP_TBL + (i<<10) + (j<<2).
    local.get $gn
    local.set $i
    local.get $gm
    local.set $j
    i32.const 0
    local.set $e
    global.get $KPAT
    local.get $dCum
    local.get $D
    i32.add
    i32.const 2
    i32.shl
    i32.add
    local.get $px
    local.get $gn
    i32.add
    local.get $py
    local.get $gm
    i32.add
    i32.sub
    i32.store
    (block $bt_done
      (loop $bt
        local.get $i
        i32.const 0
        i32.eq
        local.get $j
        i32.const 0
        i32.eq
        i32.and
        br_if $bt_done
        ;; match? i>0, j>0, a[i-1]==b[j-1], dp[i][j]==dp[i-1][j-1]
        local.get $i
        i32.const 0
        i32.gt_s
        local.get $j
        i32.const 0
        i32.gt_s
        i32.and
        if
          global.get $IDS_OLD
          local.get $px
          local.get $i
          i32.const 1
          i32.sub
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $IDS_NEW
          local.get $py
          local.get $j
          i32.const 1
          i32.sub
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.eq
          if
            global.get $DP_TBL
            local.get $i
            i32.const 10
            i32.shl
            i32.add
            local.get $j
            i32.const 2
            i32.shl
            i32.add
            i32.load
            global.get $DP_TBL
            local.get $i
            i32.const 1
            i32.sub
            i32.const 10
            i32.shl
            i32.add
            local.get $j
            i32.const 1
            i32.sub
            i32.const 2
            i32.shl
            i32.add
            i32.load
            i32.eq
            if
              local.get $i
              i32.const 1
              i32.sub
              local.set $i
              local.get $j
              i32.const 1
              i32.sub
              local.set $j
              global.get $KPAT
              local.get $dCum
              local.get $D
              local.get $e
              i32.sub
              i32.add
              i32.const 2
              i32.shl
              i32.add
              local.get $px
              local.get $i
              i32.add
              local.get $py
              local.get $j
              i32.add
              i32.sub
              i32.store
              br $bt
            end
          end
        end
        ;; delete? i>0 and dp[i][j]==dp[i-1][j]+1
        local.get $i
        i32.const 0
        i32.gt_s
        if
          global.get $DP_TBL
          local.get $i
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $DP_TBL
          local.get $i
          i32.const 1
          i32.sub
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.const 1
          i32.add
          i32.eq
          if
            local.get $i
            i32.const 1
            i32.sub
            local.set $i
            local.get $e
            i32.const 1
            i32.add
            local.set $e
            global.get $KPAT
            local.get $dCum
            local.get $D
            local.get $e
            i32.sub
            i32.add
            i32.const 2
            i32.shl
            i32.add
            local.get $px
            local.get $i
            i32.add
            local.get $py
            local.get $j
            i32.add
            i32.sub
            i32.store
            br $bt
          end
        end
        ;; insert? j>0 and dp[i][j]==dp[i][j-1]+1
        local.get $j
        i32.const 0
        i32.gt_s
        if
          global.get $DP_TBL
          local.get $i
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $DP_TBL
          local.get $i
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 1
          i32.sub
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.const 1
          i32.add
          i32.eq
          if
            local.get $j
            i32.const 1
            i32.sub
            local.set $j
            local.get $e
            i32.const 1
            i32.add
            local.set $e
            global.get $KPAT
            local.get $dCum
            local.get $D
            local.get $e
            i32.sub
            i32.add
            i32.const 2
            i32.shl
            i32.add
            local.get $px
            local.get $i
            i32.add
            local.get $py
            local.get $j
            i32.add
            i32.sub
            i32.store
            br $bt
          end
        end
        ;; substitution (del+ins): i>0, j>0, dp[i][j]==dp[i-1][j-1]+2.
        local.get $i
        i32.const 0
        i32.gt_s
        local.get $j
        i32.const 0
        i32.gt_s
        i32.and
        if
          global.get $DP_TBL
          local.get $i
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 2
          i32.shl
          i32.add
          i32.load
          global.get $DP_TBL
          local.get $i
          i32.const 1
          i32.sub
          i32.const 10
          i32.shl
          i32.add
          local.get $j
          i32.const 1
          i32.sub
          i32.const 2
          i32.shl
          i32.add
          i32.load
          i32.const 2
          i32.add
          i32.eq
          if
            local.get $i
            i32.const 1
            i32.sub
            local.set $i
            local.get $e
            i32.const 1
            i32.add
            local.set $e
            global.get $KPAT
            local.get $dCum
            local.get $D
            local.get $e
            i32.sub
            i32.add
            i32.const 2
            i32.shl
            i32.add
            local.get $px
            local.get $i
            i32.add
            local.get $py
            local.get $j
            i32.add
            i32.sub
            i32.store
            local.get $j
            i32.const 1
            i32.sub
            local.set $j
            local.get $e
            i32.const 1
            i32.add
            local.set $e
            global.get $KPAT
            local.get $dCum
            local.get $D
            local.get $e
            i32.sub
            i32.add
            i32.const 2
            i32.shl
            i32.add
            local.get $px
            local.get $i
            i32.add
            local.get $py
            local.get $j
            i32.add
            i32.sub
            i32.store
            br $bt
          end
        end
        unreachable
        br $bt))
    local.get $D)

  ;; Build LIS anchors over unique lines + the patience k(d) table.
  ;; Sets $N_ANCHORS, $D_ANCHOR (and fills $KPAT via $dp_gap). Aborts (sets $N_ANCHORS=0)
  ;; when anchors are too few (<100), candidates exceed capacity, or a
  ;; gap is too large — the caller then uses the proven v3 band.
  (func $build_anchors (param $n i32) (param $m i32)
    (local $nCands i32) (local $i i32) (local $id i32) (local $j i32)
    (local $len i32) (local $p i32) (local $lo i32) (local $hi i32) (local $mid i32)
    (local $candIdx i32) (local $prevIdx i32)
    (local $nAnchors i32) (local $a i32) (local $ai i32) (local $aj i32)
    (local $dcum i32) (local $px i32) (local $py i32)
    (local $gd i32) (local $wpCount i32) (local $lastD i32)
    i32.const 0
    local.set $nCands
    i32.const 0
    local.set $i
    (block $c_done
      (loop $c
        local.get $i
        local.get $n
        i32.ge_s
        br_if $c_done
        local.get $nCands
        i32.const 65534
        i32.ge_s
        if
          i32.const 0
          global.set $N_ANCHORS
          i32.const 0
          global.set $WP_COUNT
          i32.const 0
          global.set $D_ANCHOR
          return
        end
        global.get $IDS_OLD
        local.get $i
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $id
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.load
        i32.const 1
        i32.eq
        global.get $COUNTS
        local.get $id
        i32.const 12
        i32.mul
        i32.add
        i32.const 4
        i32.add
        i32.load
        i32.const 1
        i32.eq
        i32.and
        if
          global.get $CANDS
          local.get $nCands
          i32.const 3
          i32.shl
          i32.add
          local.get $i
          i32.store
          global.get $CANDS
          local.get $nCands
          i32.const 3
          i32.shl
          i32.add
          i32.const 4
          i32.add
          global.get $COUNTS
          local.get $id
          i32.const 12
          i32.mul
          i32.add
          i32.const 8
          i32.add
          i32.load
          i32.store
          local.get $nCands
          i32.const 1
          i32.add
          local.set $nCands
        end
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $c))
    i32.const 0
    local.set $len
    i32.const 0
    local.set $candIdx
    (block $lis_done
      (loop $lis
        local.get $candIdx
        local.get $nCands
        i32.ge_s
        br_if $lis_done
        global.get $CANDS
        local.get $candIdx
        i32.const 3
        i32.shl
        i32.add
        i32.const 4
        i32.add
        i32.load
        local.set $j
        i32.const 0
        local.set $lo
        local.get $len
        local.set $hi
        (block $bs_done
          (loop $bs
            local.get $lo
            local.get $hi
            i32.ge_s
            br_if $bs_done
            local.get $lo
            local.get $hi
            i32.add
            i32.const 1
            i32.shr_s
            local.set $mid
            global.get $TAILS
            local.get $mid
            i32.const 3
            i32.shl
            i32.add
            i32.load
            local.get $j
            i32.lt_s
            if
              local.get $mid
              i32.const 1
              i32.add
              local.set $lo
            else
              local.get $mid
              local.set $hi
            end
            br $bs))
        local.get $lo
        local.set $p
        local.get $p
        i32.const 0
        i32.gt_s
        if (result i32)
          global.get $TAILS
          local.get $p
          i32.const 1
          i32.sub
          i32.const 3
          i32.shl
          i32.add
          i32.const 4
          i32.add
          i32.load
        else
          i32.const -1
        end
        local.set $prevIdx
        global.get $PREV
        local.get $candIdx
        i32.const 2
        i32.shl
        i32.add
        local.get $prevIdx
        i32.store
        global.get $TAILS
        local.get $p
        i32.const 3
        i32.shl
        i32.add
        local.get $j
        i32.store
        global.get $TAILS
        local.get $p
        i32.const 3
        i32.shl
        i32.add
        i32.const 4
        i32.add
        local.get $candIdx
        i32.store
        local.get $p
        local.get $len
        i32.eq
        if
          local.get $len
          i32.const 1
          i32.add
          local.set $len
        end
        local.get $candIdx
        i32.const 1
        i32.add
        local.set $candIdx
        br $lis))
    local.get $len
    local.set $nAnchors
    local.get $nAnchors
    i32.const 100
    i32.lt_s
    if
      i32.const 0
      global.set $N_ANCHORS
      i32.const 0
      global.set $WP_COUNT
      i32.const 0
      global.set $D_ANCHOR
      return
    end
    global.get $TAILS
    local.get $len
    i32.const 1
    i32.sub
    i32.const 3
    i32.shl
    i32.add
    i32.const 4
    i32.add
    i32.load
    local.set $candIdx
    local.get $nAnchors
    i32.const 1
    i32.sub
    local.set $a
    (block $bt_done
      (loop $bt
        local.get $candIdx
        i32.const 0
        i32.lt_s
        br_if $bt_done
        global.get $ANCHORS
        local.get $a
        i32.const 3
        i32.shl
        i32.add
        global.get $CANDS
        local.get $candIdx
        i32.const 3
        i32.shl
        i32.add
        i32.load
        i32.store
        global.get $ANCHORS
        local.get $a
        i32.const 3
        i32.shl
        i32.add
        i32.const 4
        i32.add
        global.get $CANDS
        local.get $candIdx
        i32.const 3
        i32.shl
        i32.add
        i32.const 4
        i32.add
        i32.load
        i32.store
        global.get $PREV
        local.get $candIdx
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.set $candIdx
        local.get $a
        i32.const 1
        i32.sub
        local.set $a
        br $bt))
    i32.const 0
    local.set $dcum
    i32.const 0
    local.set $px
    i32.const 0
    local.set $py
    i32.const 0
    local.set $a
    (block $wp_done
      (loop $wp
        local.get $a
        local.get $nAnchors
        i32.gt_s
        br_if $wp_done
        local.get $a
        local.get $nAnchors
        i32.lt_s
        if
          global.get $ANCHORS
          local.get $a
          i32.const 3
          i32.shl
          i32.add
          i32.load
          local.set $ai
          global.get $ANCHORS
          local.get $a
          i32.const 3
          i32.shl
          i32.add
          i32.const 4
          i32.add
          i32.load
          local.set $aj
        else
          local.get $n
          local.set $ai
          local.get $m
          local.set $aj
        end
        local.get $px
        local.get $ai
        local.get $py
        local.get $aj
        local.get $dcum
        call $dp_gap
        local.set $gd
        local.get $gd
        i32.const 0
        i32.lt_s
        if
          i32.const 0
          global.set $N_ANCHORS
          i32.const 0
          global.set $D_ANCHOR
          return
        end
        local.get $dcum
        local.get $gd
        i32.add
        local.set $dcum
        local.get $ai
        i32.const 1
        i32.add
        local.set $px
        local.get $aj
        i32.const 1
        i32.add
        local.set $py
        local.get $a
        i32.const 1
        i32.add
        local.set $a
        br $wp))
    local.get $nAnchors
    global.set $N_ANCHORS
    local.get $dcum
    global.set $D_ANCHOR)

  ;; ---- Myers search (same algorithm as the v1 prototype) --------------
  ;; $bandM >= 0: search only the fixed diagonal band
  ;;   [min(0, kF) - bandM, max(0, kF) + bandM]
  ;; $bandM < 0:  full search (v2 funnel: k in [kF - (dMax - d), kF + (dMax - d)]).
  (func $search
    (param $a i32) (param $b i32) (param $off i32) (param $n i32) (param $m i32)
    (param $dMax i32) (param $v i32) (param $bandM i32)
    (result i32)
    (local $kF i32) (local $x i32) (local $y i32)
    (local $d i32) (local $D i32)
    (local $rowOff i32) (local $prevOff i32) (local $rem i32)
    (local $kLoF i32) (local $kHiF i32)
    (local $kLo i32) (local $kHi i32) (local $jLo i32) (local $jHi i32)
    (local $k i32) (local $xd i32) (local $xi i32) (local $j i32)
    (local $canDel i32) (local $canIns i32)
    (local $xDel i32) (local $xIns i32) (local $xx i32) (local $yy i32)
    (local $wpi i32) (local $kCenter i32) (local $d0 i32) (local $k0 i32) (local $d1 i32) (local $k1 i32)

    local.get $n
    local.get $m
    i32.sub
    local.set $kF

    ;; Fixed band edges (independent of d): kLoF = min(0, kF) - bandM,
    ;; kHiF = max(0, kF) + bandM. Only used when $bandM >= 0.
    i32.const 0
    local.get $kF
    i32.const 0
    local.get $kF
    i32.lt_s
    select ;; min(0, kF)
    local.get $bandM
    i32.sub
    local.set $kLoF
    i32.const 0
    local.get $kF
    i32.const 0
    local.get $kF
    i32.gt_s
    select ;; max(0, kF)
    local.get $bandM
    i32.add
    local.set $kHiF

    ;; Depth-0 snake from (0, 0) on diagonal 0.
    i32.const 0
    local.set $x
    i32.const 0
    local.set $y
    (block $snake0_done
      (loop $snake0
        local.get $x
        local.get $n
        i32.ge_s
        br_if $snake0_done
        local.get $y
        local.get $m
        i32.ge_s
        br_if $snake0_done
        local.get $a
        local.get $off
        local.get $x
        i32.add
        i32.const 2
        i32.shl
        i32.add
        i32.load
        local.get $b
        local.get $off
        local.get $y
        i32.add
        i32.const 2
        i32.shl
        i32.add
        i32.load
        i32.ne
        br_if $snake0_done
        local.get $x
        i32.const 1
        i32.add
        local.set $x
        local.get $y
        i32.const 1
        i32.add
        local.set $y
        br $snake0))
    local.get $v
    local.get $x
    i32.store
    local.get $x
    local.get $n
    i32.ge_s
    local.get $y
    local.get $m
    i32.ge_s
    i32.and
    if
      i32.const 0
      return
    end

    i32.const -1
    local.set $D
    i32.const 1
    local.set $d
    i32.const 0
    local.set $wpi
    (block $outer_done
      (loop $outer
        local.get $d
        local.get $dMax
        i32.gt_s
        br_if $outer_done
        local.get $d
        call $tri
        i32.const 2
        i32.shl
        local.set $rowOff
        local.get $d
        i32.const 1
        i32.sub
        call $tri
        i32.const 2
        i32.shl
        local.set $prevOff
        local.get $bandM
        i32.const -3
        i32.eq
        if
          ;; Patience band (v5): kCenter = $KPAT[d] (the patience-path k
          ;; at depth d), kLo/kHi = kCenter -/+ $KP_MARGIN, clamped to
          ;; [-d, d]. The DP deviation from the canonical path is at
          ;; most 12 (measured over 44 cases), so margin 24 is 2x
          ;; headroom; the D == $D_ANCHOR gate still rejects a miss.
          global.get $KPAT
          local.get $d
          i32.const 2
          i32.shl
          i32.add
          i32.load
          local.set $kCenter
          local.get $kCenter
          global.get $KP_MARGIN
          i32.sub
          i32.const 0
          local.get $d
          i32.sub
          local.get $kCenter
          global.get $KP_MARGIN
          i32.sub
          i32.const 0
          local.get $d
          i32.sub
          i32.gt_s
          select
          local.set $kLo
          local.get $kCenter
          global.get $KP_MARGIN
          i32.add
          local.get $d
          local.get $kCenter
          global.get $KP_MARGIN
          i32.add
          local.get $d
          i32.lt_s
          select
          local.set $kHi
        else
        local.get $bandM
        i32.const -2
        i32.eq
        if
          ;; Anchor band (v4b): waypoints (d, k) in $WP_PTR, $WP_COUNT
          ;; entries; kCenter(d) is the piecewise-linear interpolation
          ;; (same formula as deviation.mjs), kLo/kHi = kCenter -/+
          ;; $WP_MARGIN, clamped to [-d, d]. $wpi only moves forward.
          (block $wadv_done
            (loop $wadv
              local.get $wpi
              i32.const 1
              i32.add
              global.get $WP_COUNT
              i32.ge_s
              br_if $wadv_done
              global.get $WP_PTR
              local.get $wpi
              i32.const 1
              i32.add
              i32.const 3
              i32.shl
              i32.add
              i32.load
              local.get $d
              i32.gt_s
              br_if $wadv_done
              local.get $wpi
              i32.const 1
              i32.add
              local.set $wpi
              br $wadv))
          global.get $WP_PTR
          local.get $wpi
          i32.const 3
          i32.shl
          i32.add
          i32.load
          local.set $d0
          global.get $WP_PTR
          local.get $wpi
          i32.const 3
          i32.shl
          i32.add
          i32.const 4
          i32.add
          i32.load
          local.set $k0
          local.get $wpi
          i32.const 1
          i32.add
          global.get $WP_COUNT
          i32.ge_s
          if
            local.get $k0
            local.set $kCenter
          else
            global.get $WP_PTR
            local.get $wpi
            i32.const 1
            i32.add
            i32.const 3
            i32.shl
            i32.add
            i32.load
            local.set $d1
            global.get $WP_PTR
            local.get $wpi
            i32.const 1
            i32.add
            i32.const 3
            i32.shl
            i32.add
            i32.const 4
            i32.add
            i32.load
            local.set $k1
            local.get $d1
            local.get $d0
            i32.eq
            if
              local.get $k0
              local.set $kCenter
            else
              local.get $k0
              local.get $k1
              local.get $k0
              i32.sub
              local.get $d
              local.get $d0
              i32.sub
              i32.mul
              local.get $d1
              local.get $d0
              i32.sub
              i32.div_s
              i32.add
              local.set $kCenter
            end
          end
          local.get $kCenter
          global.get $WP_MARGIN
          i32.sub
          i32.const 0
          local.get $d
          i32.sub
          local.get $kCenter
          global.get $WP_MARGIN
          i32.sub
          i32.const 0
          local.get $d
          i32.sub
          i32.gt_s
          select
          local.set $kLo
          local.get $kCenter
          global.get $WP_MARGIN
          i32.add
          local.get $d
          local.get $kCenter
          global.get $WP_MARGIN
          i32.add
          local.get $d
          i32.lt_s
          select
          local.set $kHi
        else
        local.get $bandM
        i32.const 0
        i32.ge_s
        if
          ;; Fixed diagonal band: kLo = max(kLoF, -d), kHi = min(kHiF, d).
          local.get $kLoF
          i32.const 0
          local.get $d
          i32.sub
          local.get $kLoF
          i32.const 0
          local.get $d
          i32.sub
          i32.gt_s
          select
          local.set $kLo
          local.get $kHiF
          local.get $d
          local.get $kHiF
          local.get $d
          i32.lt_s
          select
          local.set $kHi
        else
          ;; v2 funnel: kLo = max(kF - rem, -d), kHi = min(kF + rem, d).
          local.get $dMax
          local.get $d
          i32.sub
          local.set $rem
          i32.const 0
          local.get $d
          i32.sub
          local.get $kF
          local.get $rem
          i32.sub
          i32.const 0
          local.get $d
          i32.sub
          local.get $kF
          local.get $rem
          i32.sub
          i32.gt_s
          select
          local.set $kLo
          local.get $kF
          local.get $rem
          i32.add
          local.get $d
          local.get $kF
          local.get $rem
          i32.add
          local.get $d
          i32.lt_s
          select
          local.set $kHi
        end
        end
        end
        local.get $kLo
        local.get $d
        i32.add
        i32.const 1
        i32.add
        i32.const 1
        i32.shr_s
        local.set $jLo
        local.get $kHi
        local.get $d
        i32.add
        i32.const 1
        i32.shr_s
        local.set $jHi

        local.get $jLo
        local.get $jHi
        i32.le_s
        if
          i32.const 0
          local.get $d
          i32.sub
          local.get $jLo
          i32.const 1
          i32.shl
          i32.add
          local.set $k
          local.get $jLo
          i32.const 0
          i32.gt_s
          if (result i32)
            local.get $v
            local.get $prevOff
            local.get $jLo
            i32.const 1
            i32.sub
            i32.const 2
            i32.shl
            i32.add
            i32.add
            i32.load
          else
            i32.const -1
          end
          local.set $xd
          local.get $jLo
          local.get $d
          i32.lt_s
          if (result i32)
            local.get $v
            local.get $prevOff
            local.get $jLo
            i32.const 2
            i32.shl
            i32.add
            i32.add
            i32.load
          else
            i32.const -1
          end
          local.set $xi

          local.get $jLo
          local.set $j
          (block $inner_done
            (loop $inner
              local.get $j
              local.get $jHi
              i32.gt_s
              br_if $inner_done
              local.get $xd
              i32.const 0
              i32.ge_s
              local.get $xd
              local.get $n
              i32.lt_s
              i32.and
              local.set $canDel
              local.get $xi
              i32.const 0
              i32.ge_s
              local.get $xi
              local.get $k
              i32.const 1
              i32.add
              i32.sub
              local.get $m
              i32.lt_s
              i32.and
              local.set $canIns
              local.get $canDel
              local.get $canIns
              i32.or
              if
                local.get $xd
                i32.const 1
                i32.add
                local.set $xDel
                local.get $xi
                local.set $xIns
                local.get $canDel
                local.get $canIns
                i32.eqz
                local.get $xDel
                local.get $xIns
                i32.ge_s
                i32.or
                i32.and
                if (result i32)
                  local.get $xDel
                else
                  local.get $xIns
                end
                local.set $xx
                local.get $xx
                local.get $k
                i32.sub
                local.set $yy
                (block $snake_done
                  (loop $snake
                    local.get $xx
                    local.get $n
                    i32.ge_s
                    br_if $snake_done
                    local.get $yy
                    local.get $m
                    i32.ge_s
                    br_if $snake_done
                    local.get $yy
                    i32.const 0
                    i32.lt_s
                    br_if $snake_done
                    local.get $a
                    local.get $off
                    local.get $xx
                    i32.add
                    i32.const 2
                    i32.shl
                    i32.add
                    i32.load
                    local.get $b
                    local.get $off
                    local.get $yy
                    i32.add
                    i32.const 2
                    i32.shl
                    i32.add
                    i32.load
                    i32.ne
                    br_if $snake_done
                    local.get $xx
                    i32.const 1
                    i32.add
                    local.set $xx
                    local.get $yy
                    i32.const 1
                    i32.add
                    local.set $yy
                    br $snake))
                local.get $v
                local.get $rowOff
                local.get $j
                i32.const 2
                i32.shl
                i32.add
                i32.add
                local.get $xx
                i32.store
                local.get $xx
                local.get $n
                i32.ge_s
                local.get $yy
                local.get $m
                i32.ge_s
                i32.and
                if
                  local.get $d
                  local.set $D
                  br $outer_done
                end
              else
                local.get $v
                local.get $rowOff
                local.get $j
                i32.const 2
                i32.shl
                i32.add
                i32.add
                i32.const -1
                i32.store
              end
              local.get $xi
              local.set $xd
              local.get $j
              i32.const 1
              i32.add
              local.get $d
              i32.lt_s
              if (result i32)
                local.get $v
                local.get $prevOff
                local.get $j
                i32.const 1
                i32.add
                i32.const 2
                i32.shl
                i32.add
                i32.add
                i32.load
              else
                i32.const -1
              end
              local.set $xi
              local.get $j
              i32.const 1
              i32.add
              local.set $j
              local.get $k
              i32.const 2
              i32.add
              local.set $k
              br $inner))
        end
        ;; Sentinels: mark the slots just outside this row's written range
        ;; as unreachable (-1), so the next depth's edge loads (the pre-loop
        ;; xd load reads prev[jLo-1], and the in-loop xi load reads
        ;; prev[jHi+1] for the last k) can never read a stale value left by
        ;; an earlier, longer search in the same V buffer. The banded search
        ;; needs this; the v2 funnel avoided it by construction.
        ;; (row d, jLo-1) = -1 when jLo > 0.
        local.get $jLo
        i32.const 0
        i32.gt_s
        if
          local.get $v
          local.get $rowOff
          local.get $jLo
          i32.const 1
          i32.sub
          i32.const 2
          i32.shl
          i32.add
          i32.add
          i32.const -1
          i32.store
        end
        ;; (row d, jHi+1) = -1 when jHi < d.
        local.get $jHi
        local.get $d
        i32.lt_s
        if
          local.get $v
          local.get $rowOff
          local.get $jHi
          i32.const 1
          i32.add
          i32.const 2
          i32.shl
          i32.add
          i32.add
          i32.const -1
          i32.store
        end
        local.get $d
        i32.const 1
        i32.add
        local.set $d
        br $outer))
    local.get $D)

  ;; Backtrack: writes (kind, count) i32 pairs at $runs in REVERSE order,
  ;; unmerged. Kinds: 0 keep, 1 delete, 2 insert. Returns the pair count.
  (func $backtrack
    (param $a i32) (param $b i32) (param $off i32) (param $n i32) (param $m i32)
    (param $D i32) (param $v i32) (param $runs i32)
    (result i32)
    (local $d i32) (local $k i32) (local $xx i32) (local $count i32)
    (local $j i32) (local $prevOff i32)
    (local $xdRaw i32) (local $xiRaw i32)
    (local $canDel i32) (local $canIns i32)
    (local $xDel i32) (local $xIns i32) (local $del i32) (local $xStart i32)
    (local $keep i32)
    local.get $D
    local.set $d
    local.get $n
    local.get $m
    i32.sub
    local.set $k
    local.get $n
    local.set $xx
    i32.const 0
    local.set $count
    (block $bt_done
      (loop $bt
        local.get $d
        i32.const 0
        i32.le_s
        br_if $bt_done
        local.get $k
        local.get $d
        i32.add
        i32.const 1
        i32.shr_s
        local.set $j
        local.get $d
        i32.const 1
        i32.sub
        call $tri
        i32.const 2
        i32.shl
        local.set $prevOff
        local.get $j
        i32.const 0
        i32.gt_s
        if (result i32)
          local.get $v
          local.get $prevOff
          local.get $j
          i32.const 1
          i32.sub
          i32.const 2
          i32.shl
          i32.add
          i32.add
          i32.load
        else
          i32.const -1
        end
        local.set $xdRaw
        local.get $j
        local.get $d
        i32.lt_s
        if (result i32)
          local.get $v
          local.get $prevOff
          local.get $j
          i32.const 2
          i32.shl
          i32.add
          i32.add
          i32.load
        else
          i32.const -1
        end
        local.set $xiRaw
        local.get $xdRaw
        i32.const 0
        i32.ge_s
        local.get $xdRaw
        local.get $n
        i32.lt_s
        i32.and
        local.set $canDel
        local.get $xiRaw
        i32.const 0
        i32.ge_s
        local.get $xiRaw
        local.get $k
        i32.const 1
        i32.add
        i32.sub
        local.get $m
        i32.lt_s
        i32.and
        local.set $canIns
        local.get $xdRaw
        i32.const 1
        i32.add
        local.set $xDel
        local.get $xiRaw
        local.set $xIns
        local.get $canDel
        local.get $canIns
        i32.eqz
        local.get $xDel
        local.get $xIns
        i32.ge_s
        i32.or
        i32.and
        local.set $del
        local.get $del
        if (result i32)
          local.get $xDel
        else
          local.get $xIns
        end
        local.set $xStart
        local.get $xx
        local.get $xStart
        i32.sub
        local.set $keep
        local.get $keep
        i32.const 0
        i32.gt_s
        if
          local.get $runs
          local.get $count
          i32.const 3
          i32.shl
          i32.add
          i32.const 0
          i32.store
          local.get $runs
          local.get $count
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          local.get $keep
          i32.store
          local.get $count
          i32.const 1
          i32.add
          local.set $count
        end
        local.get $runs
        local.get $count
        i32.const 3
        i32.shl
        i32.add
        local.get $del
        if (result i32)
          i32.const 1
        else
          i32.const 2
        end
        i32.store
        local.get $runs
        local.get $count
        i32.const 3
        i32.shl
        i32.const 4
        i32.add
        i32.add
        i32.const 1
        i32.store
        local.get $count
        i32.const 1
        i32.add
        local.set $count
        local.get $del
        if
          local.get $k
          i32.const 1
          i32.sub
          local.set $k
          local.get $xdRaw
          local.set $xx
        else
          local.get $k
          i32.const 1
          i32.add
          local.set $k
          local.get $xiRaw
          local.set $xx
        end
        local.get $d
        i32.const 1
        i32.sub
        local.set $d
        br $bt))
    local.get $xx
    i32.const 0
    i32.gt_s
    if
      local.get $runs
      local.get $count
      i32.const 3
      i32.shl
      i32.add
      i32.const 0
      i32.store
      local.get $runs
      local.get $count
      i32.const 3
      i32.shl
      i32.const 4
      i32.add
      i32.add
      local.get $xx
      i32.store
      local.get $count
      i32.const 1
      i32.add
      local.set $count
    end
    local.get $count)

  ;; ---- output helpers ----------------------------------------------------
  ;; Write the decimal representation of a non-negative i32 at $out.
  ;; Returns the pointer just past the digits.
  (func $itoa (param $v i32) (param $out i32) (result i32)
    (local $tmp i32)
    (local $nd i32)
    (local $i i32)
    global.get $SCRATCH
    local.set $tmp
    i32.const 0
    local.set $nd
    ;; Special case 0.
    local.get $v
    i32.const 0
    i32.eq
    if
      local.get $out
      i32.const 48
      i32.store8
      local.get $out
      i32.const 1
      i32.add
      return
    end
    (block $dig_done
      (loop $dig
        local.get $v
        i32.const 0
        i32.le_s
        br_if $dig_done
        local.get $tmp
        local.get $nd
        i32.add
        local.get $v
        i32.const 10
        i32.rem_u
        i32.const 48
        i32.add
        i32.store8
        local.get $nd
        i32.const 1
        i32.add
        local.set $nd
        local.get $v
        i32.const 10
        i32.div_u
        local.set $v
        br $dig))
    ;; Digits are reversed in $tmp; copy them forward.
    local.get $nd
    local.set $i
    (block $copy_done
      (loop $copy
        local.get $i
        i32.const 0
        i32.le_s
        br_if $copy_done
        local.get $i
        i32.const 1
        i32.sub
        local.set $i
        local.get $out
        local.get $tmp
        local.get $i
        i32.add
        i32.load8_u
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        local.set $out
        br $copy))
    local.get $out)

  ;; Copy $len bytes from $src to $dst. Returns $dst + $len.
  (func $copy_bytes (param $dst i32) (param $src i32) (param $len i32) (result i32)
    local.get $dst
    local.get $src
    local.get $len
    memory.copy
    local.get $dst
    local.get $len
    i32.add)

  ;; Emit one patch line: op byte, then the line bytes from the span
  ;; [spans[idx], spans[idx+1]) of text $text; if the line has no trailing
  ;; newline, append "\n%\n". Returns the pointer just past the output.
  (func $emit_line (param $op i32) (param $text i32) (param $spans i32)
                   (param $idx i32) (param $out i32) (result i32)
    (local $start i32)
    (local $end i32)
    (local $len i32)
    local.get $spans
    local.get $idx
    i32.const 2
    i32.shl
    i32.add
    i32.load
    local.set $start
    local.get $spans
    local.get $idx
    i32.const 1
    i32.add
    i32.const 2
    i32.shl
    i32.add
    i32.load
    local.set $end
    local.get $end
    local.get $start
    i32.sub
    local.set $len
    local.get $out
    local.get $op
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    local.set $out
    local.get $out
    local.get $text
    local.get $start
    i32.add
    local.get $len
    call $copy_bytes
    local.set $out
    ;; No trailing newline? Append "\n%\n".
    local.get $len
    i32.const 0
    i32.eq
    local.get $text
    local.get $end
    i32.const 1
    i32.sub
    i32.add
    i32.load8_u
    i32.const 10
    i32.ne
    i32.or
    if
      local.get $out
      i32.const 10
      i32.store8
      local.get $out
      i32.const 1
      i32.add
      i32.const 37
      i32.store8
      local.get $out
      i32.const 2
      i32.add
      i32.const 10
      i32.store8
      local.get $out
      i32.const 3
      i32.add
      local.set $out
    end
    local.get $out)

  ;; Format the patch from the forward merged run list into $out.
  ;; Runs are (kind,count) i32 pairs at $runs, $runCount of them, covering
  ;; both texts in full. Returns the output byte length.
  (func $format (param $n i32) (param $m i32) (param $runs i32) (param $runCount i32)
                (param $out i32) (result i32)
    (local $o i32) (local $p i32) (local $deleted i32) (local $inserted i32)
    (local $nChanges i32) (local $nHunks i32)
    (local $i i32) (local $kind i32) (local $cnt i32)
    (local $c i32) (local $co i32) (local $cp i32) (local $cd i32) (local $ci i32)
    (local $h i32) (local $first i32) (local $last i32)
    (local $oldStart i32) (local $newStart i32) (local $after i32)
    (local $oldEnd i32) (local $newEnd i32) (local $at i32)
    (local $po i32) (local $pp i32) (local $pd i32) (local $pi i32)

    ;; Pass 1: runs -> changes (o,p,dels,ins) quads in CHANGES.
    i32.const 0
    local.set $o
    i32.const 0
    local.set $p
    i32.const 0
    local.set $deleted
    i32.const 0
    local.set $inserted
    i32.const 0
    local.set $nChanges
    i32.const 0
    local.set $i
    (block $p1_done
      (loop $p1
        local.get $i
        local.get $runCount
        i32.ge_s
        br_if $p1_done
        local.get $runs
        local.get $i
        i32.const 3
        i32.shl
        i32.add
        i32.load
        local.set $kind
        local.get $runs
        local.get $i
        i32.const 3
        i32.shl
        i32.const 4
        i32.add
        i32.add
        i32.load
        local.set $cnt
        local.get $kind
        i32.const 0
        i32.eq
        if
          local.get $o
          local.get $cnt
          i32.add
          local.set $o
          local.get $p
          local.get $cnt
          i32.add
          local.set $p
        else
          ;; Merge into the last change when contiguous, else start one.
          local.get $nChanges
          i32.const 0
          i32.gt_s
          if
            global.get $CHANGES
            local.get $nChanges
            i32.const 1
            i32.sub
            i32.const 4
            i32.shl
            i32.add
            i32.load
            local.set $co
            global.get $CHANGES
            local.get $nChanges
            i32.const 1
            i32.sub
            i32.const 4
            i32.shl
            i32.const 4
            i32.add
            i32.add
            i32.load
            local.set $cp
            global.get $CHANGES
            local.get $nChanges
            i32.const 1
            i32.sub
            i32.const 4
            i32.shl
            i32.const 8
            i32.add
            i32.add
            i32.load
            local.set $cd
            global.get $CHANGES
            local.get $nChanges
            i32.const 1
            i32.sub
            i32.const 4
            i32.shl
            i32.const 12
            i32.add
            i32.add
            i32.load
            local.set $ci
          end
          ;; contiguous = nChanges>0 && co+cd==o && cp+ci==p
          local.get $nChanges
          i32.const 0
          i32.gt_s
          local.get $co
          local.get $cd
          i32.add
          local.get $o
          i32.eq
          i32.and
          local.get $cp
          local.get $ci
          i32.add
          local.get $p
          i32.eq
          i32.and
          if
            ;; Update the last change in place.
            local.get $kind
            i32.const 1
            i32.eq
            if
              global.get $CHANGES
              local.get $nChanges
              i32.const 1
              i32.sub
              i32.const 4
              i32.shl
              i32.const 8
              i32.add
              i32.add
              local.get $cd
              local.get $cnt
              i32.add
              i32.store
              local.get $o
              local.get $cnt
              i32.add
              local.set $o
              local.get $deleted
              local.get $cnt
              i32.add
              local.set $deleted
            else
              global.get $CHANGES
              local.get $nChanges
              i32.const 1
              i32.sub
              i32.const 4
              i32.shl
              i32.const 12
              i32.add
              i32.add
              local.get $ci
              local.get $cnt
              i32.add
              i32.store
              local.get $p
              local.get $cnt
              i32.add
              local.set $p
              local.get $inserted
              local.get $cnt
              i32.add
              local.set $inserted
            end
          else
            global.get $CHANGES
            local.get $nChanges
            i32.const 4
            i32.shl
            i32.add
            local.get $o
            i32.store
            global.get $CHANGES
            local.get $nChanges
            i32.const 4
            i32.shl
            i32.const 4
            i32.add
            i32.add
            local.get $p
            i32.store
            global.get $CHANGES
            local.get $nChanges
            i32.const 4
            i32.shl
            i32.const 8
            i32.add
            i32.add
            local.get $kind
            i32.const 1
            i32.eq
            if (result i32)
              local.get $cnt
            else
              i32.const 0
            end
            i32.store
            global.get $CHANGES
            local.get $nChanges
            i32.const 4
            i32.shl
            i32.const 12
            i32.add
            i32.add
            local.get $kind
            i32.const 2
            i32.eq
            if (result i32)
              local.get $cnt
            else
              i32.const 0
            end
            i32.store
            local.get $kind
            i32.const 1
            i32.eq
            if
              local.get $o
              local.get $cnt
              i32.add
              local.set $o
              local.get $deleted
              local.get $cnt
              i32.add
              local.set $deleted
            else
              local.get $p
              local.get $cnt
              i32.add
              local.set $p
              local.get $inserted
              local.get $cnt
              i32.add
              local.set $inserted
            end
            local.get $nChanges
            i32.const 1
            i32.add
            local.set $nChanges
          end
        end
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $p1))

    ;; Count hunks: changes at most 6 kept lines apart share a hunk.
    i32.const 0
    local.set $nHunks
    i32.const 0
    local.set $i
    (block $h_done
      (loop $h
        local.get $i
        local.get $nChanges
        i32.ge_s
        br_if $h_done
        local.get $nHunks
        i32.const 1
        i32.add
        local.set $nHunks
        ;; Advance while the next change is within 6 kept lines.
        (block $adv_done
          (loop $adv
            local.get $i
            i32.const 1
            i32.add
            local.get $nChanges
            i32.ge_s
            br_if $adv_done
            ;; gap = c[i+1].o - (c[i].o + c[i].dels)
            global.get $CHANGES
            local.get $i
            i32.const 1
            i32.add
            i32.const 4
            i32.shl
            i32.add
            i32.load
            global.get $CHANGES
            local.get $i
            i32.const 4
            i32.shl
            i32.add
            i32.load
            global.get $CHANGES
            local.get $i
            i32.const 4
            i32.shl
            i32.const 8
            i32.add
            i32.add
            i32.load
            i32.add
            i32.sub
            i32.const 6
            i32.gt_s
            br_if $adv_done
            local.get $i
            i32.const 1
            i32.add
            local.set $i
            br $adv))
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $h))

    ;; Emit the header: makefun-diff/1 old=N new=M hunks=H deleted=D inserted=I\n
    local.get $out
    i32.const 109 ;; 'm'
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    i32.const 97 ;; 'a'
    i32.store8
    local.get $out
    i32.const 2
    i32.add
    i32.const 107 ;; 'k'
    i32.store8
    local.get $out
    i32.const 3
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 4
    i32.add
    i32.const 102 ;; 'f'
    i32.store8
    local.get $out
    i32.const 5
    i32.add
    i32.const 117 ;; 'u'
    i32.store8
    local.get $out
    i32.const 6
    i32.add
    i32.const 110 ;; 'n'
    i32.store8
    local.get $out
    i32.const 7
    i32.add
    i32.const 45 ;; '-'
    i32.store8
    local.get $out
    i32.const 8
    i32.add
    i32.const 100 ;; 'd'
    i32.store8
    local.get $out
    i32.const 9
    i32.add
    i32.const 105 ;; 'i'
    i32.store8
    local.get $out
    i32.const 10
    i32.add
    i32.const 102 ;; 'f'
    i32.store8
    local.get $out
    i32.const 11
    i32.add
    i32.const 102 ;; 'f'
    i32.store8
    local.get $out
    i32.const 12
    i32.add
    i32.const 47 ;; '/'
    i32.store8
    local.get $out
    i32.const 13
    i32.add
    i32.const 49 ;; '1'
    i32.store8
    local.get $out
    i32.const 14
    i32.add
    i32.const 32 ;; ' '
    i32.store8
    local.get $out
    i32.const 15
    i32.add
    i32.const 111 ;; 'o'
    i32.store8
    local.get $out
    i32.const 16
    i32.add
    i32.const 108 ;; 'l'
    i32.store8
    local.get $out
    i32.const 17
    i32.add
    i32.const 100 ;; 'd'
    i32.store8
    local.get $out
    i32.const 18
    i32.add
    i32.const 61 ;; '='
    i32.store8
    local.get $out
    i32.const 19
    i32.add
    local.set $out
    local.get $n
    local.get $out
    call $itoa
    local.set $out
    local.get $out
    i32.const 32
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    i32.const 110 ;; 'n'
    i32.store8
    local.get $out
    i32.const 2
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 3
    i32.add
    i32.const 119 ;; 'w'
    i32.store8
    local.get $out
    i32.const 4
    i32.add
    i32.const 61 ;; '='
    i32.store8
    local.get $out
    i32.const 5
    i32.add
    local.set $out
    local.get $m
    local.get $out
    call $itoa
    local.set $out
    local.get $out
    i32.const 32
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    i32.const 104 ;; 'h'
    i32.store8
    local.get $out
    i32.const 2
    i32.add
    i32.const 117 ;; 'u'
    i32.store8
    local.get $out
    i32.const 3
    i32.add
    i32.const 110 ;; 'n'
    i32.store8
    local.get $out
    i32.const 4
    i32.add
    i32.const 107 ;; 'k'
    i32.store8
    local.get $out
    i32.const 5
    i32.add
    i32.const 115 ;; 's'
    i32.store8
    local.get $out
    i32.const 6
    i32.add
    i32.const 61 ;; '='
    i32.store8
    local.get $out
    i32.const 7
    i32.add
    local.set $out
    local.get $nHunks
    local.get $out
    call $itoa
    local.set $out
    local.get $out
    i32.const 32
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    i32.const 100 ;; 'd'
    i32.store8
    local.get $out
    i32.const 2
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 3
    i32.add
    i32.const 108 ;; 'l'
    i32.store8
    local.get $out
    i32.const 4
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 5
    i32.add
    i32.const 116 ;; 't'
    i32.store8
    local.get $out
    i32.const 6
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 7
    i32.add
    i32.const 100 ;; 'd'
    i32.store8
    local.get $out
    i32.const 8
    i32.add
    i32.const 61 ;; '='
    i32.store8
    local.get $out
    i32.const 9
    i32.add
    local.set $out
    local.get $deleted
    local.get $out
    call $itoa
    local.set $out
    local.get $out
    i32.const 32
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    i32.const 105 ;; 'i'
    i32.store8
    local.get $out
    i32.const 2
    i32.add
    i32.const 110 ;; 'n'
    i32.store8
    local.get $out
    i32.const 3
    i32.add
    i32.const 115 ;; 's'
    i32.store8
    local.get $out
    i32.const 4
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 5
    i32.add
    i32.const 114 ;; 'r'
    i32.store8
    local.get $out
    i32.const 6
    i32.add
    i32.const 116 ;; 't'
    i32.store8
    local.get $out
    i32.const 7
    i32.add
    i32.const 101 ;; 'e'
    i32.store8
    local.get $out
    i32.const 8
    i32.add
    i32.const 100 ;; 'd'
    i32.store8
    local.get $out
    i32.const 9
    i32.add
    i32.const 61 ;; '='
    i32.store8
    local.get $out
    i32.const 10
    i32.add
    local.set $out
    local.get $inserted
    local.get $out
    call $itoa
    local.set $out
    local.get $out
    i32.const 10 ;; '\n'
    i32.store8
    local.get $out
    i32.const 1
    i32.add
    local.set $out

    ;; Pass 2: emit each hunk.
    i32.const 0
    local.set $h
    (block $emit_done
      (loop $emit
        local.get $h
        local.get $nChanges
        i32.ge_s
        br_if $emit_done
        ;; Hunk = changes [h .. last] while gap <= 6.
        local.get $h
        local.set $first
        local.get $h
        local.set $last
        (block $grow_done
          (loop $grow
            local.get $last
            i32.const 1
            i32.add
            local.get $nChanges
            i32.ge_s
            br_if $grow_done
            global.get $CHANGES
            local.get $last
            i32.const 1
            i32.add
            i32.const 4
            i32.shl
            i32.add
            i32.load
            global.get $CHANGES
            local.get $last
            i32.const 4
            i32.shl
            i32.add
            i32.load
            global.get $CHANGES
            local.get $last
            i32.const 4
            i32.shl
            i32.const 8
            i32.add
            i32.add
            i32.load
            i32.add
            i32.sub
            i32.const 6
            i32.gt_s
            br_if $grow_done
            local.get $last
            i32.const 1
            i32.add
            local.set $last
            br $grow))
        ;; first/last change quads.
        global.get $CHANGES
        local.get $first
        i32.const 4
        i32.shl
        i32.add
        i32.load
        local.set $co
        global.get $CHANGES
        local.get $first
        i32.const 4
        i32.shl
        i32.const 4
        i32.add
        i32.add
        i32.load
        local.set $cp
        global.get $CHANGES
        local.get $first
        i32.const 4
        i32.shl
        i32.const 8
        i32.add
        i32.add
        i32.load
        local.set $cd
        global.get $CHANGES
        local.get $first
        i32.const 4
        i32.shl
        i32.const 12
        i32.add
        i32.add
        i32.load
        local.set $ci
        ;; last change quads (reuse $po..$pi as the last change).
        global.get $CHANGES
        local.get $last
        i32.const 4
        i32.shl
        i32.add
        i32.load
        local.set $po
        global.get $CHANGES
        local.get $last
        i32.const 4
        i32.shl
        i32.const 4
        i32.add
        i32.add
        i32.load
        local.set $pp
        global.get $CHANGES
        local.get $last
        i32.const 4
        i32.shl
        i32.const 8
        i32.add
        i32.add
        i32.load
        local.set $pd
        global.get $CHANGES
        local.get $last
        i32.const 4
        i32.shl
        i32.const 12
        i32.add
        i32.add
        i32.load
        local.set $pi
        ;; oldStart = max(0, first.o - 3); newStart = first.p - (first.o - oldStart)
        ;; after = min(3, n - (last.o + last.dels))
        ;; oldEnd = last.o + last.dels + after; newEnd = last.p + last.ins + after
        local.get $co
        i32.const 3
        i32.sub
        i32.const 0
        local.get $co
        i32.const 3
        i32.sub
        i32.const 0
        i32.gt_s
        select
        local.set $oldStart
        local.get $cp
        local.get $co
        local.get $oldStart
        i32.sub
        i32.sub
        local.set $newStart
        local.get $n
        local.get $po
        local.get $pd
        i32.add
        i32.sub
        i32.const 3
        local.get $n
        local.get $po
        local.get $pd
        i32.add
        i32.sub
        i32.const 3
        i32.lt_s
        select
        local.set $after
        local.get $po
        local.get $pd
        i32.add
        local.get $after
        i32.add
        local.set $oldEnd
        local.get $pp
        local.get $pi
        i32.add
        local.get $after
        i32.add
        local.set $newEnd
        ;; Emit "@ oldStart+1 oldEnd-oldStart newStart+1 newEnd-newStart\n"
        local.get $out
        i32.const 64 ;; '@'
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        i32.const 32
        i32.store8
        local.get $out
        i32.const 2
        i32.add
        local.set $out
        local.get $oldStart
        i32.const 1
        i32.add
        local.get $out
        call $itoa
        local.set $out
        local.get $out
        i32.const 32
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        local.set $out
        local.get $oldEnd
        local.get $oldStart
        i32.sub
        local.get $out
        call $itoa
        local.set $out
        local.get $out
        i32.const 32
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        local.set $out
        local.get $newStart
        i32.const 1
        i32.add
        local.get $out
        call $itoa
        local.set $out
        local.get $out
        i32.const 32
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        local.set $out
        local.get $newEnd
        local.get $newStart
        i32.sub
        local.get $out
        call $itoa
        local.set $out
        local.get $out
        i32.const 10
        i32.store8
        local.get $out
        i32.const 1
        i32.add
        local.set $out
        ;; Body: for each change in [first..last], context + dels + ins.
        local.get $oldStart
        local.set $at
        local.get $first
        local.set $c
        (block $body_done
          (loop $body
            local.get $c
            local.get $last
            i32.gt_s
            br_if $body_done
            global.get $CHANGES
            local.get $c
            i32.const 4
            i32.shl
            i32.add
            i32.load
            local.set $co
            global.get $CHANGES
            local.get $c
            i32.const 4
            i32.shl
            i32.const 4
            i32.add
            i32.add
            i32.load
            local.set $cp
            global.get $CHANGES
            local.get $c
            i32.const 4
            i32.shl
            i32.const 8
            i32.add
            i32.add
            i32.load
            local.set $cd
            global.get $CHANGES
            local.get $c
            i32.const 4
            i32.shl
            i32.const 12
            i32.add
            i32.add
            i32.load
            local.set $ci
            ;; KEEP lines aStr[at .. c.o)
            (block $keep1_done
              (loop $keep1
                local.get $at
                local.get $co
                i32.ge_s
                br_if $keep1_done
                i32.const 61 ;; '='
                global.get $IN_OLD
                global.get $SPANS_OLD
                local.get $at
                local.get $out
                call $emit_line
                local.set $out
                local.get $at
                i32.const 1
                i32.add
                local.set $at
                br $keep1))
            ;; DELETE lines aStr[c.o .. c.o+dels)
            local.get $co
            local.set $at
            (block $del_done
              (loop $del
                local.get $at
                local.get $co
                local.get $cd
                i32.add
                i32.ge_s
                br_if $del_done
                i32.const 45 ;; '-'
                global.get $IN_OLD
                global.get $SPANS_OLD
                local.get $at
                local.get $out
                call $emit_line
                local.set $out
                local.get $at
                i32.const 1
                i32.add
                local.set $at
                br $del))
            ;; INSERT lines bStr[c.p .. c.p+ins)
            local.get $cp
            local.set $at
            (block $ins_done
              (loop $ins
                local.get $at
                local.get $cp
                local.get $ci
                i32.add
                i32.ge_s
                br_if $ins_done
                i32.const 43 ;; '+'
                global.get $IN_NEW
                global.get $SPANS_NEW
                local.get $at
                local.get $out
                call $emit_line
                local.set $out
                local.get $at
                i32.const 1
                i32.add
                local.set $at
                br $ins))
            ;; at = c.o + c.dels
            local.get $co
            local.get $cd
            i32.add
            local.set $at
            local.get $c
            i32.const 1
            i32.add
            local.set $c
            br $body))
        ;; Trailing KEEP lines aStr[at .. oldEnd)
        (block $keep2_done
          (loop $keep2
            local.get $at
            local.get $oldEnd
            i32.ge_s
            br_if $keep2_done
            i32.const 61 ;; '='
            global.get $IN_OLD
            global.get $SPANS_OLD
            local.get $at
            local.get $out
            call $emit_line
            local.set $out
            local.get $at
            i32.const 1
            i32.add
            local.set $at
            br $keep2))
        ;; Next hunk starts after $last.
        local.get $last
        i32.const 1
        i32.add
        local.set $h
        br $emit))
    ;; Output length = out - $OUT... the caller passes $out as the base;
    ;; recompute from the initial pointer kept in $po? No: $out was advanced.
    ;; The caller knows the base; return length via a global-free trick:
    ;; length is (current $out) - (the $out param on entry). We saved the
    ;; entry $out in $po at the start? We did not. Fix: the entry pointer is
    ;; recovered below from the first local? -- replaced by the solve()
    ;; wrapper, which passes the base separately. This function returns the
    ;; END pointer; solve() subtracts the base.
    local.get $out)

  ;; ---- top-level solve ---------------------------------------------------
  ;; solve(oldPtr, oldLen, newPtr, newLen, outPtr, dMaxHint) -> i64 packed
  ;; (outLen << 32) | D. The caller (JS) copies the UTF-8 texts to
  ;; IN_OLD / IN_NEW first and decodes [OUT, OUT+outLen) after.
  (func (export "solve")
    (param $oldPtr i32) (param $oldLen i32) (param $newPtr i32) (param $newLen i32)
    (param $outPtr i32) (param $dMaxHint i32)
    (result i64)
    (local $n i32) (local $m i32)
    (local $prefix i32) (local $suffix i32) (local $mn i32) (local $mm i32)
    (local $dMax i32) (local $D i32) (local $count i32)
    (local $finalCount i32) (local $i i32) (local $j i32)
    (local $kind i32) (local $cnt i32) (local $outEnd i32) (local $outLen i32)

    ;; Reset the intern table and the id counter.
    global.get $TABLE
    i32.const 0
    i32.const 3145728
    memory.fill
    i32.const 0
    global.set $next_id

    ;; Inputs must fit the fixed input regions (the JS loader guarantees
    ;; this; the check is here so a bad caller traps instead of corrupting
    ;; the layout).
    local.get $oldLen
    i32.const 2097152
    i32.gt_s
    if unreachable end
    local.get $newLen
    i32.const 2097152
    i32.gt_s
    if unreachable end

    ;; Inputs already live at IN_OLD/IN_NEW (the JS loader encodes into
    ;; those fixed regions); copy only if a foreign caller passed
    ;; different pointers.
    local.get $oldPtr
    global.get $IN_OLD
    i32.ne
    if
      global.get $IN_OLD
      local.get $oldPtr
      local.get $oldLen
      memory.copy
    end
    local.get $newPtr
    global.get $IN_NEW
    i32.ne
    if
      global.get $IN_NEW
      local.get $newPtr
      local.get $newLen
      memory.copy
    end

    ;; Tokenize + intern both texts (fused: scan + hash + probe + counts).
    i32.const 0
    global.get $IN_OLD
    local.get $oldLen
    global.get $SPANS_OLD
    global.get $IDS_OLD
    call $tokenize_text
    local.set $n
    i32.const 1
    global.get $IN_NEW
    local.get $newLen
    global.get $SPANS_NEW
    global.get $IDS_NEW
    call $tokenize_text
    local.set $m

    ;; Common prefix, then common suffix of what is left.
    i32.const 0
    local.set $prefix
    (block $pre_done
      (loop $pre
        local.get $prefix
        local.get $n
        i32.ge_s
        br_if $pre_done
        local.get $prefix
        local.get $m
        i32.ge_s
        br_if $pre_done
        global.get $IDS_OLD
        local.get $prefix
        i32.const 2
        i32.shl
        i32.add
        i32.load
        global.get $IDS_NEW
        local.get $prefix
        i32.const 2
        i32.shl
        i32.add
        i32.load
        i32.ne
        br_if $pre_done
        local.get $prefix
        i32.const 1
        i32.add
        local.set $prefix
        br $pre))
    i32.const 0
    local.set $suffix
    (block $suf_done
      (loop $suf
        local.get $suffix
        local.get $n
        local.get $prefix
        i32.sub
        i32.ge_s
        br_if $suf_done
        local.get $suffix
        local.get $m
        local.get $prefix
        i32.sub
        i32.ge_s
        br_if $suf_done
        global.get $IDS_OLD
        local.get $n
        i32.const 1
        i32.sub
        local.get $suffix
        i32.sub
        i32.const 2
        i32.shl
        i32.add
        i32.load
        global.get $IDS_NEW
        local.get $m
        i32.const 1
        i32.sub
        local.get $suffix
        i32.sub
        i32.const 2
        i32.shl
        i32.add
        i32.load
        i32.ne
        br_if $suf_done
        local.get $suffix
        i32.const 1
        i32.add
        local.set $suffix
        br $suf))
    local.get $n
    local.get $prefix
    i32.sub
    local.get $suffix
    i32.sub
    local.set $mn
    local.get $m
    local.get $prefix
    i32.sub
    local.get $suffix
    i32.sub
    local.set $mm

    ;; Search the middle slice.
    i32.const -1
    local.set $D
    local.get $mn
    i32.const 0
    i32.ne
    local.get $mm
    i32.const 0
    i32.ne
    i32.or
    if
      ;; Patience-guided attempt (v5): LIS anchors + per-gap DP give
      ;; the patience k(d) table; try the narrow band first, fall back
      ;; to the v3 band on a miss.
      local.get $n
      local.get $m
      call $build_anchors
      global.get $N_ANCHORS
      i32.const 100
      i32.ge_s
      if
        global.get $D_ANCHOR
        local.set $dMax
        global.get $V
        local.get $dMax
        i32.const 1
        i32.add
        call $tri
        i32.const 2
        i32.shl
        i32.add
        call $ensure_mem
        global.get $IDS_OLD
        global.get $IDS_NEW
        local.get $prefix
        local.get $mn
        local.get $mm
        local.get $dMax
        global.get $V
        i32.const -3
        call $search
        local.set $D
        ;; Accept only if D == $D_ANCHOR (the patience/DP total);
        ;; otherwise the band missed the optimal path — fall back to
        ;; the v3 band.
        local.get $D
        i32.const 0
        i32.ge_s
        local.get $D
        global.get $D_ANCHOR
        i32.ne
        i32.and
        if
          i32.const -1
          local.set $D
        end
      end
      ;; Only run the v3 band if the anchor attempt did not find a path.
      local.get $D
      i32.const 0
      i32.lt_s
      if
      local.get $dMaxHint
      local.set $dMax
      ;; Make sure the V region fits dMax.
      global.get $V
      local.get $dMax
      i32.const 1
      i32.add
      call $tri
      i32.const 2
      i32.shl
      i32.add
      call $ensure_mem
      global.get $IDS_OLD
      global.get $IDS_NEW
      local.get $prefix
      local.get $mn
      local.get $mm
      local.get $dMax
      global.get $V
      i32.const 150
      call $search
      local.set $D
      ;; Band miss: widen in doubling steps instead of jumping straight to
      ;; mn+mm (whose triangular rows would need ~5 GB for a 25k-line
      ;; middle slice). Any dMax >= the true D finds the exact path, so
      ;; this stays exact; it only costs a re-run on the rare miss.
      (block $retry_done
        (loop $retry
          local.get $D
          i32.const 0
          i32.ge_s
          br_if $retry_done
          local.get $dMax
          local.get $mn
          local.get $mm
          i32.add
          i32.ge_s
          br_if $retry_done
          ;; dMax = min(mn+mm, dMax*2)
          local.get $dMax
          i32.const 2
          i32.mul
          local.get $mn
          local.get $mm
          i32.add
          local.get $dMax
          i32.const 2
          i32.mul
          local.get $mn
          local.get $mm
          i32.add
          i32.lt_s
          select
          local.set $dMax
          global.get $V
          local.get $dMax
          i32.const 1
          i32.add
          call $tri
          i32.const 2
          i32.shl
          i32.add
          call $ensure_mem
          global.get $IDS_OLD
          global.get $IDS_NEW
          local.get $prefix
          local.get $mn
          local.get $mm
          local.get $dMax
          global.get $V
          i32.const 150
          call $search
          local.set $D
          br $retry))
      end
      ;; Still no path: the band is too narrow for this input. Fall back
      ;; to the full (unbanded) search at dMax = mn + mm. V is already
      ;; sized for mn+mm by the retry loop's last ensure_mem.
      local.get $D
      i32.const 0
      i32.lt_s
      if
        local.get $mn
        local.get $mm
        i32.add
        local.set $dMax
        global.get $IDS_OLD
        global.get $IDS_NEW
        local.get $prefix
        local.get $mn
        local.get $mm
        local.get $dMax
        global.get $V
        i32.const -1
        call $search
        local.set $D
      end
      local.get $D
      i32.const 0
      i32.lt_s
      if unreachable end
    end

    ;; If the search block was skipped (mn==0 or mm==0), $D is still -1;
    ;; normalize to 0 to match the v3 packed return (the loader only uses
    ;; $D as a next-call hint; the true D there is mn+mm, all ins/del).
    local.get $D
    i32.const 0
    i32.lt_s
    if
      i32.const 0
      local.set $D
    end

    ;; Backtrack to reversed unmerged runs, then normalize into the final
    ;; forward merged run list (prefix keep + middle + suffix keep).
    i32.const 0
    local.set $finalCount
    local.get $D
    i32.const 0
    i32.gt_s
    if
      global.get $IDS_OLD
      global.get $IDS_NEW
      local.get $prefix
      local.get $mn
      local.get $mm
      local.get $D
      global.get $V
      global.get $RUNS
      call $backtrack
      local.set $count
      ;; Reverse the pairs in place (swap pair i with pair count-1-i).
      i32.const 0
      local.set $i
      (block $rev_done
        (loop $rev
          local.get $i
          local.get $count
          i32.const 1
          i32.sub
          local.get $i
          i32.sub
          i32.ge_s
          br_if $rev_done
          ;; j = count-1-i
          local.get $count
          i32.const 1
          i32.sub
          local.get $i
          i32.sub
          local.set $j
          ;; swap kinds
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.add
          i32.load
          local.set $kind
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.add
          global.get $RUNS
          local.get $j
          i32.const 3
          i32.shl
          i32.add
          i32.load
          i32.store
          global.get $RUNS
          local.get $j
          i32.const 3
          i32.shl
          i32.add
          local.get $kind
          i32.store
          ;; swap counts
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          i32.load
          local.set $cnt
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          global.get $RUNS
          local.get $j
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          i32.load
          i32.store
          global.get $RUNS
          local.get $j
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          local.get $cnt
          i32.store
          local.get $i
          i32.const 1
          i32.add
          local.set $i
          br $rev))
    end
    ;; Build RUNS_FINAL: [prefix keep?] + reversed-merged middle + [suffix keep?]
    ;; First the prefix keep.
    local.get $prefix
    i32.const 0
    i32.gt_s
    if
      global.get $RUNS_FINAL
      i32.const 0
      i32.store
      global.get $RUNS_FINAL
      i32.const 4
      i32.add
      local.get $prefix
      i32.store
      i32.const 1
      local.set $finalCount
    end
    ;; Then the middle runs, merging consecutive equal kinds.
    local.get $D
    i32.const 0
    i32.gt_s
    if
      i32.const 0
      local.set $i
      (block $merge_done
        (loop $merge
          local.get $i
          local.get $count
          i32.ge_s
          br_if $merge_done
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.add
          i32.load
          local.set $kind
          global.get $RUNS
          local.get $i
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          i32.load
          local.set $cnt
          ;; Merge with the last final run when the kind matches.
          local.get $finalCount
          i32.const 0
          i32.gt_s
          if
            global.get $RUNS_FINAL
            local.get $finalCount
            i32.const 1
            i32.sub
            i32.const 3
            i32.shl
            i32.add
            i32.load
            local.get $kind
            i32.eq
            if
              global.get $RUNS_FINAL
              local.get $finalCount
              i32.const 1
              i32.sub
              i32.const 3
              i32.shl
              i32.const 4
              i32.add
              i32.add
              global.get $RUNS_FINAL
              local.get $finalCount
              i32.const 1
              i32.sub
              i32.const 3
              i32.shl
              i32.const 4
              i32.add
              i32.add
              i32.load
              local.get $cnt
              i32.add
              i32.store
              local.get $i
              i32.const 1
              i32.add
              local.set $i
              br $merge
            end
          end
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 3
          i32.shl
          i32.add
          local.get $kind
          i32.store
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          local.get $cnt
          i32.store
          local.get $finalCount
          i32.const 1
          i32.add
          local.set $finalCount
          local.get $i
          i32.const 1
          i32.add
          local.set $i
          br $merge))
    end
    ;; Then the suffix keep (merge with the last run when it is a keep).
    local.get $suffix
    i32.const 0
    i32.gt_s
    if
      local.get $finalCount
      i32.const 0
      i32.gt_s
      if
        global.get $RUNS_FINAL
        local.get $finalCount
        i32.const 1
        i32.sub
        i32.const 3
        i32.shl
        i32.add
        i32.load
        i32.const 0
        i32.eq
        if
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 1
          i32.sub
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 1
          i32.sub
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          i32.load
          local.get $suffix
          i32.add
          i32.store
        else
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 3
          i32.shl
          i32.add
          i32.const 0
          i32.store
          global.get $RUNS_FINAL
          local.get $finalCount
          i32.const 3
          i32.shl
          i32.const 4
          i32.add
          i32.add
          local.get $suffix
          i32.store
          local.get $finalCount
          i32.const 1
          i32.add
          local.set $finalCount
        end
      else
        global.get $RUNS_FINAL
        i32.const 0
        i32.store
        global.get $RUNS_FINAL
        i32.const 4
        i32.add
        local.get $suffix
        i32.store
        i32.const 1
        local.set $finalCount
      end
    end

    ;; Format into the caller's outPtr.
    local.get $n
    local.get $m
    global.get $RUNS_FINAL
    local.get $finalCount
    local.get $outPtr
    call $format
    local.set $outEnd
    local.get $outEnd
    local.get $outPtr
    i32.sub
    local.set $outLen

    ;; Pack (outLen << 32) | D.
    local.get $outLen
    i64.extend_i32_u
    i64.const 32
    i64.shl
    local.get $D
    i64.extend_i32_u
    i64.or)
)
