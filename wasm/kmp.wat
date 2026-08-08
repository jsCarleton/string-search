(module
  ;; Knuth-Morris-Pratt string matching.
  ;;
  ;; The caller is responsible for placing the text and pattern bytes into
  ;; linear memory (e.g. via TextEncoder in JS) and for providing a scratch
  ;; buffer for the pattern's failure ("lps") table, which is one i32 per
  ;; pattern byte (4 * patLen bytes).
  (memory (export "memory") 1)

  ;; Build the "longest proper prefix which is also a suffix" table used to
  ;; skip re-comparisons on a mismatch.
  (func $build_lps (export "build_lps")
    (param $patPtr i32) (param $patLen i32) (param $lpsPtr i32)
    (local $len i32)   ;; length of the current longest prefix-suffix
    (local $i i32)
    (local $prevLen i32)

    (if (i32.eqz (local.get $patLen)) (then (return)))

    ;; lps[0] is always 0
    (i32.store (local.get $lpsPtr) (i32.const 0))
    (local.set $len (i32.const 0))
    (local.set $i (i32.const 1))

    (block $done
      (loop $loop
        (br_if $done (i32.ge_s (local.get $i) (local.get $patLen)))

        (if (i32.eq
              (i32.load8_u (i32.add (local.get $patPtr) (local.get $i)))
              (i32.load8_u (i32.add (local.get $patPtr) (local.get $len))))
          (then
            (local.set $len (i32.add (local.get $len) (i32.const 1)))
            (i32.store
              (i32.add (local.get $lpsPtr) (i32.shl (local.get $i) (i32.const 2)))
              (local.get $len))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
          )
          (else
            (if (i32.ne (local.get $len) (i32.const 0))
              (then
                (local.set $prevLen
                  (i32.load
                    (i32.add (local.get $lpsPtr)
                      (i32.shl (i32.sub (local.get $len) (i32.const 1)) (i32.const 2)))))
                (local.set $len (local.get $prevLen))
              )
              (else
                (i32.store
                  (i32.add (local.get $lpsPtr) (i32.shl (local.get $i) (i32.const 2)))
                  (i32.const 0))
                (local.set $i (i32.add (local.get $i) (i32.const 1)))
              )
            )
          )
        )
        (br $loop)
      )
    )
  )

  ;; Search for the first occurrence of pattern[0..patLen) in
  ;; text[0..textLen), using the KMP algorithm. Returns the index of the
  ;; match in text, or -1 if the pattern does not occur.
  (func $kmp_search (export "kmp_search")
    (param $textPtr i32) (param $textLen i32)
    (param $patPtr i32) (param $patLen i32)
    (param $lpsPtr i32)
    (result i32)
    (local $i i32)  ;; index into text
    (local $j i32)  ;; index into pattern

    (if (i32.eqz (local.get $patLen))
      (then (return (i32.const 0)))
    )

    (call $build_lps (local.get $patPtr) (local.get $patLen) (local.get $lpsPtr))

    (local.set $i (i32.const 0))
    (local.set $j (i32.const 0))

    (block $done
      (loop $loop
        (br_if $done (i32.ge_s (local.get $i) (local.get $textLen)))

        (if (i32.eq
              (i32.load8_u (i32.add (local.get $textPtr) (local.get $i)))
              (i32.load8_u (i32.add (local.get $patPtr) (local.get $j))))
          (then
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))
            (if (i32.eq (local.get $j) (local.get $patLen))
              (then
                (return (i32.sub (local.get $i) (local.get $j)))
              )
            )
          )
          (else
            (if (i32.ne (local.get $j) (i32.const 0))
              (then
                (local.set $j
                  (i32.load
                    (i32.add (local.get $lpsPtr)
                      (i32.shl (i32.sub (local.get $j) (i32.const 1)) (i32.const 2)))))
              )
              (else
                (local.set $i (i32.add (local.get $i) (i32.const 1)))
              )
            )
          )
        )
        (br $loop)
      )
    )

    (i32.const -1)
  )
)
