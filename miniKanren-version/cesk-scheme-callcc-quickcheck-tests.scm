#!/usr/bin/env scheme-script
(import (rnrs)
        (mk-lib)
        (lookupo-lib)
        (test-check-lib)
        (cesk-scheme-callcc)
        (rename (cesk-scheme-callcc-simple-dummy-v-out) (evalo evalo-simple) (eval-expo eval-expo-simple) (empty-env empty-env-simple) (empty-store empty-store-simple) (empty-k empty-k-simple)))

(define max-tries 200)

(define bounded-search
  (lambda (r max-tries)
    (let ((n 0))
      (lambda (a)
        (if (= n max-tries)
          ((== r `(reached ,max-tries)) a)
          (begin
            (set! n (+ 1 n))
            (fail a)))))))

(define check-evalo
  (lambda (evalo-simple evalo)
    (lambda (r max-tries)
      (let ((ok (bounded-search r max-tries)))
        (fresh (exp val)
          (evalo-simple exp val)
          (conda
            [(evalo exp val) ok]
            [(== r `(counterexample ,exp ,val))]))))))

(test "check-evalo"
  (run 1 (q) ((check-evalo evalo-simple evalo) q max-tries))
  `((reached ,max-tries)))
