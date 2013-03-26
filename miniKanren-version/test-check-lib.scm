(library (test-check-lib)
  (export test test-disable)
  (import (rnrs) (only (chezscheme) errorf printf))

  (define-syntax test
    (syntax-rules ()
      ((_ title tested-expression expected-result)
       (begin
         (printf "Testing ~s\n" title)
         (let* ((expected expected-result)
                (produced tested-expression))
           (or (equal? expected produced)
               (errorf 'test
                       "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                       'tested-expression expected produced)))))))

  (define-syntax test-disable
    (syntax-rules ()
      ((_ title tested-expression expected-result)
       (begin
         (printf "Disable testing ~s\n" title)
         #t))))

)