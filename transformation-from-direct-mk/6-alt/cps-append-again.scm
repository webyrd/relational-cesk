(load "mk.scm")

(load "pmatch.scm")

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))


(define append-tests
  (lambda (append name)
    (let ()

      (test-check (string-append "append-1-" name)
        (append '() '())
        '())
      
      (test-check (string-append "append-2-" name)
        (append '() '(d e))
        '(d e))
      
      (test-check (string-append "append-3-" name)
        (append '(a b c) '())
        '(a b c))
      
      (test-check (string-append "append-4-" name)
        (append '(a b c) '(d e))
        '(a b c d e))
      
      )))


(define appendo-tests
  (lambda (appendo name)
    (let ()

      (test-check (string-append "appendo-10-a-" name)
        (run 1 (q) (appendo '() '(d e) q))
        '((d e)))

      (test-check (string-append "appendo-12-a-" name)
        (run 1 (q) (appendo '(a) '() q))
        '((a)))

      (test-check (string-append "appendo-13-a-" name)
        (run 1 (q) (appendo '(a b) '() q))
        '((a b)))
            
      (test-check (string-append "appendo-11-a-" name)
        (run 1 (q) (appendo '(a b c) '() q))
        '((a b c)))

      (test-check (string-append "appendo-1-a-" name)
        (run 1 (q) (appendo '(a b c) '(d e) q))
        '((a b c d e)))

      (test-check (string-append "appendo-3-a-" name)
        (run 1 (q) (appendo '(a b c) q '(a b c d e)))
        '((d e)))
      
      (test-check (string-append "appendo-10-b-" name)
        (run* (q) (appendo '() '(d e) q))
        '((d e)))

      (test-check (string-append "appendo-11-b-" name)
        (run* (q) (appendo '(a b c) '() q))
        '((a b c)))
     
      (test-check (string-append "appendo-1-b-" name)
        (run* (q) (appendo '(a b c) '(d e) q))
        '((a b c d e)))

      (test-check (string-append "appendo-3-b-" name)
        (run* (q) (appendo '(a b c) q '(a b c d e)))
        '((d e)))

      (test-check (string-append "appendo-5-" name)
        (run* (q)
          (fresh (l s)
            (appendo '(b) s '(a b c d e))
            (== `(,l ,s) q)))
        '())

      (test-check (string-append "appendo-7-" name)
        (run* (q)
          (fresh (l s rest)
            (appendo '(b) s `(a b c d e  . ,rest))
            (== `(,l ,s) q)))
        '())

      (test-check (string-append "appendo-2-a-" name)
        (run 1 (q) (appendo q '(d e) '(a b c d e)))
        '((a b c)))
      
      (test-check (string-append "appendo-4-a-" name)
        (run 6 (q)
          (fresh (l s)
            (appendo l s '(a b c d e))
            (== `(,l ,s) q)))
        '((() (a b c d e))
          ((a) (b c d e))
          ((a b) (c d e))
          ((a b c) (d e))
          ((a b c d) (e))
          ((a b c d e) ())))

      (test-check (string-append "appendo-8-" name)
        (run 5 (q)
          (fresh (l s rest)
            (appendo l '(z) `(a b c d e  . ,rest))
            (== `(,l ,s) q)))
        '(((a b c d e) _.0)
          ((a b c d e _.0) _.1)
          ((a b c d e _.0 _.1) _.2)
          ((a b c d e _.0 _.1 _.2) _.3)
          ((a b c d e _.0 _.1 _.2 _.3) _.4)))
      
      (test-check (string-append "appendo-2-b-" name)
        (run* (q) (appendo q '(d e) '(a b c d e)))
        '((a b c)))

      (test-check (string-append "appendo-6-" name)
        (run* (q)
          (fresh (l s)
            (appendo l '(z) '(a b c d e))
            (== `(,l ,s) q)))
        '())      
      
      (test-check (string-append "appendo-9-" name)
        (run* (q)
          (fresh (l s more rest)
            (appendo `(b . ,more) s `(a b c d e  . ,rest))
            (== `(,l ,s) q)))
        '())

      (test-check (string-append "appendo-4-b-" name)
        (run* (q)
          (fresh (l s)
            (appendo l s '(a b c d e))
            (== `(,l ,s) q)))
        '((() (a b c d e))
          ((a) (b c d e))
          ((a b) (c d e))
          ((a b c) (d e))
          ((a b c d) (e))
          ((a b c d e) ())))
           
      )))


(let ()

  (define append
    (lambda (l s)
      (pmatch l
        [() s]
        [(,a . ,d) `(,a . ,(append d s))])))  

  (printf "testing append\n")

  (append-tests append "vanilla-append")
  
  )

(let ()

  (define appendo
    (lambda (l s out)
      (conde
        [(== '() l) (== out s)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (== `(,a . ,res) out)
           (appendo d s res))])))

  (printf "testing appendo\n")
  
  (appendo-tests appendo "vanilla-appendo")
    
  )


;; CPS it!!!!
(let ()

  (define appendo-cps
    (lambda (l s out k)
      (conde
        [(== '() l)
         (k s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)

           ;; trick
           (k `(,a . ,res) out)
           
           (appendo-cps d s res (lambda (v out^)
                                  (fresh ()

                                    (== v res)
                                    (== v out^)
                                    
                                    (k `(,a . ,res) out)))))])))

  (define appendo
    (lambda (l s out)
      (appendo-cps l s out (lambda (v out^) (== out^ v)))))
  
  (printf "testing CPSed appendo\n")
  
  (appendo-tests appendo "appendo-cps")
    
  )

;; CPS it, right way???
(let ()

  (define appendo-cps
    (lambda (l s k)
      (conde
        [(== '() l)
         (k s)]
        [(fresh (a d res)
           (== `(,a . ,d) l)

           ;; trick (still works!!)
           (k `(,a . ,res))
           
           (appendo-cps d s (lambda (v)
                              (fresh ()

                                (== res v)

                                (k `(,a . ,v))
                                ))))])))

  (define appendo
    (lambda (l s out)
      (appendo-cps l s (lambda (v) (== out v)))))
  
  (printf "testing CPSed appendo, correct approach???\n")
  
  (appendo-tests appendo "appendo-cps-correct?")
    
  )
