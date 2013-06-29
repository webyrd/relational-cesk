;;; CPS

(load "mk.scm")
(load "pmatch.scm")

(define append 'u-dun-goofed) ; just to keep ourselves safe from accidentally using built-in append

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

;;;;;;;

(let ()
  
  (define append
    (lambda (l s)
      (pmatch l
        [() s]
        [(,a . ,d) `(,a . ,(append d s))])))
  
  (append-tests append "vanilla-append")

  )


(let ()

  (define appendo
    (lambda (l s out)
      (conde
        [(== '() l)
         (== s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (== `(,a . ,res) out)
;;; appendo must come last, or some tests will diverge           
           (appendo d s res))])))

  (appendo-tests appendo "vanilla-appendo")
  
  )


;;;;;;;

(let ()

  (define append-anf
    (lambda (l s)
      (pmatch l
        [() s]
        [(,a . ,d)
         (let ((res (append-anf d s)))
           `(,a . ,res))])))

  (append-tests append-anf "append-anf")
  
  )


(let ()

;;; diverges!!! (since the recursive call isn't last)  

  (define append-anfo
    (lambda (l s out)
      (conde
        [(== '() l) (== s out)]
        [(fresh (a d)
           (== `(,a . ,d) l)
           (fresh (res)
             (append-anfo d s res)
             (== `(,a . ,res) out)))])))

;  (appendo-tests append-anfo "append-anfo")
  'dummy-exp
  
  )



;;;;;

; Higher-order k

(let ()

  (define append-cps
    (lambda (l s k)
      (pmatch l
        [() (k s)]
        [(,a . ,d)
         (append-cps d s (lambda (res)
                           (k `(,a . ,res))))])))
  (define append
    (lambda (l s)
      (append-cps l s (lambda (v) v))))  

  (append-tests append "append-cps")
  
  )


(let ()

;;; diverges!!
  
  (define append-cpso
;;; are the wires broken in this version?  presumably, since out is never used until the last step
;;; try reconnecting the wires
    (lambda (l s k out)
      (conde
        [(== '() l) (k s out)]
        [(fresh (a d)
           (== `(,a . ,d) l)
           (append-cpso d s (lambda (res out^) ; all continuations take an out^ argument
                              (k `(,a . ,res) out^)) out))])))

  (define appendo
    (lambda (l s out)
      (append-cpso l s (lambda (v out^) (== v out^)) out)))  

;  (appendo-tests appendo "append-cpso")
  'dummy-exp
  
  )



;; move to 1st-order rep of k, to ensure all arguments make sense while being fresh logic variables

; RI

(let ()

;; diverges!!
  
  (define apply-ko
    (lambda (k v out^)
      (k v out^)))

  (define empty-k
    (lambda ()
      (lambda (v out^)
        (== v out^))))

  (define append-k
    (lambda (a k)
      (lambda (v out^)
        (apply-ko k `(,a . ,v) out^))))

  (define append-cpso
    (lambda (l s k out)
      (conde
        [(== '() l) (apply-ko k s out)]
        [(fresh (a d)
           (== `(,a . ,d) l)
           (append-cpso d s (append-k a k) out))])))

  (define appendo
    (lambda (l s out)
      (append-cpso l s (empty-k) out)))

;  (appendo-tests appendo "append-cpso-ri")
  'dummy-exp
  
  )


; 1st order

(let ()

;; diverges!!
  
  (define apply-ko
    (lambda (k^ v out^)
      (conde
        [(== '(empty-k) k^) (== v out^)]
        [(fresh (a k)
           (== `(append-k ,a ,k) k^)
           (apply-ko k `(,a . ,v) out^))])))

  (define empty-k
    (lambda ()
      '(empty-k)))

  (define append-k
    (lambda (a k)
      `(append-k ,a ,k)))

  (define append-cpso
    (lambda (l s k out)
      (conde
        [(== '() l) (apply-ko k s out)]
        [(fresh (a d)
           (== `(,a . ,d) l)
           (append-cpso d s (append-k a k) out))])))

  (define appendo
    (lambda (l s out)
      (append-cpso l s (empty-k) out)))

;  (appendo-tests appendo "append-cpso-1st-order")
  'dummy-exp
  
  )


;;; h-o, CPSing appendo      continuation goal ko takes a value and an out^

(let ()

;; diverges!!
  
  (define appendo-cps
    (lambda (l s out ko)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (appendo-cps d s res (lambda (v out^)
                                  (fresh ()
                                    (== v res) ; this association is necessary to get the correct answer!!!
                                    (ko `(,a . ,res) out)))))])))
  
  (define appendo
    (lambda (l s out)
      (appendo-cps l s out (lambda (v out^) (== out^ v)))))

;  (appendo-tests appendo "appendo-cps-h-o")
  'dummy-exp
  
  )



;;;;;;  CPS the ANF version of append

(let ()

  (define append-anf-cps
    (lambda (l s k)
      (pmatch l
        [() (k s)]
        [(,a . ,d)
         (append-anf-cps d s (lambda (v)
                               (let ((res v))
                                 (k `(,a . ,res)))))])))

  (define append
    (lambda (l s)
      (append-anf-cps l s (lambda (v) v))))

  (append-tests append "append-anf-cps")
  
  )

; which simplifies to...

(let ()

  (define append-anf-cps
    (lambda (l s k)
      (pmatch l
        [() (k s)]
        [(,a . ,d)
         (append-anf-cps d s (lambda (v)
                               (k `(,a . ,v))))])))
  
  (define append
    (lambda (l s)
      (append-anf-cps l s (lambda (v) v))))

  (append-tests append "append-anf-cps-simplified")
  
  )


;; mk version (h-o):

(let ()

  ;; diverges!!

  (define append-anf-cpso
    (lambda (l s ko out)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d)
           (== `(,a . ,d) l)
           (append-anf-cpso d s (lambda (v out^)
                                  (ko `(,a . ,v) out^))
                            out))])))

  (define appendo
    (lambda (l s out)
      (append-anf-cpso l s (lambda (v out^) (== out^ v)) out)))

;  (appendo-tests appendo "append-anf-cpso-h-o")
  'dummy-exp
  
  )




;; RI

(define apply-ko
  (lambda (k v out^)
    (k v out^)))

(define empty-k
  (lambda ()
    (lambda (v out^)
      (== out^ v))))

(define append-k
  (lambda (a k^)
    (lambda (v out^)
      (apply-ko k^ `(,a . ,v) out^))))

(define append-anf-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (apply-ko ko s out)]
      [(== `(,a . ,d) l)
       (append-anf-cpso d s (append-k a k) out)])))

(define append-anfo
  (lambda (l s out)
    (append-anf-cpso l s (empty-k) out)))

;; 1st order

(define apply-ko
  (lambda (k v out^)
    (conde
      [(== '(empty-k) k)
       (== out^ v)]
      [(fresh (a k^)
         (== `(append-k ,a ,k^) k)
         (apply-ko k^ `(,a . ,v) out^))])))

(define empty-k
  (lambda ()
    '(empty-k)))

(define append-k
  (lambda (a k^)
    `(append-k ,a ,k^)))

(define append-anf-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (apply-ko ko s out)]
      [(== `(,a . ,d) l)
       (append-anf-cpso d s (append-k a) out)])))

(define append-anfo
  (lambda (l s out)
    (append-anf-cpso l s (empty-k) out)))




;;; CPS original (unnested) mk code

;; start
(define appendo
  (lambda (l s out)
    (conde
      [(== '() l)
       (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (appendo d s res)
         (== `(,a . ,res) out))])))

(let ()

  ;; diverges!!
  
  (define appendo-cpso
    (lambda (l s ko out)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (appendo-cpso d s (lambda (v out^)
                               (fresh ()
;;;;; Epic WATness!
                                 (== res v) ;; this unifcation appears necessary to get the correct answer

                                 (== out^ res) ; WAT!!!!!

                                 (== v out^) ;; double WAT!!!

                                 (fresh (out-a out-d) ; triple WAT!!!
                                   (== `(,out-a . ,out-d) out)
                                   (== out-d out^))
;;;;;;                             
                                 (ko `(,a . ,res) out)))
                         res))])))

  (define appendo
    (lambda (l s out)
      (appendo-cpso l s (lambda (v out^) (== out^ v)) out)))

;  (appendo-tests appendo "appendo-cpso-h-o")
  'dummy-exp

  )


;; put appendo at the end

;;; *** by reordering goals, we can affect which continuation we are
;;; passing along, and whether the recursive call is in tail position.
;;; We don't seem to have this flexibility if we CPS in Scheme first,
;;; and then translate to mk.  So if we translate to mk first, reorder
;;; goals like we normally do to get good divergence behavior, then
;;; CPS, we retain the divergence behavior.  So in this case it seems
;;; we don't need to reconnect the wires.  So ultimately the problem
;;; with CPSing in Scheme, then translating to mk, is that the goal
;;; ordering is fixed in the wrong order (and I don't see a way around
;;; this.)

;; start
(define appendo
  (lambda (l s out)
    (conde
      [(== '() l)
       (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendo d s res))])))

(let ()
  
  (define appendo-cpso
    (lambda (l s ko out)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (== `(,a . ,res) out)
           (appendo-cpso d s ko res))])))

  (define appendo
    (lambda (l s out)
      (appendo-cpso l s (lambda (v out^) (== out^ v)) out)))

  (appendo-tests appendo "appendo-cpso-recur-at-end-h-o")
  
  )

;; *** TODO
;; RI

(let ()

  (define apply-ko
    (lambda ()))
  
  (define appendo-cpso
    (lambda (l s ko out)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d res)
           (== `(,a . ,d) l)
           (== `(,a . ,res) out)
           (appendo-cpso d s ko res))])))

  (define appendo
    (lambda (l s out)
      (appendo-cpso l s (lambda (v out^) (== out^ v)) out)))

  (appendo-tests appendo "appendo-cpso-recur-at-end-ri")
  
  )

;; *** TODO
;; 1st order


;; *** TODO
;; try leaving k empty in call to 1st order rep.  What is the divergence behavior like?





;;; put appendo first

;; start
(define appendo
  (lambda (l s out)
    (conde
      [(== '() l)
       (== s out)]
      [(fresh (a d res)
         (appendo d s res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out))])))

(let ()

  (define appendo-cpso
    (lambda (l s ko out)
      (conde
        [(== '() l) (ko s out)]
        [(fresh (a d res)
           (appendo-cpso d s (lambda (v out^)
                               (fresh ()

                                 (== v res) ; our old friend  (v represent the 'out' argument from the direct-style appendo call)

                                 
                                 (== `(,a . ,d) l) ; what happens if I swap the order of these last two goals?
                                                   ; Bad things wrt divergence, presumably
                                 (ko `(,a . ,res) out)))
                         res))])))

  (define appendo
    (lambda (l s out)
      (appendo-cpso l s (lambda (v out^) (== out^ v)) out)))
  
  (appendo-tests appendo "appendo-cpso-recur-first-h-o")
  
  )
