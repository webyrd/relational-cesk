;;; CPS the quines interpreter in miniKanren, without adding a store or changing lookupo
;;; Questions:
;;;
;;; Does CPSing in the miniKanren preserve quine generation?  Hypothesis: yes
;;;
;;; After going to a 1st order rep of continuations, does leaving the
;;; continuation argument fresh preserve quine generation?
;;; Hypothesis: yes, but generation may proceed more slowly.  However,
;;; run^n when there are only n-1 answers will presumably diverge.

(load "mk.scm")


(define eval-expo 'undefined) ; just to be safe

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

(define tests
  (lambda (eval-expo)

    (define replace*
      (lambda (al x)
        (cond
          [(null? x) '()]
          [(symbol? x)
           (cond
             [(assq x al) => cdr]
             [else x])]                         
          [(pair? x)
           (cons (replace* al (car x))
                 (replace* al (cdr x)))]
          [(boolean? x) x]
          [(string? x) x]
          [else (error 'replace* (format "unknown expression type: ~a\n" x))])))

    (define replace-respect-quote*
      (lambda (al x)
        (cond
          [(null? x) '()]
          [(symbol? x)
           (cond
             [(assq x al) => cdr]
             [else x])]                         
          [(pair? x)
           (if (eq? (car x) 'quote)
               x
               (cons (replace-respect-quote* al (car x))
                     (replace-respect-quote* al (cdr x))))]
          [(boolean? x) x]
          [(string? x) x]
          [else (error 'replace-respect-quote* (format "unknown expression type: ~a\n" x))])))

    (define quinec 
      '((lambda (x)
          (list x (list (quote quote) x)))
        (quote
         (lambda (x)
           (list x (list (quote quote) x))))))

    (test-check "var-1"
      (run* (q)
        (eval-expo 'y '((y . (closure z z ()))) q))
      '((closure z z ())))

    (test-check "lambda-1"
      (run* (q)
        (eval-expo '(lambda (x) x) '() q))
      '((closure x x ())))

    (test-check "lambda-2"
      (run* (q)
        (eval-expo '(lambda (x) (lambda (y) (x y))) '() q))
      '((closure x (lambda (y) (x y)) ())))

    (test-check "quote-1"
      (run* (q)
        (eval-expo '(quote (lambda (x) x)) '() q))
      '((lambda (x) x)))

    (test-check "app-0"
      (run 1 (q)
        (eval-expo '((lambda (x) x) (lambda (y) y)) '() q))
      '((closure y y ())))
    
    (test-check "app-1"
      (run* (q)
        (eval-expo '((lambda (x) x) (lambda (y) y)) '() q))
      '((closure y y ())))
    
    (test-check "extend-3"
      (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
      '((closure x x ((quote . (closure y y ()))))))

    (test-check "quinec-1"
      (run 1 (q) (eval-expo quinec '() q))
      '(((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))))

    (test-check "quinec-2"
      (run* (q) (eval-expo quinec '() q))
      '(((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))))

    (test-check "quinec-3"
      (run 1 (q) (eval-expo q '() quinec))
      '('((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))))
    
    (test-check "intro-2"
      (equal? (replace* '((_.0 . x)) (car (car (run 1 (q) (eval-expo q '() q))))) quinec)
      #t)

    (test-check "punchline from intro"
      (equal? (replace* '((_.0 . x)) (caar (run 1 (q) (eval-expo q '() q)))) quinec)
      #t)

    (test-check "quine-gen-1"
      (run 1 (q) (eval-expo q '() q))
      '((((lambda (_.0) (list _.0 (list 'quote _.0)))
          '(lambda (_.0) (list _.0 (list 'quote _.0))))
         (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
         (sym _.0))))

    (test-check "quine-gen-2"
      (replace* '((_.0 . x)) (car (car (run 1 (q) (eval-expo q '() q)))))
      quinec)

    (test-check "quine-gen-3"
      (run 1 (x)
        (fresh (p q)
          (=/= p q)
          (eval-expo p '() q) (eval-expo q '() p)
          (== `(,p ,q) x)))
      '((('((lambda (_.0)
              (list 'quote (list _.0 (list 'quote _.0))))
            '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
          ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
           '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
         (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
         (sym _.0))))

    (test-check "quine-gen-4-a"
      (run 1 (x)
        (fresh (p q r)
          (== '''((lambda (_.0)
                    (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
                  '(lambda (_.0)
                     (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
              p)
          (== ''((lambda (_.0)
                   (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
                 '(lambda (_.0)
                    (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
              q)
          (== '((lambda (_.0)
                  (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
                '(lambda (_.0)
                   (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
              r)          
          (=/= p q) (=/= q r) (=/= r p)
          (eval-expo p '() q) (eval-expo q '() r) (eval-expo r '() p)
          (== `(,p ,q ,r) x)))
      '((''((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))) '((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))) ((lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0))))) '(lambda (_.0) (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))))
    
    (test-check "quine-gen-4-b"
      (run 1 (x)
        (fresh (p q r)
          (=/= p q) (=/= q r) (=/= r p)
          (eval-expo p '() q) (eval-expo q '() r) (eval-expo r '() p)
          (== `(,p ,q ,r) x)))
      '(((''((lambda (_.0)
               (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
             '(lambda (_.0)
                (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
          '((lambda (_.0)
              (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
            '(lambda (_.0)
               (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
          ((lambda (_.0)
             (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
           '(lambda (_.0)
              (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))
         (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
         (sym _.0))))

    (test-check "backwards-1"
      (run 3 (q)
        (eval-expo q '() '(closure y y ())))
      '((lambda (y) y)
        (((lambda (_.0) _.0) (lambda (y) y)) (sym _.0))
        (((lambda (_.0) (_.0 _.0)) (lambda (y) y)) (sym _.0))))

    (test-check "backwards-2"
      (run 10 (q)
        (fresh (exp env val)
          (eval-expo exp env val)
          (== `(,exp ,env ,val) q)))
      '((('_.0 () _.0) (absento (closure _.0)))
        (('_.0 ((_.1 . _.2)) _.0) (=/= ((_.1 quote))) (absento (closure _.0)))
        (('_.0 ((_.1 . _.2) (_.3 . _.4)) _.0) (=/= ((_.1 quote)) ((_.3 quote))) (absento (closure _.0)))
        ((list) () ())
        ((_.0 ((_.0 . _.1) . _.2) _.1) (sym _.0))
        (('_.0 ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6)) _.0) (=/= ((_.1 quote)) ((_.3 quote)) ((_.5 quote))) (absento (closure _.0)))
        (('_.0 ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8)) _.0) (=/= ((_.1 quote)) ((_.3 quote)) ((_.5 quote)) ((_.7 quote))) (absento (closure _.0)))
        (('_.0 ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10)) _.0) (=/= ((_.1 quote)) ((_.3 quote)) ((_.5 quote)) ((_.7 quote)) ((_.9 quote))) (absento (closure _.0)))
        (('_.0 ((_.1 . _.2) (_.3 . _.4) (_.5 . _.6) (_.7 . _.8) (_.9 . _.10) (_.11 . _.12)) _.0) (=/= ((_.1 quote)) ((_.11 quote)) ((_.3 quote)) ((_.5 quote)) ((_.7 quote)) ((_.9 quote))) (absento (closure _.0)))
        ((_.0 ((_.1 . _.2) (_.0 . _.3) . _.4) _.3) (=/= ((_.0 _.1))) (sym _.0))))

    
    ))




;;; original interpreter, from 2012 quines paper

(let ()

  (define lookupo
    (lambda (x env t)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x) (== v t))
          ((=/= y x) (lookupo x rest t))))))

  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  (define proper-listo
    (lambda (exp env val)
      (conde
        ((== '() exp)
         (== '() val))
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)
           (== `(,v-a . ,v-d) val)
           (eval-expo a env v-a)
           (proper-listo d env v-d))))))

  (define eval-expo
    (lambda (exp env val)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (not-in-envo 'quote env)
           (absento 'closure v)
           (== v val)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (not-in-envo 'list env)
           (absento 'closure a*)
           (proper-listo a* env val)))
        ((symbolo exp) (lookupo exp env val))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo rator env `(closure ,x ,body ,env^))
           (eval-expo rand env a)
           (eval-expo body `((,x . ,a) . ,env^) val)))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (== `(closure ,x ,body ,env) val))))))

  (printf "testing direct-style quines interpreter in miniKanren\n")

;  (tests eval-expo)
  
  )



;;; quines interpreter, CPSed in miniKanren, single argument continuations, 1st order continuations

(let ()

  (define apply-ko
    (lambda (k^ v)
      (conde
        [(fresh (val)
           (== `(empty-k ,val) k^)
           (== v val))]
        [(fresh (x body env^ rand env a val k)
           (== `(app-outer-k ,x ,body ,env^ ,rand ,env ,a ,val ,k) k^)

           (== v `(closure ,x ,body ,env^))
           
           (eval-expo-cps rand env a (app-inner-k body x a env^ val k)))]
        [(fresh (body x a env^ val k)
           (== `(app-inner-k ,body ,x ,a ,env^ ,val ,k) k^)

           (== v a)
                                                 
           (eval-expo-cps body `((,x . ,a) . ,env^) val k))]
        [(fresh (v-a d env v-d k)
           (== `(proper-listo-outer-k ,v-a ,d ,env ,v-d ,k) k^)

           (== v v-a)
            
           (proper-listo-cps d env v-d (proper-listo-inner-k v-a v-d k)))]
        [(fresh (v-a v-d k)
           (== `(proper-listo-inner-k ,v-a ,v-d ,k) k^)

           (== v v-d)
           
           (apply-ko k `(,v-a . ,v-d)))])))

  (define empty-k
;; weird that empty-k takes an arg.
;; Maybe these continuations really should take an out argument    
    (lambda (val)
      `(empty-k ,val)))

  (define app-outer-k
    (lambda (x body env^ rand env a val k)
      `(app-outer-k ,x ,body ,env^ ,rand ,env ,a ,val ,k)))

  (define app-inner-k
    (lambda (body x a env^ val k)
      `(app-inner-k ,body ,x ,a ,env^ ,val ,k)))

 (define proper-listo-outer-k
   (lambda (v-a d env v-d k)
     `(proper-listo-outer-k ,v-a ,d ,env ,v-d ,k)))

  (define proper-listo-inner-k
    (lambda (v-a v-d k)
      `(proper-listo-inner-k ,v-a ,v-d ,k)))
  
  (define lookupo-cps
    (lambda (x env t k)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x)
           (apply-ko k v))
          ((=/= y x)
           (lookupo-cps x rest t k))))))

  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  (define proper-listo-cps
    (lambda (exp env val k)
      (conde
        ((== '() exp)
         (apply-ko k '())) 
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)

           (apply-ko k `(,v-a . ,v-d))
           
           (eval-expo-cps a env v-a (proper-listo-outer-k v-a d env v-d k)))))))

  (define eval-expo-cps
    (lambda (exp env val k)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (absento 'closure v)
           (not-in-envo 'quote env)
           (apply-ko k v)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (absento 'closure a*)
           (not-in-envo 'list env)
           (proper-listo-cps a* env val k)))
        ((symbolo exp)
         (lookupo-cps exp env val k))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo-cps rator env `(closure ,x ,body ,env^)
                          (app-outer-k x body env^ rand env a val k))))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (apply-ko k `(closure ,x ,body ,env)))))))

  (define eval-expo
    (lambda (exp env val)
      (eval-expo-cps exp env val (empty-k val))))
  
  (printf "testing interpreter CPSed in miniKanren, experimental 4\n")
  
  (tests eval-expo)
  
  )


;;; quines interpreter, CPSed in miniKanren, single argument continuations, RI wrt continuations

(let ()

  (define apply-ko
    (lambda (k v)
      (k v)))

  (define empty-k
;; weird that empty-k takes an arg.
;; Maybe these continuations really should take an out argument
    (lambda (val)
      (lambda (v) (== v val))))

  (define app-outer-k
    (lambda (x body env^ rand env a val k)
      (lambda (v)
        (fresh ()
                                                            
          (== v `(closure ,x ,body ,env^))
                              
          (eval-expo-cps rand env a
                         (app-inner-k body x a env^ val k))))))

  (define app-inner-k
    (lambda (body x a env^ val k)
      (lambda (v^)
        (fresh ()

          (== v^ a)
                                                 
          (eval-expo-cps body `((,x . ,a) . ,env^) val k)))))

 (define proper-listo-outer-k
   (lambda (v-a d env v-d k)
     (lambda (v)
       (fresh ()

         (== v v-a)
                                        
         (proper-listo-cps d env v-d (proper-listo-inner-k v-a v-d k))))))

  (define proper-listo-inner-k
    (lambda (v-a v-d k)
      (lambda (v^)
        (fresh ()

          (== v^ v-d)

          (apply-ko k `(,v-a . ,v-d))))
      
      ))
  
  (define lookupo-cps
    (lambda (x env t k)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x)
           (apply-ko k v))
          ((=/= y x)
           (lookupo-cps x rest t k))))))

  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))
  
  (define proper-listo-cps
    (lambda (exp env val k)
      (conde
        ((== '() exp)
         (apply-ko k '())) 
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)

           (apply-ko k `(,v-a . ,v-d))
           
           (eval-expo-cps a env v-a (proper-listo-outer-k v-a d env v-d k)))))))

  (define eval-expo-cps
    (lambda (exp env val k)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (absento 'closure v)
           (not-in-envo 'quote env)
           (apply-ko k v)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (absento 'closure a*)
           (not-in-envo 'list env)
           (proper-listo-cps a* env val k)))
        ((symbolo exp)
         (lookupo-cps exp env val k))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo-cps rator env `(closure ,x ,body ,env^)
                          (app-outer-k x body env^ rand env a val k))))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (apply-ko k `(closure ,x ,body ,env)))))))

  (define eval-expo
    (lambda (exp env val)
      (eval-expo-cps exp env val (empty-k val))))

  (printf "testing interpreter CPSed in miniKanren, experimental 3\n")
  
  (tests eval-expo)
  
  )



;;; quines interpreter, CPSed in miniKanren, single argument continuations

(let ()

  ;; ??? Which of these helpers should be treated as serious and
  ;; CPSed?  Exactly what is the defn of serious for a relation?  That
  ;; a run1 call on just that relation might diverge?  I assume that's
  ;; the defn.

  ;; CPSing these helpers is trivial, so long as the recursions come last.
  ;; proper-listo is the only interesting case, since it calls eval-expo-cps
  
  (define lookupo-cps
    (lambda (x env t k)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x)
           (k v)) ; was (k v t)   (this seems suspicious--can I really get rid of the t???)
          ((=/= y x)
           (lookupo-cps x rest t k))))))

  ;; somehwat weird one, since it is a predicate in Scheme,
  ;; and doesn't really have an output (either succeeds or doesn't in
  ;; miniKanren)
  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  
  (define proper-listo-cps
    (lambda (exp env val k)
      (conde
        ((== '() exp)
         (k '())) ; was (k '() val)
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)

           ;; cheat a little (by reconnecting the wires just a tad)
           ;(== `(,v-a . ,v-d) val)  ; (results in a large speedup.
                                    ; Still, the interpreter can
                                    ; generate quines on its own even
                                    ; without this trick)

           ;; seems to work!
           (k `(,v-a . ,v-d)) ; was (k `(,v-a . ,v-d) val)

           
           (eval-expo-cps a env v-a (lambda (v)
                                      (fresh ()

                                        (== v v-a)
                                        
                                        (proper-listo-cps d env v-d (lambda (v^)
                                                                      (fresh ()

                                                                        (== v^ v-d)

                                                                        ;;; really
                                                                        ;;; want
                                                                        ;;; this
                                                                        ;;; unification
                                                                        ;;; to
                                                                        ;;; come
                                                                        ;;; earlier

                                                                        ;; interesting CPSing in miniKanren helps,
                                                                        ;; but doesn't seem to give complete control.
                                                                        ;; reconnecting the wires trick still seems useful.
                                                                        ;; Hmm--can I CPS with this unification happening earlier?
                                                                        ;; How was I able to get away with that in append???
                                                                        (k `(,v-a . ,v-d)))))))))))))



  
  (define eval-expo-cps
    (lambda (exp env val k)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (absento 'closure v)
           (not-in-envo 'quote env)
           (k v)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (absento 'closure a*)
           (not-in-envo 'list env)
           (proper-listo-cps a* env val k)))
        ((symbolo exp)
         (lookupo-cps exp env val k))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo-cps rator env `(closure ,x ,body ,env^)
                          (lambda (v)
                            (fresh ()

                              ;;; when CPSing in mk, out^ argument
                              ;;; appears to always be ignored except
                              ;;; in initial k

                              ;;; also, v must be explicitly unified
                              ;;; with the 'out' from the CPSed call
                              ;;; containing the continuation
                                                            
                              (== v `(closure ,x ,body ,env^))
                              
                              (eval-expo-cps rand env a
                                             (lambda (v^)
                                               (fresh ()

                                                 (== v^ a)
                                                 
                                                 (eval-expo-cps body `((,x . ,a) . ,env^) val k)))))))))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (k `(closure ,x ,body ,env)))))))

  (define eval-expo
    (lambda (exp env val)
      (eval-expo-cps exp env val (lambda (v) (== v val)))))

  (printf "testing interpreter CPSed in miniKanren, experimental 2\n")
  
  (tests eval-expo)
  
  )



;;; quines interpreter, CPSed in miniKanren

(let ()

  ;; ??? Which of these helpers should be treated as serious and
  ;; CPSed?  Exactly what is the defn of serious for a relation?  That
  ;; a run1 call on just that relation might diverge?  I assume that's
  ;; the defn.

  ;; CPSing these helpers is trivial, so long as the recursions come last.
  ;; proper-listo is the only interesting case, since it calls eval-expo-cps
  
  (define lookupo-cps
    (lambda (x env t k)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x)
           (k v t))
          ((=/= y x)
           (lookupo-cps x rest t k))))))

  ;; somehwat weird one, since it is a predicate in Scheme,
  ;; and doesn't really have an output (either succeeds or doesn't in
  ;; miniKanren)
  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  
  (define proper-listo-cps
    (lambda (exp env val k)
      (conde
        ((== '() exp)
         (k '() val))
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)

           ;; cheat a little (by reconnecting the wires just a tad)
           ;(== `(,v-a . ,v-d) val)  ; (results in a large speedup.
                                    ; Still, the interpreter can
                                    ; generate quines on its own even
                                    ; without this trick)

           ;; seems to work!
           (k `(,v-a . ,v-d) val)

           
           (eval-expo-cps a env v-a (lambda (v out^)
                                      (fresh ()

                                        (== v v-a)
                                        
                                        (proper-listo-cps d env v-d (lambda (v^ out^^)
                                                                      (fresh ()

                                                                        (== v^ v-d)

                                                                        ;;; really
                                                                        ;;; want
                                                                        ;;; this
                                                                        ;;; unification
                                                                        ;;; to
                                                                        ;;; come
                                                                        ;;; earlier

                                                                        ;; interesting CPSing in miniKanren helps,
                                                                        ;; but doesn't seem to give complete control.
                                                                        ;; reconnecting the wires trick still seems useful.
                                                                        ;; Hmm--can I CPS with this unification happening earlier?
                                                                        ;; How was I able to get away with that in append???
                                                                        (k `(,v-a . ,v-d) val))))))))))))



  
  (define eval-expo-cps
    (lambda (exp env val k)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (absento 'closure v)
           (not-in-envo 'quote env)
           (k v val)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (absento 'closure a*)
           (not-in-envo 'list env)
           (proper-listo-cps a* env val k)))
        ((symbolo exp)
         (lookupo-cps exp env val k))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo-cps rator env `(closure ,x ,body ,env^)
                          (lambda (v out^)
                            (fresh ()

                              ;;; when CPSing in mk, out^ argument
                              ;;; appears to always be ignored except
                              ;;; in initial k

                              ;;; also, v must be explicitly unified
                              ;;; with the 'out' from the CPSed call
                              ;;; containing the continuation
                                                            
                              (== v `(closure ,x ,body ,env^))
                              
                              (eval-expo-cps rand env a
                                             (lambda (v^ out^^)
                                               (fresh ()

                                                 (== v^ a)
                                                 
                                                 (eval-expo-cps body `((,x . ,a) . ,env^) val k)))))))))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (k `(closure ,x ,body ,env) val))))))

  (define eval-expo
    (lambda (exp env val)
      (eval-expo-cps exp env val (lambda (v out^) (== v out^)))))

  (printf "testing interpreter CPSed in miniKanren, experimental\n")
  
  (tests eval-expo)
  
  )


;;; quines interpreter, CPSed in miniKanren

(let ()

  ;; ??? Which of these helpers should be treated as serious and
  ;; CPSed?  Exactly what is the defn of serious for a relation?  That
  ;; a run1 call on just that relation might diverge?  I assume that's
  ;; the defn.

  ;; CPSing these helpers is trivial, so long as the recursions come last.
  ;; proper-listo is the only interesting case, since it calls eval-expo-cps
  
  (define lookupo-cps
    (lambda (x env t k)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          ((== y x)
           (k v t))
          ((=/= y x)
           (lookupo-cps x rest t k))))))

  ;; somehwat weird one, since it is a predicate in Scheme,
  ;; and doesn't really have an output (either succeeds or doesn't in
  ;; miniKanren)
  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))

  
  (define proper-listo-cps
    (lambda (exp env val k)
      (conde
        ((== '() exp)
         (k '() val))
        ((fresh (a d v-a v-d)
           (== `(,a . ,d) exp)

           ;; cheat a little (by reconnecting the wires just a tad)
;           (== `(,v-a . ,v-d) val)  ; (results in a large speedup.
                                    ; Still, the interpreter can
                                    ; generate quines on its own even
                                    ; without this trick)
           
           (eval-expo-cps a env v-a (lambda (v out^)
                                      (fresh ()

                                        (== v v-a)
                                        
                                        (proper-listo-cps d env v-d (lambda (v^ out^^)
                                                                      (fresh ()

                                                                        (== v^ v-d)

                                                                        ;;; really
                                                                        ;;; want
                                                                        ;;; this
                                                                        ;;; unification
                                                                        ;;; to
                                                                        ;;; come
                                                                        ;;; earlier

                                                                        ;; interesting CPSing in miniKanren helps,
                                                                        ;; but doesn't seem to give complete control.
                                                                        ;; reconnecting the wires trick still seems useful.
                                                                        ;; Hmm--can I CPS with this unification happening earlier?
                                                                        ;; How was I able to get away with that in append???
                                                                        (k `(,v-a . ,v-d) val))))))))))))



  
  (define eval-expo-cps
    (lambda (exp env val k)
      (conde
        ((fresh (v)
           (== `(quote ,v) exp)
           (absento 'closure v)
           (not-in-envo 'quote env)
           (k v val)))
        ((fresh (a*)
           (== `(list . ,a*) exp)
           (absento 'closure a*)
           (not-in-envo 'list env)
           (proper-listo-cps a* env val k)))
        ((symbolo exp)
         (lookupo-cps exp env val k))
        ((fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (eval-expo-cps rator env `(closure ,x ,body ,env^)
                          (lambda (v out^)
                            (fresh ()

                              ;;; when CPSing in mk, out^ argument
                              ;;; appears to always be ignored except
                              ;;; in initial k

                              ;;; also, v must be explicitly unified
                              ;;; with the 'out' from the CPSed call
                              ;;; containing the continuation
                                                            
                              (== v `(closure ,x ,body ,env^))
                              
                              (eval-expo-cps rand env a
                                             (lambda (v^ out^^)
                                               (fresh ()

                                                 (== v^ a)
                                                 
                                                 (eval-expo-cps body `((,x . ,a) . ,env^) val k)))))))))
        ((fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (k `(closure ,x ,body ,env) val))))))

  (define eval-expo
    (lambda (exp env val)
      (eval-expo-cps exp env val (lambda (v out^) (== v out^)))))

  (printf "testing interpreter CPSed in miniKanren\n")
  
  (tests eval-expo)
  
  )


(let ()

  ;; CPSed in Scheme (bottom of file), then converted to mk
  
  (define lookup-cpso
    (lambda (x env k out)
      (fresh (y v rest)
        (== `((,y . ,v) . ,rest) env)
        (conde
          [(== y x) (k v out)]
          [(=/= y x) (lookup-cpso x rest k out)]))))

  (define not-in-envo
    (lambda (x env)
      (conde
        ((== '() env))
        ((fresh (y v rest)
           (== `((,y . ,v) . ,rest) env)
           (=/= y x)
           (not-in-envo x rest))))))
  
  (define proper-list-cpso    
    (lambda (a* env k out)
      (conde
        [(== '() a*)
         (k '() out)]
        [(fresh (e rest)
           (== `(,e . ,rest) a*)

;;; doesn't seem as easy to easily reconnect the wires by just pulling
;;; out a unification with 'out', like we can when we CPS first.
;;; Probably have to do the full derivatives trick.
           
           (eval-exp-cpso e env (lambda (v out^)                                  
                                  (proper-list-cpso rest env (lambda (v^ out^^)
                                                               (k `(,v . ,v^) out^^))
                                                    out^))
                          out))])))
  
  (define eval-exp-cpso
    (lambda (exp env k out)
      (conde
        [(fresh (v)
           (== `(quote ,v) exp)
           (not-in-envo 'quote env)
           (k v out))]
        [(fresh (a*)
           (== `(list . ,a*) exp)
           (not-in-envo 'list env)
           (proper-list-cpso a* env k out))]
        [(symbolo exp)
         (lookup-cpso exp env k out)]
        [(fresh (rator rand)
           (== `(,rator ,rand) exp)
           (eval-exp-cpso rator env
                          (lambda (proc out^)
                            (eval-exp-cpso rand env
                                           (lambda (arg out^^)
                                             (fresh (x body env^)
                                               (== `(closure ,x ,body ,env^) proc)
                                               (eval-exp-cpso body `((,x . ,arg) . ,env^) k out^^)))
                                           out^))
                          out))]
        [(fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (k `(closure ,x ,body ,env) out))])))

  (define eval-expo
    (lambda (exp env val)
      (eval-exp-cpso exp env (lambda (v out^) (== v out^)) val)))

  (printf "testing interpreter CPSed in Scheme, then converted to mk\n")
  
  (tests eval-expo)
  
  )

#!eof

;;; direct style scheme

(define lookup
  (lambda (x env)
    (dmatch env
      (() (error 'lookup "unbound variable"))
      (((,y . ,v) . ,rest) (guard (eq? y x))
       v)
      (((,y . ,v) . ,rest) (guard (not (eq? y x)))
       (lookup x rest)))))

(define not-in-env
  (lambda (x env)
    (dmatch env
      (() #t)
      (((,y . ,v) . ,rest) (guard (eq? y x)) #f)      
      (((,y . ,v) . ,rest) (guard (not (eq? y x)))
       (not-in-env x rest)))))

;;; use a loop instead of 'map', so we can CPS in the next step
(define proper-list
  (lambda (a* env)
    (dmatch a*
      (() '())
      ((,e . ,rest)
       `(,(eval-exp e env) . ,(proper-list rest env))))))

(define eval-exp
  (lambda (exp env)
    (dmatch exp
      ((quote ,v) (guard (not-in-env 'quote env)) v)
      ((list . ,a*) (guard (not-in-env 'list env))

       (proper-list a* env)

       ;;(map (lambda (e) (eval-exp e env)) a*)

       )
      (,x (guard (symbol? x)) (lookup x env))
      ((,rator ,rand)
       (guard (rator? rator env))
       (let ((proc (eval-exp rator env))
             (arg (eval-exp rand env)))
         (dmatch proc
           ((closure ,x ,body ,env)
            (eval-exp body `((,x . ,arg) . ,env))))))
      ((lambda (,x) ,body)
       (guard (symbol? x) (not-in-env 'lambda env))
       `(closure ,x ,body ,env)))))

(define rator?
  (let ((op-names '(lambda quote list)))
    (lambda (x env)
      (not (and (symbol? x)
                (memq x op-names)
                (not-in-env x env))))))

(test-check "extend-1"
  (eval-exp '(lambda (x) x) '())
  '(closure x x ()))

(test-check "extend-2"
  (eval-exp '(quote (closure x x ())) '())
  '(closure x x ()))


;;; CPS in Scheme

(define lookup-cps
  (lambda (x env k)
    (dmatch env
      (() (error 'lookup "unbound variable"))
      (((,y . ,v) . ,rest) (guard (eq? y x))
       (k v))
      (((,y . ,v) . ,rest) (guard (not (eq? y x)))
       (lookup-cps x rest k)))))

(define not-in-env
  (lambda (x env)
    (dmatch env
      (() #t)
      (((,y . ,v) . ,rest) (guard (eq? y x)) #f)      
      (((,y . ,v) . ,rest) (guard (not (eq? y x)))
       (not-in-env x rest)))))

(define proper-list-cps
  (lambda (a* env k)
    (dmatch a*
      (() (k '()))
      ((,e . ,rest)
       (eval-exp-cps e env (lambda (v)
                             (proper-list-cps rest env (lambda (v^)
                                                         (k `(,v . ,v^))))))))))

(define eval-exp-cps
  (lambda (exp env k)
    (dmatch exp
      ((quote ,v) (guard (not-in-env 'quote env))
       (k v))
      ((list . ,a*) (guard (not-in-env 'list env))

       (proper-list-cps a* env k)
       
       ;; (map (lambda (e) (eval-exp-cps e env)) a*)

       )
      (,x (guard (symbol? x))
       (lookup-cps x env k))
      ((,rator ,rand)
       (guard (rator? rator env))
       (eval-exp-cps rator env
                     (lambda (proc)
                       (eval-exp-cps rand env
                                     (lambda (arg)
                                       (dmatch proc
                                         ((closure ,x ,body ,env)
                                          (eval-exp-cps body `((,x . ,arg) . ,env) k))))))))
      ((lambda (,x) ,body)
       (guard (symbol? x) (not-in-env 'lambda env))
       (k `(closure ,x ,body ,env))))))

(define rator?
  (let ((op-names '(lambda quote list)))
    (lambda (x env)
      (not (and (symbol? x)
                (memq x op-names)
                (not-in-env x env))))))
