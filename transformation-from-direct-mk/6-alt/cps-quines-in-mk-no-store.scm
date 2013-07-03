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

    (test-check "app-1"
      (run* (q)
        (eval-expo '((lambda (x) x) (lambda (y) y)) '() q))
      '((closure y y ())))
    
    (test-check "extend-3"
      (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
      '((closure x x ((quote . (closure y y ()))))))

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

    (test-check "quine-gen-4"
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

  (tests eval-expo)
  
  )
