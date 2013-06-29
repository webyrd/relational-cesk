(load "interp.scm")

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

(define quinec 
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

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

(test-check "var-1"
  (run* (q) (eval-expo 'y '((y . (closure z z ()))) q))
  '((closure z z ())))

(test-check "lambda-1"
  (run* (q) (eval-expo '(lambda (x) x) '() q))
  '((closure x x ())))

(test-check "lambda-2"
  (run* (q) (eval-expo '(lambda (x) (lambda (y) (x y))) '() q))
  '((closure x (lambda (y) (x y)) ())))

(test-check "quote-1"
  (run* (q) (eval-expo '(quote (lambda (x) x)) '() q))
  '((lambda (x) x)))

(test-check "app-1"
  (run* (q) (eval-expo '((lambda (x) x) (lambda (y) y)) '() q))
  '((closure y y ())))

(test-check "extend-3"
  (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
  '((closure x x ((quote . (closure y y ()))))))

(test-check "quinec"
  (run* (q) (eval-expo quinec '() q))
  '(((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))))

(test-check "quinec-backwards-1"
  (run 5 (q) (eval-expo q '() quinec))
  '('((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))
    (list '(lambda (x) (list x (list 'quote x))) ''(lambda (x) (list x (list 'quote x))))
    (((lambda (_.0) '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))) '_.1) (=/= ((_.0 quote))) (sym _.0) (absento (closure _.1)))
    (((lambda (_.0) _.0) '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))) (sym _.0))
    (((lambda (_.0) '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))) (list)) (=/= ((_.0 quote))) (sym _.0))))

(test-check "quinec-backwards-2"
  (run 1 (q)
    (eval-expo q '() quinec)
    (== quinec q))
  '(((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))))

(test-check "intro-2"
;;; appears to diverge, due to lookupo  
  (equal? (replace* '((_.0 . x)) (car (car (run 1 (q) (eval-expo q '() q))))) quinec)
  #t
  )
