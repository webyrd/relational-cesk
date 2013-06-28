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
  (run* (q) (eval-expo 'y '((y . 5)) '((5 . (closure z z ()))) q))
  '(((closure z z ()) . ((5 . (closure z z ()))))))

(test-check "lambda-1"
  (run* (q) (eval-expo '(lambda (x) x) '() '() q))
  '(((closure x x ()) . ())))

(test-check "lambda-2"
  (run* (q) (eval-expo '(lambda (x) (lambda (y) (x y))) '() '() q))
  '(((closure x (lambda (y) (x y)) ()) . ())))

(test-check "quote-1"
  (run* (q) (eval-expo '(quote (lambda (x) x)) '() '() q))
  '(((lambda (x) x) . ())))

(test-check "app-1"
  (run* (q) (eval-expo '((lambda (x) x) (lambda (y) y)) '() '() q))
  '((((closure y y ()) . ((_.0 . (closure y y ())))) (num _.0))))

(test-check "extend-3"
  (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() '() q))
  '((((closure x x ((quote . _.0))) . ((_.1 . (closure x x ((quote . _.0)))) (_.0 . (closure y y ())))) (=/= ((_.0 _.1))) (num _.0 _.1))))

(test-check "quinec"
  (run* (q) (eval-expo quinec '() '() q))
  '(((((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x)))) . ((_.0 . (lambda (x) (list x (list 'quote x)))))) (num _.0))))

(test-check "intro-2"
;;; appears to diverge, due to lookupo
  (run 1 (q) (eval-expo q '() '() q))
  '???
  )
