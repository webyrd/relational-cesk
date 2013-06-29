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


;;;

(test-check "improved-lookupo-0"
  (run 1 (q) (lookupo 'x '() '() q))
  '())

(test-check "improved-lookupo-1"
  (run 1 (q) (lookupo 'x '((w . 0) (x . 1) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) q))
  '(bar))

(test-check "improved-lookupo-2"
  (run* (q) (lookupo 'x '((w . 0) (x . 1) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) q))
  '(bar))

(test-check "improved-lookupo-6"
  (run 1 (q) (lookupo q '((w . 0) (x . 1) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) 'foo))
  '(w))

(test-check "improved-lookupo-7"
  (run 2 (q) (lookupo q '((w . 0) (x . 1) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) 'foo))
  '(w))

(test-check "improved-lookupo-8"
  (run 1 (q) (lookupo q '((w . 0) (x . 1) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) 'quux))
  '())

(test-check "improved-lookupo-9"
  (run 1 (q) (lookupo 'x '((w . 0) (y . 2)) '((0 . foo) (1 . bar) (2 . baz)) q))
  '())

(test-check "improved-lookupo-10"
  (run 1 (q) (lookupo 'x '((w . 0) (x . 1) (y . 2)) '((0 . foo) (2 . baz)) q))
  '())

(test-check "improved-lookupo-12"
  (run 1 (q) (lookupo 'x '((w . 0) (x . 1) (y . 2)) `((1 . foo) . ,q) 'baz))
  '())

;; Diverges!!
;;
;; (test-check "improved-lookupo-13"
;; ;;; this test-check diverges using naive lookupo
;;   (run 1 (q) (lookupo 'x `((w . 0) . ,q) '((1 . foo) (2 . bar)) 'baz))
;;   '())

;; Diverges!!
;;
;; (test-check "improved-lookupo-13a"
;;   (run* (q) (lookupo 'x `((w . 0) . ,q) '((1 . foo) (2 . bar)) 'bar))
;;   '(((x . 2) . _.0)))

(test-check "improved-lookupo-14"
  (run 1 (q)
    (fresh (rest-e rest-s)
      (lookupo 'w `((w . 0) . ,rest-e) `((0 . foo) . ,rest-s) 'baz)
      (== `(,rest-e ,rest-s) q)))
  '())

;;;



(test-check "intro-2"
;;; appears to diverge, due to lookupo
  (run 1 (q) (eval-expo q '() '() q))
  '???
  )
