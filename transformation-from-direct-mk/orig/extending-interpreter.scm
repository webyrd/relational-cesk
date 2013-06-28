(load "testcheck.scm")
(load "quinec.scm")
(load "appendixC.scm")
(load "appendixD.scm")
(load "interp-helpers.scm")
(load "replacestar.scm")

(define eval-exp
  (lambda (exp env)
    (dmatch exp
      ((quote ,v) (guard (not-in-env 'quote env)) v)
      ((list . ,a*) (guard (not-in-env 'list env))
       (map (lambda (e) (eval-exp e env)) a*))
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

(test-check "extend-3"
  (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
  '((closure x x ((quote . (closure y y ()))))))

;;; footnote from intro
(test-check "intro-2"
  (equal? (replace* '((_.0 . x)) (car (car (run 1 (q) (eval-expo q '() q))))) quinec)
  #t)
