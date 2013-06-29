;;; add store, with output store as an extra arg (rather than returning a value/store pair)

;;; original direct-style, environment-passing interpreter, with quote
;;; and list, from 2012 Scheme Workshop quines paper.
;;;
;;; with updated mk.scm, which generalizes absento

(load "mk.scm")

;;; helpers

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
  (lambda (exp env store-in val store-out)
    (conde
      ((== '() exp)
       (== '() val)
       (== store-in store-out))
      ((fresh (a d v-a v-d store-1)
         (== `(,a . ,d) exp)
         (== `(,v-a . ,v-d) val)
         (eval-expo a env store-in v-a store-1)
         (proper-listo d env store-1 v-d store-out))))))

;;; evaluator

(define eval-expo
  (lambda (exp env store-in val store-out)
    (conde
      ((fresh (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== v val)
         (== store-out store-in)))
      ((fresh (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env store-in val store-out)))
      ((symbolo exp)
       (== store-out store-in)
       (fresh (addr)
         (lookupo exp env addr)
         (lookupo addr store-in val)))
      ((fresh (rator rand x body env^ arg addr store-1 store-2)
         (== `(,rator ,rand) exp)
         (eval-expo rator env store-in `(closure ,x ,body ,env^) store-1)
         (eval-expo rand env store-1 arg store-2)
         (absento addr store-2)
         (eval-expo body `((,x . ,addr) . ,env^) `((,addr . ,arg) . ,store-2) val store-out)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val)
         (== store-out store-in))))))
