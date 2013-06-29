;;;  add store argument to eval-expo, which now returns (value
;;;  . store) pairs as answers; update lookupo to use the store as
;;;  well as the env, and to use symbolo and numbero constraints


(load "mk.scm")

;;; helpers

;;; updated lookupo

;;; possible intermediate step
;;
;; (define lookupo
;;   (lambda (x env store t)
;;     (fresh (addr)
;;       (symbolo x)
;;       (numbero addr)
;;       (lookup-auxo x env addr)
;;       (lookup-auxo addr store t))))

;; (define lookup-auxo
;;   (lambda (x alist t)
;;     (fresh (y v rest)
;;       (== `((,y . ,v) . ,rest) alist)
;;       (conde
;;         ((== y x) (== v t))
;;         ((=/= y x) (lookup-auxo x rest t))))))

(define lookupo
  (lambda (x env store t)
    (fresh (addr)
      (symbolo x)
      (numbero addr)
      (lookup-env-auxo x env addr)
      (lookup-store-auxo addr store t))))

(define lookup-env-auxo
  (lambda (x env addr)
    (fresh (y a rest)
      (== `((,y . ,a) . ,rest) env)
      (symbolo x)
      (symbolo y)
      (numbero addr)
      (conde
        ((== y x) (== a addr))
        ((=/= y x) (lookup-env-auxo x rest addr))))))

(define lookup-store-auxo
  (lambda (addr store t)
    (fresh (a v rest)
      (== `((,a . ,v) . ,rest) store)
      (numbero addr)
      (numbero a)
      (conde
        ((== a addr) (== v t))
        ((=/= a addr) (lookup-store-auxo addr rest t))))))

;;;

(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))

(define proper-listo
  (lambda (exp env store val/store)
    (conde
      ((== '() exp)
       (== `(() . ,store) val/store))
      ((fresh (a d v-a v-d store-a store-d)
         (== `(,a . ,d) exp)
         (== `((,v-a . ,v-d) . ,store-d) val/store)
         (eval-expo a env store `(,v-a . ,store-a))
         (proper-listo d env store-a `(,v-d . ,store-d)))))))

;;; evaluator

(define eval-expo
  (lambda (exp env store val/store)
    (conde
      ((fresh (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== `(,v . ,store) val/store)))
      ((fresh (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env store val/store)))
      ((symbolo exp)
       (fresh (val)
         (== `(,val . ,store) val/store)
         (lookupo exp env store val)))
      ((fresh (rator rand x body env^ arg addr store-rator store-rand)
         (== `(,rator ,rand) exp)
         (eval-expo rator env store `((closure ,x ,body ,env^) . ,store-rator))
         (eval-expo rand env store-rator `(,arg . ,store-rand))
         (numbero addr)
         (absento addr store-rand)
         (eval-expo body `((,x . ,addr) . ,env^) `((,addr . ,arg) . ,store-rand) val/store)))
      ((fresh (x body val)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val)
         (== `(,val . ,store) val/store))))))
