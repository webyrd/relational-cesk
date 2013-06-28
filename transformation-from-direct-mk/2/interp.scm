;;;  add store argument to eval-expo, which now returns (value . store) pairs as answers

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
       (fresh (val addr)
         (== `(,val . ,store) val/store)
         (lookupo exp env addr)
         (lookupo addr store val)))
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
