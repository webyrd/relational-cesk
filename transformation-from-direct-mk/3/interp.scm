;;;  update lookupo, to recapture quine generation

(load "mk.scm")

;;; helpers

;;; improved lookupo

(define lookupo
  (lambda (x env store t)
    (fresh (addr)
      (symbolo x)
      (numbero addr)
      (lookup-env-auxo x env store addr)
      (lookup-store-auxo addr store t))))

(define lookup-env-auxo
  (lambda (x env store t)
    (fresh (y y* addr-e addr-e* addr-s addr-s* v-s v-s*)      
      (== `((,y . ,y*) (,addr-e . ,addr-e*)) env)
      (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
      (symbolo x)
      (symbolo y)
      (numbero t)
      (numbero addr-e)
      (numbero addr-s)
      (conde
        ((== y x) (== addr-e t))
        ((=/= y x)
         (lookup-env-auxo x `(,y* ,addr-e*) `(,addr-s* ,v-s*) t))))))

(define lookup-store-auxo
  (lambda (addr store t)
    (fresh (addr-s addr-s* v-s v-s*)
      (== `((,addr-s . ,addr-s*) (,v-s . ,v-s*)) store)
      (numbero addr)
      (numbero addr-s)
      (conde
        ((== addr-s addr) (== v-s t))
        ((=/= addr-s addr)
         (lookup-store-auxo addr `(,addr-s* ,v-s*) t))))))

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
