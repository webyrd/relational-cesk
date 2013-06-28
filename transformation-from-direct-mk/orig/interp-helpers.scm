;;; helpers used in multiple interpreters

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
