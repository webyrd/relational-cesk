(load "pmatch.scm")
(load "test-check.scm")

;;; Important: lists contain locations, not values.  Values are
;;; substituted for the addresses at the end of eval-exp.  Since
;;; locations are represented as numbers, this means numbers cannot
;;; appear as values with a list.  It is probably possible to get
;;; around this restriction using tagging.  Since this is sufficient
;;; for implementing quines, I'm not going to worry about this
;;; limitation right now.

(define answer cons)

(define new-loc length)

(define lookup
  (lambda (env s x)
    (let ((loc (apply-env env x)))
      (apply-s s loc))))

(define apply-env
  (lambda (env x)
    (cond
      ((assv x env) => cdr)
      (else (errorf 'apply-env "unbound variable ~s" x)))))

(define apply-s
  (lambda (s loc)
    (cond
      ((assv loc s) => cdr)
      (else (errorf 'apply-s "unbound location ~s" loc)))))

(define ext-env
  (lambda (x loc env)
    `((,x . ,loc) . ,env)))

(define ext-s
  (lambda (loc val s)
    `((,loc . ,val) . ,s)))

(define empty-env '())

(define empty-s '())


(define not-in-env
  (lambda (x env)
    (not (assq x env))))


(define make-proc
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define apply-proc
  (lambda (p a s^ k^)
    (pmatch p
      [(closure ,x ,body ,env)
       (let ((loc (new-loc s^)))
         (let ((env^ (ext-env x loc env)))
           (let ((s^^ (ext-s loc a s^)))
             (eval-exp-aux body env^ s^^ k^))))])))



(define apply-k
  (lambda (k v/s)
    (pmatch k
      [(empty-k) v/s]
      [(throw-k ,v-e ,env^)
       (let ((cc (car v/s))
             (s (cdr v/s)))
         (eval-exp-aux v-e env^ s cc))]
      [(if-k ,c ,a ,env ,k)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (if v
             (eval-exp-aux c env s k)
             (eval-exp-aux a env s k)))]
      [(zero?-k ,k)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (apply-k k (answer (zero? v) s)))]
      [(sub1-k ,k)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (apply-k k (answer (sub1 v) s)))]
      [(subtraction-inner-k ,v1 ,k)
       (let ((v2 (car v/s))
             (s (cdr v/s)))
         (apply-k k (answer (- v1 v2) s)))]
      [(subtraction-outer-k ,e2 ,env ,k)
       (let ((v (car v/s))
             (s (cdr v/s)))
         (eval-exp-aux e2 env s (subtraction-inner-k v k)))]
      [(multiplication-inner-k ,v1 ,k)
       (let ((v2 (car v/s))
             (s^^ (cdr v/s)))
         (apply-k k (answer (* v1 v2) s^^)))]
      [(multiplication-outer-k ,e2 ,env ,k)
       (let ((v1 (car v/s))
             (s^ (cdr v/s)))
         (eval-exp-aux e2 env s^
                   (multiplication-inner-k v1 k)))]
      [(set!-k ,x ,env ,k)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (apply-env env x)))
           (apply-k k (answer (void) (ext-s loc v s^)))))]
      [(begin-inner-k ,k)
       (let ((v2 (car v/s))
             (s^^ (cdr v/s)))
         (apply-k k (answer v2 s^^)))]
      [(begin-outer-k ,rand2 ,env ,k)
       (let ((v1 (car v/s))
             (s^ (cdr v/s)))
         (eval-exp-aux rand2 env s^ (begin-inner-k k)))]
      [(application-inner-k ,p ,k)
       (let ((a (car v/s))
             (s^^ (cdr v/s)))
         (apply-proc p a s^^ k))]
      [(application-outer-k ,rand ,env ,k)
       (let ((p (car v/s))
             (s^ (cdr v/s)))
         (eval-exp-aux rand env s^ (application-inner-k p k)))]
      [(list-aux-inner-k ,loc ,k)
       (let ((loc* (car v/s))
             (s^^ (cdr v/s)))
         (apply-k k (answer (cons loc loc*) s^^)))]
      [(list-aux-outer-k ,e* ,env ,k)
       (let ((v (car v/s))
             (s^ (cdr v/s)))
         (let ((loc (new-loc s^)))
           (let ((s^^ (ext-s loc v s^)))
             (list-aux (cdr e*) env s^^ (list-aux-inner-k loc k)))))]
      [,else (error 'apply-k "unknown continuation type")])))

(define empty-k '(empty-k))

(define if-k
  (lambda (c a env k)
    `(if-k ,c ,a ,env ,k)))

(define zero?-k  
  (lambda (k)
    `(zero?-k ,k)))

(define sub1-k
  (lambda (k)
    `(sub1-k ,k)))

(define subtraction-inner-k
  (lambda (v1 k)
    `(subtraction-inner-k ,v1 ,k)))

(define subtraction-outer-k
  (lambda (e2 env k)
    `(subtraction-outer-k ,e2 ,env ,k)))

(define throw-k
  (lambda (v-e env)
    `(throw-k ,v-e ,env)))

(define multiplication-inner-k
  (lambda (v1 k)
    `(multiplication-inner-k ,v1 ,k)))

(define multiplication-outer-k
  (lambda (e2 env k)
    `(multiplication-outer-k ,e2 ,env ,k)))

(define set!-k
  (lambda (x env k)
    `(set!-k ,x ,env ,k)))

(define begin-inner-k
  (lambda (k)
    `(begin-inner-k ,k)))

(define begin-outer-k
  (lambda (rand2 env k)
    `(begin-outer-k ,rand2 ,env ,k)))

(define application-inner-k
  (lambda (p k)
    `(application-inner-k ,p ,k)))

(define application-outer-k
  (lambda (rand env k)
    `(application-outer-k ,rand ,env ,k)))

(define list-aux-inner-k
  (lambda (loc k)
    `(list-aux-inner-k ,loc ,k)))

(define list-aux-outer-k
  (lambda (e* env k)
    `(list-aux-outer-k ,e* ,env ,k)))




(define eval-exp-aux
  (lambda (exp env s k)
    (pmatch exp
      (,n (guard (number? n))
       (apply-k k (answer n s)))
      (,b (guard (boolean? b))
       (apply-k k (answer b s)))
      (,x (guard (symbol? x))
       (apply-k k (answer (lookup env s x) s)))
      ((quote ,datum) (guard (not-in-env 'quote env))
       (apply-k k (answer datum s)))
      ((if ,t ,c ,a) (guard (not-in-env 'if env))
       (eval-exp-aux t env s (if-k c a env k)))
      ((zero? ,e) (guard (not-in-env 'zero env))
       (eval-exp-aux e env s (zero?-k k)))
      ((sub1 ,e) (guard (not-in-env 'sub1 env))
       (eval-exp-aux e env s (sub1-k k)))
      ((- ,e1 ,e2) (guard (not-in-env '- env))
       (eval-exp-aux e1 env s (subtraction-outer-k e2 env k)))
      ((* ,e1 ,e2) (guard (not-in-env '* env))
       (eval-exp-aux e1 env s (multiplication-outer-k e2 env k)))      
      ((throw ,cc-e ,v-e)
       (eval-exp-aux cc-e env s (throw-k v-e env)))
      ((letcc ,cc ,body)
       (let ((loc (new-loc s)))
         (let ((env^ (ext-env cc loc env)))
           (let ((s^ (ext-s loc k s)))
             (eval-exp-aux body env^ s^ k)))))            
      ((lambda (,x) ,body) (guard (not-in-env 'lambda env))
       (apply-k k (answer (make-proc x body env) s)))
      ((set! ,x ,rhs) (guard (not-in-env 'set! env))
       (eval-exp-aux rhs env s (set!-k x env k)))
      ((begin ,rand1 ,rand2) (guard (not-in-env 'begin env))
       (eval-exp-aux rand1 env s (begin-outer-k rand2 env k)))
      ((list . ,e*) (guard (not-in-env 'list env))
       (list-aux e* env s k))
      ((,rator ,rand)
       (eval-exp-aux rator env s (application-outer-k rand env k))))))

(define list-aux
  (lambda (e* env s k)
    (cond
      [(null? e*) (apply-k k (answer '() s))]         
      [else
       (eval-exp-aux (car e*) env s
                 (list-aux-outer-k e* env k))])))

(define eval-exp
  (lambda (exp env s k)
    (pmatch (eval-exp-aux exp env s k)
      [(,v . ,s^)
       (walk*-v v s^)])))

(define walk*-v
  (lambda (v s)
    (pmatch v
      [,x (guard (symbol? x)) x] ; quoted symbol
      [,b (guard (boolean? b)) b]
      [,n (guard (number? n)) n]      
      [() '()] ; empty list (created with either quote or list--doesn't matter)
      [(,a . ,d) (guard (and (not (number? a)) (not (eq? 'closure a)))) ; quoted list (case 1) [can't overlap with a list of nums]
       `(,a . ,d)]
      [((,aa . ,ad) . ,d) ; quoted list (case 2) [can't overlap with a list of nums]
       `((,aa . ,ad) . ,d)]
      [(closure ,x ,body ,env)
;;; arguably I should walk* the body as well, although this could cause its own problems.
;;; although if procedures are opaque, the user really has no right to look inside
       `(closure ,x ,body ,env)]
      [(,addr . ,addr*) (guard (number? addr)) ; non-empty list
       (map-lookup-address `(,addr . ,addr*) s)])))

(define map-lookup-address
  (lambda (addr* s)
    (pmatch addr*
      [() '()]
      [(,addr . ,addr-res) (guard (number? addr))
       (let ((t (apply-s s addr)))
         (let ((v (walk*-v t s)))
           (cons v (map-lookup-address addr-res s))))])))


(test "lookup"
  (let ((env (ext-env 'a (new-loc empty-s) empty-env))
        (s (ext-s (new-loc empty-s) 7 empty-s)))
    (lookup env s 'a))
  7)

(test "lookup-2"
  (let ((env (ext-env 'a (new-loc empty-s) empty-env))
        (s (ext-s (new-loc empty-s) 'foo empty-s)))
    (lookup env s 'a))
  'foo)

(test "cesk-number"
  (eval-exp '5 empty-env empty-s empty-k)
  5)

(test "cesk-boolean"
  (eval-exp '#t empty-env empty-s empty-k)
  #t)

(test "cesk-variable"
  (eval-exp 'a
            (ext-env 'a (new-loc empty-s) empty-env)
            (ext-s (new-loc empty-s) 7 empty-s)
            empty-k)
  7)

(test "cesk-variable-2"
  (eval-exp 'a
            (ext-env 'a (new-loc empty-s) empty-env)
            (ext-s (new-loc empty-s) 'foo empty-s)
            empty-k)
  'foo)
 
(test "cesk-identity"
  (eval-exp '((lambda (x) x) 5)
            empty-env
            empty-s
            empty-k)
  5)

(test "cesk-identity-2"
  (eval-exp '((lambda (x) x) (quote foo))
            empty-env
            empty-s
            empty-k)
  'foo)

(test "letcc/throw-0"
  (eval-exp '(letcc k k)
            empty-env
            empty-s
            empty-k)
  empty-k)

(test "letcc/throw-0b"
  (eval-exp '(letcc k 1)
            empty-env
            empty-s
            empty-k)
  '1)

(test "letcc/throw-0c"
  (eval-exp '(letcc k (throw k 1))
            empty-env
            empty-s
            empty-k)
  '1)

(test "letcc/throw-1"
  (eval-exp '(letcc k (* 5 (throw k (* 2 6))))
            empty-env
            empty-s
            empty-k)
  '12)

(test "letcc/throw-2"
  (eval-exp '(letcc k
               ((quote 5)
                (throw k (quote 7))))
            empty-env
            empty-s
            empty-k)
  '7)

(test "cesk-set!"
  (eval-exp '((lambda (x) (begin (set! x 5) x)) 6)
            empty-env
            empty-s
            empty-k)
  5)

(test "cesk-quote"
  (eval-exp '(quote (lambda (x) 5))
            empty-env
            empty-s
            empty-k)
  '(lambda (x) 5))

(test "cesk-quote-2"
  (eval-exp '(quote (lambda (x) x))
            empty-env
            empty-s
            empty-k)
  '(lambda (x) x))

(test "cesk-zero?-1"
  (eval-exp '(zero? ((lambda (x) x) 0))
            empty-env
            empty-s
            empty-k)
  '#t)

(test "cesk-zero?-2"
  (eval-exp '(zero? ((lambda (x) x) 1))
            empty-env
            empty-s
            empty-k)
  '#f)

(test "cesk-subtraction"
  (eval-exp '(- ((lambda (x) x) 7) ((lambda (x) x) 4))
            empty-env
            empty-s
            empty-k)
  '3)

(test "cesk-multiplication"
  (eval-exp '(* ((lambda (x) x) 7) ((lambda (x) x) 4))
            empty-env
            empty-s
            empty-k)
  '28)

(test "cesk-if-1"
  (eval-exp '(if (zero? (- 7 4)) ((lambda (x) x) (list (quote foo) (quote bar))) ((lambda (x) x) (list #f #t)))
            empty-env
            empty-s
            empty-k)
  '(#f #t))

(test "cesk-if-2"
  (eval-exp '(if (zero? (- 6 (* 2 3))) ((lambda (x) x) (list (quote foo) (quote bar))) ((lambda (x) x) (list #f #t)))
            empty-env
            empty-s
            empty-k)
  '(foo bar))

(define fact-five
  '((lambda (f)
      ((f f) 5))
    (lambda (f)
      (lambda (n)
        (if (zero? n)
            1
            (* n ((f f) (sub1 n))))))))

(test "cesk-fact-5"
  (eval-exp fact-five
            empty-env
            empty-s
            empty-k)
  120)

(test "cesk-list-0"
  (eval-exp '(list)
            empty-env
            empty-s
            empty-k)
  '())

(test "cesk-list-1"
  (eval-exp '(list 5)
            empty-env
            empty-s
            empty-k)
  '(5))

(test "cesk-list-2"
  (eval-exp '(list 5 6)
            empty-env
            empty-s
            empty-k)
  '(5 6))

(test "cesk-list-3"
  (eval-exp '(list (zero? (- 6 (* 2 3))) ((lambda (x) x) (list (quote foo) (quote bar))) ((lambda (x) x) (list #f #t)))
            empty-env
            empty-s
            empty-k)
  '(#t (foo bar) (#f #t)))

(test "cesk-list-1a"
  (eval-exp '(list (quote foo))
            empty-env
            empty-s
            empty-k)
  '(foo))

(test "cesk-list-2a"
  (eval-exp '(list (quote foo) (quote bar))
            empty-env
            empty-s
            empty-k)
  '(foo bar))

(test "cesk-list-3a"
  (eval-exp '(list (quote baz)
                   ((lambda (x) x) (list (quote foo) (quote bar)))
                   ((lambda (x) x) (list (quote quux))))
            empty-env
            empty-s
            empty-k)
  '(baz (foo bar) (quux)))


(test "cesk-shadowing"
  (eval-exp '((lambda (sub1) (sub1 3)) (lambda (n) (* n n)))
            empty-env
            empty-s
            empty-k)
  9)

(test "cesk-shadowing-2"
  (eval-exp '((lambda (x)
                ((lambda (quote)
                   (quote x))
                 (lambda (y) (list y y y))))
              (quote bar))
            empty-env
            empty-s
            empty-k)
  '(bar bar bar))

(define quinec 
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

(test "cesk-quinec"
  (eval-exp quinec
            empty-env
            empty-s
            empty-k)
  quinec)
