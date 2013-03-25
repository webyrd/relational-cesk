(load "mk.scm")
(load "quines-lookupo.scm")
(load "test-check.scm")

(define answer cons)

(define not-in-envo
;;; with the old absento, this definition only works if x is a ground symbol
  (lambda (x env)
    (fresh (x*)
      (symbolo x)
      (env->x*o env x*)
      (absento x x*))))

(define not-in-storeo
  (lambda (addr store)
    (fresh (addr*)
      (numbero addr)
      (store->addr*o store addr*)
      (absento addr addr*))))

(define make-proc
  (lambda (x body env)    
    `(closure ,x ,body ,env)))

(define apply-proco
  (lambda (p a s^ k^ out v-out)
    (fresh (x body env addr env^ s^^)
      (== `(closure ,x ,body ,env) p)
      (numbero addr)
      (not-in-storeo addr s^)
      (ext-envo x addr env env^)
      (ext-storeo addr a s^ s^^)
      (eval-exp-auxo body env^ s^^ k^ out v-out) ; v-out
      )))

(define apply-ko
  (lambda (k^ v/s out v-out)
    (conde
      [(fresh (v s)
         (== '(empty-k) k^)
         (== v/s out)
         (== `(,v . ,s) v/s)
         (== v v-out)) ; v-out
       ]
      [(fresh (x env k v s^ addr s^^ v-out-ignore)
         (== `(set!-k ,x ,env ,k) k^)
         (== `(,v . ,s^) v/s)
         (numbero addr)
         (ext-storeo addr v s^ s^^)
         (lookup-env-only-auxo x env addr)
         (apply-ko k (answer 'void s^^) out v-out-ignore)
         )]
      [(fresh (v-e env^ cc s v-out-ignore)
         (== `(throw-k ,v-e ,env^) k^)
         (== `(,cc . ,s) v/s)
         (eval-exp-auxo v-e env^ s cc out v-out-ignore))]      
      [(fresh (p k a s^^ v-out^)
         (== `(application-inner-k ,p ,k ,v-out^) k^)
         (== `(,a . ,s^^) v/s)
         (apply-proco p a s^^ k out v-out^) ; v-out
         )]
      [(fresh (rand env k p s^ v-out^ v-out-ignore)
         (== `(application-outer-k ,rand ,env ,k ,v-out^) k^)
         (== `(,p . ,s^) v/s)

;;; this is actually incorrect!
;;; causes failure too quickly--test  letcc/throw-2c fails if this
;;; code is included.
; this isn't related to v-out, but p had better be a closure
;         (fresh (x body env^)
;           (== `(closure ,x ,body ,env^) p))
;          
         
         (eval-exp-auxo rand env s^ (application-inner-k p k v-out^) out v-out-ignore) ; v-out
         )]
      [(fresh (v k v* s^^ v-out-ignore)
         (== `(list-aux-inner-k ,v ,k) k^)
         (== `(,v* . ,s^^) v/s)
         (== v* v-out) ; v-out
         (apply-ko k (answer (cons v v*) s^^) out v-out-ignore))]
      [(fresh (e* env k v s^ e*-rest ignore v-out-rest)
         (== `(list-aux-outer-k ,e* ,env ,k ,v-out-rest) k^)
         (== `(,v . ,s^) v/s)
         (== `(,ignore . ,e*-rest) e*)
         (list-auxo e*-rest env s^ (list-aux-inner-k v k) out v-out-rest))])))

(define empty-k '(empty-k))

(define throw-k
  (lambda (v-e env)
    `(throw-k ,v-e ,env)))

(define application-inner-k
  (lambda (p k v-out^)
    `(application-inner-k ,p ,k ,v-out^)))

(define application-outer-k
  (lambda (rand env k v-out^)
    `(application-outer-k ,rand ,env ,k ,v-out^)))

(define list-aux-inner-k
  (lambda (v k)
    `(list-aux-inner-k ,v ,k)))

(define list-aux-outer-k
  (lambda (e* env k v-out^)
    `(list-aux-outer-k ,e* ,env ,k ,v-out^)))

(define set!-k
  (lambda (x env k)
    `(set!-k ,x ,env ,k)))

(define eval-exp-auxo
  (lambda (exp env s k out v-out)
    (conde
      [(fresh (datum)
         (== `(quote ,datum) exp)
         (not-in-envo 'quote env)
         (absento 'closure datum)
         (absento 'void datum)
         (== datum v-out) ; v-out
         (apply-ko k (answer datum s) out v-out))]
      [(fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== (make-proc x body env) v-out) ; v-out
         (apply-ko k (answer (make-proc x body env) s) out v-out))]      
      [(fresh (cc body addr env^ s^ v-out-ignore)
         (== `(letcc ,cc ,body) exp)
         (numbero addr)
         (not-in-storeo addr s)
         (ext-envo cc addr env env^)
         (ext-storeo addr k s s^)
         (eval-exp-auxo body env^ s^ k out v-out-ignore))]
      [(fresh (v)
         (symbolo exp)
         (== v v-out) ; v-out
         (lookupo exp env s v)
         (apply-ko k (answer v s) out v-out))]
      [(fresh (x e v-out-ignore)
         (== `(set! ,x ,e) exp)
         (not-in-envo 'set! env)
         (symbolo x)
         ; (== 'void v-out) ; v-out
         (eval-exp-auxo e env s (set!-k x env k) out v-out-ignore))]
      [(fresh (cc-e v-e v-out-ignore)
         (== `(throw ,cc-e ,v-e) exp)
         (eval-exp-auxo cc-e env s (throw-k v-e env) out v-out-ignore))]      
      [(fresh (rator rand v-out-ignore)
         (== `(,rator ,rand) exp)
         (eval-exp-auxo rator env s (application-outer-k rand env k v-out) out v-out-ignore) ; v-out
         )]
      [(fresh (e*)
         (== `(list . ,e*) exp)
         (not-in-envo 'list env)
         (list-auxo e* env s k out v-out) ; v-out
         )])))

(define list-auxo
  (lambda (e* env s k out v-out*)
    (conde
      [(fresh (v-out-ignore)
         (== '() e*)
         (== '() v-out*) ; v-out*
         (apply-ko k (answer '() s) out v-out-ignore))]
      [(fresh (e ignore ignore^ v-out v-out-rest)
         (== `(,e . ,ignore) e*)
         (== `(,v-out . ,v-out-rest) v-out*) ; v-out*
         (eval-exp-auxo e env s (list-aux-outer-k e* env k v-out-rest) out v-out))])))

(define eval-expo
  (lambda (exp env s k out)
    (fresh (ans v s^ ignore)
      (== (answer v s^) ans)
      (== out v)
      (eval-exp-auxo exp env s k ans v))))

(define evalo
  (lambda (exp out)
    (eval-expo exp empty-env empty-store empty-k out)))

;;; datastructures based on higher-order functions

(test "cell-get-1"
  (run* (q)
    (evalo
      '((lambda (make-cell)
          ((lambda (c1) ((c1 (lambda (bang) (lambda (get) get))) c1))
            (make-cell (quote 3))))
         (lambda (value)
           (((lambda (bang)
               (lambda (get)
                 (lambda (f)
                   ((f bang) get))))
              (lambda (new-value) (set! value new-value)))
             (lambda (dummy) value))))
      q))
  '(3))

(test "cell-get-2"
  (run* (q)
    (evalo
      '((lambda (make-cell)
          ((lambda (c1) (c1 (lambda (bang) (lambda (get) (get c1)))))
            (make-cell (quote 3))))
         (lambda (value)
           (((lambda (bang)
               (lambda (get)
                 (lambda (f)
                   ((f bang) get))))
              (lambda (new-value) (set! value new-value)))
             (lambda (dummy) value))))
      q))
  '(3))

(test "cell-set-1"
  (run* (q)
    (evalo
      '((lambda (make-cell)
          ((lambda (c1)
             (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
            (make-cell (quote 3))))
         (lambda (value)
           (((lambda (bang)
               (lambda (get)
                 (lambda (f)
                   ((f bang) get))))
              (lambda (new-value) (set! value new-value)))
             (lambda (dummy) value))))
      q))
  '(4))

(test "cell-guess-1"
  (run 1 (q)
    (fresh (code-bang code-get)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang '(lambda (new-value) (set! value new-value)))
      (== code-get '(lambda (dummy) value))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-2"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) (set! value ,code-bang-part)))
      (== code-get '(lambda (dummy) value))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-3"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part code-get-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) (set! value ,code-bang-part)))
      (== code-get `(lambda (dummy) ,code-get-part))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

(test "cell-guess-4"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (absento 'throw code-bang)
      (== code-bang `(lambda (new-value) ,code-bang-part))
      (== code-get `(lambda (dummy) value))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
     (lambda (dummy) value))))

;; this one hangs
(test-disable "cell-guess-5"
  (run 1 (q)
    (fresh (code-bang code-get code-bang-part code-get-part)
      (absento 4 code-bang)
      (absento 4 code-get)
      (== code-bang `(lambda (new-value) ,code-bang-part))
      (== code-get `(lambda (dummy) ,code-get-part))
      (evalo
        `((lambda (make-cell)
            ((lambda (c1)
               (c1 (lambda (bang) (lambda (get) ((lambda (ignore) (get c1)) (bang (quote 4)))))))
              (make-cell (quote 3))))
           (lambda (value)
             (((lambda (bang)
                 (lambda (get)
                   (lambda (f)
                     ((f bang) get))))
                ,code-bang)
               ,code-get)))
        '4)
      (== q `(,code-bang ,code-get))))
  '(((lambda (new-value) (set! value new-value))
      (lambda (dummy) value))))

;;; other tests

(test "cesk-set!-1"
  (run* (q)
    (evalo '((lambda (x)
               ((lambda (ignore) x)
                (set! x (quote 5))))
             (quote 6))
           q))
  '(5))

(test "cesk-set!-backwards-1"
  (run 2 (q)
    (evalo `((lambda (x)
               ((lambda (ignore) x)
                ,q))
             (quote 6))
           '5))
  '((throw '(empty-k) '5)
    (set! x '5)))

(test "letcc/throw-0"
  (run* (q)
    (evalo '(letcc k k) q))  
  `(,empty-k))

(test "letcc/throw-0b"
  (run* (q)
    (evalo '(letcc k (quote 1)) q))
  '(1))

(test "letcc/throw-0c"
  (run* (q)
    (evalo '(letcc k (throw k (quote 1))) q))
  '(1))

(test "letcc/throw-2a"
  (run* (q)
    (evalo '(letcc k
              ((lambda (x) x)
               (throw k (lambda (y) y))))
           q))
  '(((closure y y ((k) (_.0))) (num _.0))))

(test "letcc/throw-2b"
  (run* (q)
    (evalo '(letcc k
              ((lambda (x) (quote 5))
               (throw k (quote 7))))
           q))  
  '(7))

(test "letcc/throw-2c"
  (run* (q)
    (evalo '(letcc k
              ((quote 5)
               (throw k (quote 7))))
           q))
  '(7))

(test "cesk-quote-a"
  (run* (q)
    (evalo '(quote x) q))
  '(x))

(test "cesk-quote"
  (run* (q)
    (evalo '(quote (lambda (x) x)) q))
  '((lambda (x) x)))

(test "cesk-list-0"
  (run* (q)
    (evalo '(list) q))
  '(()))

(test "cesk-closure"
  (run* (q)
    (evalo '(lambda (x) x) q))
  '((closure x x (() ()))))

(test "cesk-identity-a"
  (run* (q)
    (evalo '((lambda (x) x) (lambda (y) y)) q))
  '((closure y y (() ()))))

(test "cesk-identity-b"
  (run* (q)
    (evalo '((lambda (x) x) (quote foo)) q))
  '(foo))

(test "cesk-list-1"
  (run* (q)
    (evalo '(list (quote foo)) q))
  '((foo)))

(test "cesk-list-2"
  (run* (q)
    (evalo '(list (quote foo) (quote bar)) q))
  '((foo bar)))

(test "cesk-list-1-backwards"
  (run 10 (q)
    (evalo q '(foo)))
  '('(foo)
    ((letcc _.0 '(foo)) (=/= ((_.0 quote))) (sym _.0))
    ((letcc _.0 (letcc _.1 '(foo)))
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1))
    ((letcc _.0 (letcc _.1 (letcc _.2 '(foo))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2))
    (throw '(empty-k) '(foo))
    ((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 '(foo)))))
     (=/= ((_.0 quote))
          ((_.1 quote))
          ((_.2 quote))
          ((_.3 quote)))
     (sym _.0 _.1 _.2 _.3))
    ((letcc _.0 (throw '(empty-k) '(foo)))
     (=/= ((_.0 quote)))
     (sym _.0))
    (list 'foo)
    ((letcc
         _.0
       (letcc _.1 (letcc _.2 (letcc _.3 (letcc _.4 '(foo))))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)) ((_.3 quote))
          ((_.4 quote)))
     (sym _.0 _.1 _.2 _.3 _.4))
    ((set! _.0 (throw '(empty-k) '(foo))) (sym _.0))))

(test "cesk-list-2-backwards"
  (run 3 (q)
    (fresh (x body)
      (evalo `(lambda (,x) ,body) '(foo))))
  '())

(test "cesk-list-2b"
  (run 10 (q)
    (evalo q '(foo bar)))
  '('(foo bar) ((letcc _.0 '(foo bar)) (=/= ((_.0 quote))) (sym _.0))
    ((letcc _.0 (letcc _.1 '(foo bar)))
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1))
    ((letcc _.0 (letcc _.1 (letcc _.2 '(foo bar))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2))
    (throw '(empty-k) '(foo bar))
    ((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 '(foo bar)))))
     (=/= ((_.0 quote))
          ((_.1 quote))
          ((_.2 quote))
          ((_.3 quote)))
     (sym _.0 _.1 _.2 _.3))
    ((letcc _.0 (throw '(empty-k) '(foo bar)))
     (=/= ((_.0 quote)))
     (sym _.0))
    ((letcc
         _.0
       (letcc _.1 (letcc _.2 (letcc _.3 (letcc _.4 '(foo bar))))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)) ((_.3 quote))
          ((_.4 quote)))
     (sym _.0 _.1 _.2 _.3 _.4))
    ((set! _.0 (throw '(empty-k) '(foo bar))) (sym _.0))
    ((letcc _.0 (letcc _.1 (throw '(empty-k) '(foo bar))))
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1))))

(test "cesk-list-3"
  (run* (q)
    (evalo '(list (quote baz)
                  ((lambda (x) x) (list (quote foo) (quote bar)))
                  ((lambda (x) x) (list (quote quux))))
           q))
  '((baz (foo bar) (quux))))

(test "cesk-shadowing"
  (run* (q)
    (evalo '((lambda (x)
               ((lambda (quote)
                  (quote x))
                (lambda (y) (list y y y))))
             (quote bar))
           q))
  '((bar bar bar)))

(define quinec
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

(test "cesk-quinec-forwards"
  (run* (q)
    (evalo quinec q))
  `(,quinec))

(test "cesk-quinec-both"
  (run 1 (q)
    (evalo quinec quinec))
  '(_.0))

(test "cesk-quote-bkwards-0"
  (run 1 (q)
    (evalo (quote (quote x)) (quote x)))
  `(_.0))

(test "cesk-quote-bkwards-1"
  (run 1 (q)
    (evalo `(quote (quote x)) `(quote x)))
  `(_.0))

(test "cesk-quote-bkwards-2"
  (run 1 (q)
      (fresh (y)
        (== y 'x)
        (eval-expo `(quote ,y)
                   empty-env
                   empty-store
                   empty-k
                   q)))
  `(x))

(test "cesk-quinec-bkwards-a"
  (run 1 (q)
    (== quinec q)
    (evalo q quinec))
  `(,quinec))

(test "cesk-fresh-bkwards"
  (run 10 (q)
    (fresh (expr v)
      (evalo expr v)
      (== `(,expr ,v) q)))
  '((('_.0 _.0) (absento (closure _.0) (void _.0)))
    (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
    (((letcc _.0 '_.1) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc _.0 (lambda (_.1) _.2))
      (closure _.1 _.2 ((_.0) (_.3))))
     (=/= ((_.0 lambda)))
     (num _.3)
     (sym _.0 _.1))
    (((letcc _.0 (letcc _.1 '_.2)) _.2)
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (void _.2)))
    (((letcc _.0 _.0) (empty-k)) (sym _.0))
    (((letcc _.0 (letcc _.1 (lambda (_.2) _.3)))
      (closure _.2 _.3 ((_.1 _.0) (_.4 _.5))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.4 _.5)))
     (num _.4 _.5)
     (sym _.0 _.1 _.2))
    ((list) ())
    (((letcc _.0 (letcc _.1 (letcc _.2 '_.3))) _.3)
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2)
     (absento (closure _.3) (void _.3)))
    (((letcc _.0 (letcc _.1 _.1)) (empty-k)) (sym _.0 _.1))))

(test "cesk-quinec-bkwards-c"
  (run 10 (q)
    (evalo q quinec))
  '('((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))
    ((letcc
         _.0
       '((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
     (=/= ((_.0 quote)))
     (sym _.0))
    ((letcc
         _.0
       (letcc
           _.1
         '((lambda (x) (list x (list 'quote x)))
           '(lambda (x) (list x (list 'quote x))))))
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1))
    ((letcc
         _.0
       (letcc
           _.1
         (letcc
             _.2
           '((lambda (x) (list x (list 'quote x)))
             '(lambda (x) (list x (list 'quote x)))))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2))
    (throw
     '(empty-k)
     '((lambda (x) (list x (list 'quote x)))
       '(lambda (x) (list x (list 'quote x)))))
    ((letcc
         _.0
       (letcc
           _.1
         (letcc
             _.2
           (letcc
               _.3
             '((lambda (x) (list x (list 'quote x)))
               '(lambda (x) (list x (list 'quote x))))))))
     (=/= ((_.0 quote))
          ((_.1 quote))
          ((_.2 quote))
          ((_.3 quote)))
     (sym _.0 _.1 _.2 _.3))
    ((letcc
         _.0
       (throw
        '(empty-k)
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x))))))
     (=/= ((_.0 quote)))
     (sym _.0))
    ((letcc
         _.0
       (letcc
           _.1
         (letcc
             _.2
           (letcc
               _.3
             (letcc
                 _.4
               '((lambda (x) (list x (list 'quote x)))
                 '(lambda (x) (list x (list 'quote x)))))))))
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)) ((_.3 quote))
          ((_.4 quote)))
     (sym _.0 _.1 _.2 _.3 _.4))
    ((set! _.0
           (throw
            '(empty-k)
            '((lambda (x) (list x (list 'quote x)))
              '(lambda (x) (list x (list 'quote x))))))
     (sym _.0))
    ((letcc
         _.0
       (letcc
           _.1
         (throw
          '(empty-k)
          '((lambda (x) (list x (list 'quote x)))
            '(lambda (x) (list x (list 'quote x)))))))
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1))))

(test "cesk-bkwards-3"
  (run 50 (q)
    (fresh (expr val)
      (=/= 'void val)
      (evalo expr val)
      (== `(,expr ,val) q)))
  '((('_.0 _.0) (absento (closure _.0) (void _.0)))
    (((lambda (_.0) _.1) (closure _.0 _.1 (() ()))) (sym _.0))
    (((letcc _.0 '_.1) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc _.0 (lambda (_.1) _.2))
      (closure _.1 _.2 ((_.0) (_.3))))
     (=/= ((_.0 lambda)))
     (num _.3)
     (sym _.0 _.1))
    (((letcc _.0 (letcc _.1 '_.2)) _.2)
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (void _.2)))
    (((letcc _.0 _.0) (empty-k)) (sym _.0))
    (((letcc _.0 (letcc _.1 (lambda (_.2) _.3)))
      (closure _.2 _.3 ((_.1 _.0) (_.4 _.5))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.4 _.5)))
     (num _.4 _.5)
     (sym _.0 _.1 _.2))
    ((list) ())
    (((letcc _.0 (letcc _.1 (letcc _.2 '_.3))) _.3)
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2)
     (absento (closure _.3) (void _.3)))
    (((letcc _.0 (letcc _.1 _.1)) (empty-k)) (sym _.0 _.1))
    (((throw '(empty-k) '_.0) _.0)
     (absento (closure _.0) (void _.0)))
    (((letcc _.0 (letcc _.1 (letcc _.2 (lambda (_.3) _.4))))
      (closure _.3 _.4 ((_.2 _.1 _.0) (_.5 _.6 _.7))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.2 lambda))
          ((_.5 _.6)) ((_.5 _.7)) ((_.6 _.7)))
     (num _.5 _.6 _.7)
     (sym _.0 _.1 _.2 _.3))
    (((letcc _.0 (list)) ()) (=/= ((_.0 list))) (sym _.0))
    (((letcc _.0 (letcc _.1 _.0)) (empty-k))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))
    (((throw '(empty-k) (lambda (_.0) _.1))
      (closure _.0 _.1 (() ())))
     (sym _.0))
    (((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 '_.4)))) _.4)
     (=/= ((_.0 quote))
          ((_.1 quote))
          ((_.2 quote))
          ((_.3 quote)))
     (sym _.0 _.1 _.2 _.3)
     (absento (closure _.4) (void _.4)))
    (((letcc _.0 (letcc _.1 (letcc _.2 _.2))) (empty-k))
     (sym _.0 _.1 _.2))
    (((letcc
          _.0
        (letcc _.1 (letcc _.2 (letcc _.3 (lambda (_.4) _.5)))))
      (closure _.4 _.5 ((_.3 _.2 _.1 _.0) (_.6 _.7 _.8 _.9))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.2 lambda)) ((_.3 lambda))
          ((_.6 _.7)) ((_.6 _.8)) ((_.6 _.9)) ((_.7 _.8)) ((_.7 _.9))
          ((_.8 _.9)))
     (num _.6 _.7 _.8 _.9)
     (sym _.0 _.1 _.2 _.3 _.4))
    (((letcc _.0 (throw '(empty-k) '_.1)) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc _.0 (letcc _.1 (list))) ())
     (=/= ((_.0 list)) ((_.1 list)))
     (sym _.0 _.1))
    (((letcc _.0 (throw '(empty-k) (lambda (_.1) _.2)))
      (closure _.1 _.2 ((_.0) (_.3))))
     (=/= ((_.0 lambda)) ((_.0 quote)))
     (num _.3)
     (sym _.0 _.1))
    (((letcc _.0 (letcc _.1 (letcc _.2 _.1))) (empty-k))
     (=/= ((_.1 _.2)))
     (sym _.0 _.1 _.2))
    (((list '_.0) (_.0)) (absento (closure _.0) (void _.0)))
    (((letcc
          _.0
        (letcc _.1 (letcc _.2 (letcc _.3 (letcc _.4 '_.5)))))
      _.5)
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)) ((_.3 quote))
          ((_.4 quote)))
     (sym _.0 _.1 _.2 _.3 _.4)
     (absento (closure _.5) (void _.5)))
    (((set! _.0 (throw '(empty-k) '_.1)) _.1)
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc _.0 (letcc _.1 (letcc _.2 _.0))) (empty-k))
     (=/= ((_.0 _.1)) ((_.0 _.2)))
     (sym _.0 _.1 _.2))
    (((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 _.3))))
      (empty-k))
     (sym _.0 _.1 _.2 _.3))
    (((letcc
          _.0
        (letcc
            _.1
          (letcc _.2 (letcc _.3 (letcc _.4 (lambda (_.5) _.6))))))
      (closure
       _.5
       _.6
       ((_.4 _.3 _.2 _.1 _.0) (_.7 _.8 _.9 _.10 _.11))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.10 _.11)) ((_.10 _.7))
          ((_.10 _.8)) ((_.10 _.9)) ((_.11 _.7)) ((_.11 _.8))
          ((_.11 _.9)) ((_.2 lambda)) ((_.3 lambda)) ((_.4 lambda))
          ((_.7 _.8)) ((_.7 _.9)) ((_.8 _.9)))
     (num _.10 _.11 _.7 _.8 _.9)
     (sym _.0 _.1 _.2 _.3 _.4 _.5))
    (((letcc _.0 (letcc _.1 (throw '(empty-k) '_.2))) _.2)
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (void _.2)))
    (((throw '(throw-k '_.0 (_.1 _.2)) '(empty-k)) _.0)
     (absento (closure _.0) (closure _.1) (closure _.2) '_.1
              (void _.0) (void _.1) (void _.2)))
    (((throw '(empty-k) (letcc _.0 '_.1)) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((set! _.0 (throw '(empty-k) (lambda (_.1) _.2)))
      (closure _.1 _.2 (() ())))
     (sym _.0 _.1))
    (((list (lambda (_.0) _.1)) ((closure _.0 _.1 (() ()))))
     (sym _.0))
    (((letcc _.0 (letcc _.1 (letcc _.2 (list)))) ())
     (=/= ((_.0 list)) ((_.1 list)) ((_.2 list)))
     (sym _.0 _.1 _.2))
    (((letcc
          _.0
        (letcc _.1 (throw '(empty-k) (lambda (_.2) _.3))))
      (closure _.2 _.3 ((_.1 _.0) (_.4 _.5))))
     (=/= ((_.0 lambda)) ((_.0 quote)) ((_.1 lambda))
          ((_.1 quote)) ((_.4 _.5)))
     (num _.4 _.5)
     (sym _.0 _.1 _.2))
    (((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 _.2))))
      (empty-k))
     (=/= ((_.2 _.3)))
     (sym _.0 _.1 _.2 _.3))
    (((throw '(list-aux-inner-k _.0 (empty-k)) '_.1)
      (_.0 . _.1))
     (absento (closure _.0) (closure _.1) (void _.0) (void _.1)))
    (((letcc _.0 (list '_.1)) (_.1))
     (=/= ((_.0 list)) ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc
          _.0
        (letcc
            _.1
          (letcc _.2 (letcc _.3 (letcc _.4 (letcc _.5 '_.6))))))
      _.6)
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)) ((_.3 quote))
          ((_.4 quote)) ((_.5 quote)))
     (sym _.0 _.1 _.2 _.3 _.4 _.5)
     (absento (closure _.6) (void _.6)))
    (((throw (letcc _.0 '(empty-k)) '_.1) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (void _.1)))
    (((letcc
          _.0
        (letcc _.1 (letcc _.2 (letcc _.3 (letcc _.4 _.4)))))
      (empty-k))
     (sym _.0 _.1 _.2 _.3 _.4))
    (((letcc
          _.0
        (letcc
            _.1
          (letcc
              _.2
            (letcc _.3 (letcc _.4 (letcc _.5 (lambda (_.6) _.7)))))))
      (closure
       _.6
       _.7
       ((_.5 _.4 _.3 _.2 _.1 _.0) (_.8 _.9 _.10 _.11 _.12 _.13))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.10 _.11))
          ((_.10 _.12)) ((_.10 _.13)) ((_.10 _.8)) ((_.10 _.9))
          ((_.11 _.12)) ((_.11 _.13)) ((_.11 _.8)) ((_.11 _.9))
          ((_.12 _.13)) ((_.12 _.8)) ((_.12 _.9)) ((_.13 _.8))
          ((_.13 _.9)) ((_.2 lambda)) ((_.3 lambda)) ((_.4 lambda))
          ((_.5 lambda)) ((_.8 _.9)))
     (num _.10 _.11 _.12 _.13 _.8 _.9)
     (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6))
    (((set! _.0 (letcc _.1 (throw '(empty-k) '_.2))) _.2)
     (=/= ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) (void _.2)))
    (((throw '(throw-k (lambda (_.0) _.1) (_.2 _.3)) '(empty-k))
      (closure _.0 _.1 (_.2 _.3)))
     (=/= ((_.0 closure)) ((_.0 void)))
     (sym _.0)
     (absento (closure _.1) (closure _.2) (closure _.3)
              (lambda _.2) (void _.1) (void _.2) (void _.3)))
    (((letcc _.0 (letcc _.1 (letcc _.2 (letcc _.3 _.1))))
      (empty-k))
     (=/= ((_.1 _.2)) ((_.1 _.3)))
     (sym _.0 _.1 _.2 _.3))
    (((letcc _.0 (set! _.1 (throw '(empty-k) '_.2))) _.2)
     (=/= ((_.0 quote)) ((_.0 set!)))
     (sym _.0 _.1)
     (absento (closure _.2) (void _.2)))
    (((throw '(empty-k) (letcc _.0 (lambda (_.1) _.2)))
      (closure _.1 _.2 ((_.0) (_.3))))
     (=/= ((_.0 lambda)))
     (num _.3)
     (sym _.0 _.1))
    (((letcc
          _.0
        (letcc _.1 (letcc _.2 (throw '(empty-k) '_.3))))
      _.3)
     (=/= ((_.0 quote)) ((_.1 quote)) ((_.2 quote)))
     (sym _.0 _.1 _.2)
     (absento (closure _.3) (void _.3)))
    ((((lambda (_.0) '_.1) '_.2) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (closure _.2) (void _.1) (void _.2)))
    (((letcc _.0 (throw '(throw-k '_.1 (_.2 _.3)) '(empty-k)))
      _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) (closure _.2) (closure _.3) '_.2
              (void _.1) (void _.2) (void _.3)))))

(test "cesk-quinec-bkwards-a"
  (run 50 (q)
    (fresh (expr env store k val)
      (eval-expo
       expr
       env
       store
       k
       val)
      (== `(,expr ,env ,store ,k ,val) q)))
  '((('_.0 (_.1 _.2) _.3 (empty-k) _.0)
     (absento (closure _.0) '_.1 (void _.0)))
    (((lambda (_.0) _.1)
      (_.2 _.3)
      _.4
      (empty-k)
      (closure _.0 _.1 (_.2 _.3)))
     (sym _.0)
     (absento (lambda _.2)))
    (('(empty-k)
      (_.0 _.1)
      _.2
      (throw-k '(empty-k) (_.3 _.4))
      (empty-k))
     (absento '_.0 '_.3))
    (((letcc _.0 '_.1) (_.2 _.3) (_.4 _.5) (empty-k) _.1)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (_.5 . _.6))
          (empty-k)
          _.5)
     (num _.2)
     (sym _.0))
    (((letcc _.0 (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (empty-k)
      (closure _.1 _.2 ((_.0 . _.3) (_.7 . _.4))))
     (=/= ((_.0 lambda)))
     (num _.7)
     (sym _.0 _.1)
     (absento (_.7 _.5) (lambda _.3)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '_.0 (_.6 _.7))
       (empty-k)
       _.0)
      _.0)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) '_.1 '_.6 (void _.0)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k _.6 ((_.6 . _.7) (_.8 . _.9)) (empty-k))
      void)
     (=/= ((_.0 quote)))
     (num _.8)
     (sym _.0 _.6)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 _.7 . _.8))
          (empty-k)
          _.7)
     (=/= ((_.2 _.4)))
     (num _.2 _.4)
     (sym _.0))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k _.6 ((_.7 _.6 . _.8) (_.9 _.10 . _.11)) (empty-k))
      void)
     (=/= ((_.0 quote)) ((_.6 _.7)))
     (num _.10 _.9)
     (sym _.0 _.6 _.7)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.4 _.6 . _.7) (_.8 _.9 . _.10))
          (empty-k)
          _.8)
     (=/= ((_.0 _.1)))
     (num _.3 _.4 _.6)
     (sym _.0 _.1))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (void . _.5))
          (set!-k _.6 ((_.6 . _.7) (_.8 . _.9)) (empty-k))
          void)
     (num _.2 _.8)
     (sym _.0 _.6))
    (((letcc _.0 (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (set!-k _.7 ((_.7 . _.8) (_.9 . _.10)) (empty-k))
      void)
     (=/= ((_.0 lambda)))
     (num _.9)
     (sym _.0 _.1 _.7)
     (absento (lambda _.3)))
    (((letcc _.0 '(empty-k))
      (_.1 _.2)
      (_.3 _.4)
      (throw-k '_.5 (_.6 _.7))
      _.5)
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.5) '_.1 '_.6 (void _.5)))
    (((lambda (_.0) _.1)
      ((_.2 . _.3) (_.4 . _.5))
      (_.6 _.7)
      (application-inner-k
       (closure _.2 (lambda (_.0) _.1) (_.3 _.5))
       (empty-k)
       (closure _.0 _.1 ((_.2 . _.3) (_.4 . _.5))))
      (closure _.0 _.1 ((_.2 . _.3) (_.4 . _.5))))
     (=/= ((_.2 lambda)))
     (num _.4)
     (sym _.0 _.2)
     (absento (_.4 _.6) (lambda _.3)))
    (('(empty-k)
      (_.0 _.1)
      (_.2 _.3)
      (throw-k (letcc _.4 '(empty-k)) (_.5 _.6))
      (empty-k))
     (=/= ((_.4 quote)))
     (sym _.4)
     (absento '_.0 '_.5))
    (((letcc _.0 (letcc _.1 '_.2))
      (_.3 _.4)
      (_.5 _.6)
      (empty-k)
      _.2)
     (=/= ((_.0 quote)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2) '_.3 (void _.2)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (set!-k
       _.5
       ((_.5 . _.6) (_.7 . _.8))
       (application-inner-k
        (closure _.9 '_.0 (_.10 _.11))
        (empty-k)
        _.0))
      _.0)
     (=/= ((_.9 quote)))
     (num _.7)
     (sym _.5 _.9)
     (absento (closure _.0) '_.1 '_.10 (void _.0)))
    (('(list-aux-inner-k list-aux-inner-k (empty-k))
      (_.0 _.1)
      _.2
      (throw-k '(list-aux-inner-k (empty-k)) (_.3 _.4))
      (list-aux-inner-k list-aux-inner-k (empty-k)))
     (absento '_.0 '_.3))
    (((set! _.0 '_.1)
      ((_.0 . _.2) (_.3 . _.4))
      (_.5 _.6)
      (empty-k)
      void)
     (=/= ((_.0 quote)) ((_.0 set!)))
     (num _.3)
     (sym _.0)
     (absento (closure _.1) '_.2 (set! _.2) (void _.1)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k
       _.6
       ((_.7 _.8 _.6 . _.9) (_.10 _.11 _.12 . _.13))
       (empty-k))
      void)
     (=/= ((_.0 quote)) ((_.6 _.7)) ((_.6 _.8)))
     (num _.10 _.11 _.12)
     (sym _.0 _.6 _.7 _.8)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.5 _.2 . _.6) (_.7 _.8 _.9 . _.10))
          (empty-k)
          _.9)
     (=/= ((_.2 _.4)) ((_.2 _.5)))
     (num _.2 _.4 _.5)
     (sym _.0))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (void . _.5))
          (set!-k _.6 ((_.7 _.6 . _.8) (_.9 _.10 . _.11)) (empty-k))
          void)
     (=/= ((_.6 _.7)))
     (num _.10 _.2 _.9)
     (sym _.0 _.6 _.7))
    (((letcc _.0 (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (set!-k _.7 ((_.8 _.7 . _.9) (_.10 _.11 . _.12)) (empty-k))
      void)
     (=/= ((_.0 lambda)) ((_.7 _.8)))
     (num _.10 _.11)
     (sym _.0 _.1 _.7 _.8)
     (absento (lambda _.3)))
    (((list) (_.0 _.1) _.2 (empty-k) ()) (absento (list _.0)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k
       _.6
       ((_.6 . _.7) (_.8 . _.9))
       (set!-k _.10 ((_.10 . _.11) (_.12 . _.13)) (empty-k)))
      void)
     (=/= ((_.0 quote)))
     (num _.12 _.8)
     (sym _.0 _.10 _.6)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 void . _.7))
          (set!-k _.8 ((_.8 . _.9) (_.10 . _.11)) (empty-k))
          void)
     (=/= ((_.2 _.4)))
     (num _.10 _.2 _.4)
     (sym _.0 _.8))
    (('(empty-k)
      (_.0 _.1)
      ((_.2 . _.3) ((empty-k) . _.4))
      (throw-k _.5 ((_.5 . _.6) (_.2 . _.7)))
      (empty-k))
     (num _.2)
     (sym _.5)
     (absento '_.0))
    (((letcc _.0 '(empty-k))
      (_.1 _.2)
      (_.3 _.4)
      (throw-k (lambda (_.5) _.6) (_.7 _.8))
      (closure _.5 _.6 (_.7 _.8)))
     (=/= ((_.0 quote)))
     (sym _.0 _.5)
     (absento (lambda _.7) '_.1))
    (((letcc _.0 _.0) (_.1 _.2) (_.3 _.4) (empty-k) (empty-k))
     (sym _.0))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) ((empty-k) . _.5))
          (throw-k '(empty-k) (_.6 _.7))
          (empty-k))
     (num _.2)
     (sym _.0)
     (absento '_.6))
    (((letcc _.0 (letcc _.1 (lambda (_.2) _.3)))
      (_.4 _.5)
      (_.6 _.7)
      (empty-k)
      (closure _.2 _.3 ((_.1 _.0 . _.4) (_.8 _.9 . _.5))))
     (=/= ((_.0 lambda)) ((_.1 lambda)) ((_.8 _.9)))
     (num _.8 _.9)
     (sym _.0 _.1 _.2)
     (absento (_.8 _.6) (_.9 _.6) (lambda _.4)))
    (((set! _.0 '_.1)
      ((_.2 _.0 . _.3) (_.4 _.5 . _.6))
      (_.7 _.8)
      (empty-k)
      void)
     (=/= ((_.0 _.2)) ((_.0 quote)) ((_.0 set!)) ((_.2 quote))
          ((_.2 set!)))
     (num _.4 _.5)
     (sym _.0 _.2)
     (absento (closure _.1) '_.3 (set! _.3) (void _.1)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 '(empty-k) (_.6 _.7))
       (throw-k '_.0 (_.8 _.9))
       (empty-k))
      _.0)
     (=/= ((_.5 quote)))
     (sym _.5)
     (absento (closure _.0) '_.1 '_.6 '_.8 (void _.0)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (list-aux-inner-k _.6 (empty-k))
      (_.6 . _.1))
     (=/= ((_.0 quote)))
     (sym _.0)
     (absento (closure _.1) '_.2 (void _.1)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (application-inner-k
       (closure _.5 (letcc _.6 '_.0) (_.7 _.8))
       (empty-k)
       _.9)
      _.0)
     (=/= ((_.5 quote)) ((_.6 quote)))
     (sym _.5 _.6)
     (absento (closure _.0) '_.1 '_.7 (void _.0)))
    (('_.0
      (_.1 _.2)
      (_.3 _.4)
      (set!-k
       _.5
       ((_.6 _.5 . _.7) (_.8 _.9 . _.10))
       (application-inner-k
        (closure _.11 '_.0 (_.12 _.13))
        (empty-k)
        _.0))
      _.0)
     (=/= ((_.11 quote)) ((_.5 _.6)))
     (num _.8 _.9)
     (sym _.11 _.5 _.6)
     (absento (closure _.0) '_.1 '_.12 (void _.0)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (application-inner-k
       (closure _.6 '_.7 (_.8 _.9))
       (empty-k)
       _.7)
      _.7)
     (=/= ((_.0 quote)) ((_.6 quote)))
     (sym _.0 _.6)
     (absento (closure _.1) (closure _.7) '_.2 '_.8 (void _.1)
              (void _.7)))
    (((set! _.0 (lambda (_.1) _.2))
      ((_.0 . _.3) (_.4 . _.5))
      (_.6 _.7)
      (empty-k)
      void)
     (=/= ((_.0 lambda)) ((_.0 set!)))
     (num _.4)
     (sym _.0 _.1)
     (absento (lambda _.3) (set! _.3)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k
       _.6
       ((_.7 _.8 _.9 _.6 . _.10) (_.11 _.12 _.13 _.14 . _.15))
       (empty-k))
      void)
     (=/= ((_.0 quote)) ((_.6 _.7)) ((_.6 _.8)) ((_.6 _.9)))
     (num _.11 _.12 _.13 _.14)
     (sym _.0 _.6 _.7 _.8 _.9)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (void . _.5))
          (set!-k
           _.6
           ((_.7 _.8 _.6 . _.9) (_.10 _.11 _.12 . _.13))
           (empty-k))
          void)
     (=/= ((_.6 _.7)) ((_.6 _.8)))
     (num _.10 _.11 _.12 _.2)
     (sym _.0 _.6 _.7 _.8))
    (((letcc _.0 (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (set!-k
       _.7
       ((_.8 _.9 _.7 . _.10) (_.11 _.12 _.13 . _.14))
       (empty-k))
      void)
     (=/= ((_.0 lambda)) ((_.7 _.8)) ((_.7 _.9)))
     (num _.11 _.12 _.13)
     (sym _.0 _.1 _.7 _.8 _.9)
     (absento (lambda _.3)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k
       _.6
       ((_.6 . _.7) (_.8 . _.9))
       (set!-k
        _.10
        ((_.11 _.10 . _.12) (_.13 _.14 . _.15))
        (empty-k)))
      void)
     (=/= ((_.0 quote)) ((_.10 _.11)))
     (num _.13 _.14 _.8)
     (sym _.0 _.10 _.11 _.6)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.4 _.2 . _.5) (_.6 void . _.7))
          (set!-k _.8 ((_.9 _.8 . _.10) (_.11 _.12 . _.13)) (empty-k))
          void)
     (=/= ((_.2 _.4)) ((_.8 _.9)))
     (num _.11 _.12 _.2 _.4)
     (sym _.0 _.8 _.9))
    (((throw '(empty-k) '_.0) (_.1 _.2) _.3 _.4 _.0)
     (absento (closure _.0) '_.1 (void _.0)))
    (((letcc _.0 '_.1)
      (_.2 _.3)
      (_.4 _.5)
      (set!-k
       _.6
       ((_.7 _.6 . _.8) (_.9 _.10 . _.11))
       (set!-k _.12 ((_.12 . _.13) (_.14 . _.15)) (empty-k)))
      void)
     (=/= ((_.0 quote)) ((_.6 _.7)))
     (num _.10 _.14 _.9)
     (sym _.0 _.12 _.6 _.7)
     (absento (closure _.1) '_.2 (void _.1)))
    ((_.0 ((_.1 _.0 . _.2) (_.3 _.4 . _.5))
          ((_.4 _.6 . _.7) (void _.8 . _.9))
          (set!-k _.10 ((_.10 . _.11) (_.12 . _.13)) (empty-k))
          void)
     (=/= ((_.0 _.1)))
     (num _.12 _.3 _.4 _.6)
     (sym _.0 _.1 _.10))
    ((_.0 ((_.0 . _.1) (_.2 . _.3))
          ((_.2 . _.4) (void . _.5))
          (set!-k
           _.6
           ((_.6 . _.7) (_.8 . _.9))
           (set!-k _.10 ((_.10 . _.11) (_.12 . _.13)) (empty-k)))
          void)
     (num _.12 _.2 _.8)
     (sym _.0 _.10 _.6))
    (((letcc _.0 (lambda (_.1) _.2))
      (_.3 _.4)
      (_.5 _.6)
      (set!-k
       _.7
       ((_.7 . _.8) (_.9 . _.10))
       (set!-k _.11 ((_.11 . _.12) (_.13 . _.14)) (empty-k)))
      void)
     (=/= ((_.0 lambda)))
     (num _.13 _.9)
     (sym _.0 _.1 _.11 _.7)
     (absento (lambda _.3)))
    (((set! _.0 '_.1)
      ((_.2 _.3 _.0 . _.4) (_.5 _.6 _.7 . _.8))
      (_.9 _.10)
      (empty-k)
      void)
     (=/= ((_.0 _.2)) ((_.0 _.3)) ((_.0 quote)) ((_.0 set!))
          ((_.2 quote)) ((_.2 set!)) ((_.3 quote)) ((_.3 set!)))
     (num _.5 _.6 _.7)
     (sym _.0 _.2 _.3)
     (absento (closure _.1) '_.4 (set! _.4) (void _.1)))))

(test "cesk-quinec-for-real"
  (run 1 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0))) '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)) ((_.0 void))) (sym _.0))))

(test "twines"
  (run 1 (r)
    (fresh (p q)
      (=/= p q)
      (evalo p q)
      (evalo q p)
      (== `(,p ,q) r)))
  '((('((lambda (_.0)
          (list 'quote (list _.0 (list 'quote _.0))))
        '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
      ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
       '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "cesk-quinec-for-real-3"
  (run 3 (q)
    (evalo q q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))
    (((lambda (_.0)
        (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
      '(lambda (_.0)
         (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
     (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
          ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
     (sym _.0 _.1)
     (absento (closure _.2)))
    (((lambda (_.0)
        (list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
      '(list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "cesk-hard-quinec-bkwards-b"
  (run 1 (q)
    (evalo q quinec)
    (== quinec q))
  `(,quinec))


#!eof

;;; Let thrines run for a while, but it didn't come back
(test "thrine"
  (run 1 (x)
    (fresh (p q r)
      (=/= p q)
      (=/= q r)
      (=/= r p)
      (evalo p q)
      (evalo q r)
      (evalo r p)
      (== `(,p ,q ,r) x)))
  '???)

(test "thrines"
  (run 1 (out)
    (fresh (p q r)
      (=/= p q)
      (=/= p r)
      (=/= q r)
      (evalo p q)
      (evalo q r)
      (evalo r p)
      (== `(,p ,q ,r) out)))
  '???)
