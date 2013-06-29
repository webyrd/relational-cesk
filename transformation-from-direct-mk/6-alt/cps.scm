;;; CPS practice

(load "mk.scm")

(define append
  (lambda (l s)
    (match l
      [() s]
      [(,a . ,d) `(,a . ,(append d s))])))

(define appendo
  (lambda (l s out)
    (conde
      [(== '() l)
       (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (appendo d s res)
         (== `(,a . ,res) out))])))

;;;;;;;

(define append-anf
  (lambda (l s)
    (match l
      [() s]
      [(,a . ,d)
       (let ((res (append-anf d s)))
         `(,a . ,res))])))

(define append-anfo
  (lambda (l s out)
    (conde
      [(== '() l) (== s out)]
      [(== `(,a . ,d) l)
       (fresh (res)
         (append-anfo d s res)
         (== `(,a . ,res) out))])))

;;;;;

; Higher-order k

(define append-cps
  (lambda (l s k)
    (match l
      [() (k s)]
      [(,a . ,d)
       (append-cps d s (lambda (res)
                         `(,a . ,res)))])))
(define append
  (lambda (l s)
    (append-cps l s (lambda (v) v))))


(define append-cpso
;;; are the wires broken in this version?  presumably, since out is never used until the last step
;;; try reconnecting the wires
  (lambda (l s k out)
    (conde
      [(== '() l) (k s out)]
      [(== `(,a . ,d) l)
       (append-cpso d s (lambda (res out^) ; all continuations take an out^ argument
                          (== `(,a . ,res) out^)) out)])))

(define appendo
  (lambda (l s out)
    (append-cpso l s (lambda (v out^) (== v out^)) out)))

;; move to 1st-order rep of k, to ensure all arguments make sense while being fresh logic variables

; RI

(define apply-ko
  (lambda (k v out^)
    (k v out^)))

(define empty-k
  (lambda ()
    (lambda (v out^)
      (== v out^))))

(define append-k
  (lambda (a)
    (lambda (v out^)
      (== `(,a . ,v) out^))))

(define append-cpso
  (lambda (l s k out)
    (conde
      [(== '() l) (apply-ko k s out)]
      [(== `(,a . ,d) l)
       (append-cpso d s (append-k a) out)])))

(define appendo
  (lambda (l s out)
    (append-cpso l s (empty-k) out)))

; 1st order

(define apply-ko
  (lambda (k v out^)
    (conde
      [(== '(empty-k) k) (== v out^)]
      [(fresh (a)
         (== `(append-k ,a) k)
         (== `(,a . ,v) out^))])))

(define empty-k
  (lambda ()
    '(empty-k)))

(define append-k
  (lambda (a)
    (lambda (v out^)
      (== `(,a . ,v) out^))))

(define append-cpso
  (lambda (l s k out)
    (conde
      [(== '() l) (apply-ko k s out)]
      [(== `(,a . ,d) l)
       (append-cpso d s (append-k a) out)])))

(define appendo
  (lambda (l s out)
    (append-cpso l s (empty-k) out)))





;;; h-o, CPSing appendo      continuation goal ko takes a value and an out^

(define appendo-cps
  (lambda (l s out ko)
    (conde
      [(== '() l)
       (ko s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (appendo-cps d s res (lambda (v out^)
                                (== `(,a . ,res) out))))])))

(define appendo
  (lambda (l s out)
    (appendo l s out (lambda (v out^) (== out^ v)))))



;;;;;;  CPS the ANF version of append

(define append-anf
  (lambda (l s)
    (match l
      [() s]
      [(,a . ,d)
       (let ((res (append-anf d s)))
         `(,a . ,res))])))

(define append-anf-cps
  (lambda (l s k)
    (match l
      [() (k s)]
      [(,a . ,d)
       (append-anf-cps d s (lambda (v)
                             (let ((res v))
                               (k `(,a . ,res)))))])))
; which simplifies to...
(define append-anf-cps
  (lambda (l s k)
    (match l
      [() (k s)]
      [(,a . ,d)
       (append-anf-cps d s (lambda (v)
                             (k `(,a . ,v))))])))

(define append-anf
  (lambda (l s)
    (append-anf-cps l s (lambda (v) v))))

;; mk version (h-o):

(define append-anf-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (ko s out)]
      [(fresh (a d)
         (== `(,a . ,d) l)
         (append-anf-cpso d s (lambda (v out^)
                                (ko `(,a . ,v) out^))
                          out))])))

(define append-anfo
  (lambda (l s out)
    (append-anf-cpso l s (lambda (v out^) (== out^ v)) out)))


;; RI

(define apply-ko
  (lambda (k v out^)
    (k v out^)))

(define empty-k
  (lambda ()
    (lambda (v out^)
      (== out^ v))))

(define append-k
  (lambda (a k^)
    (lambda (v out^)
      (apply-ko k^ `(,a . ,v) out^))))

(define append-anf-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (apply-ko ko s out)]
      [(== `(,a . ,d) l)
       (append-anf-cpso d s (append-k a k) out)])))

(define append-anfo
  (lambda (l s out)
    (append-anf-cpso l s (empty-k) out)))

;; 1st order

(define apply-ko
  (lambda (k v out^)
    (conde
      [(== '(empty-k) k)
       (== out^ v)]
      [(fresh (a k^)
         (== `(append-k ,a ,k^) k)
         (apply-ko k^ `(,a . ,v) out^))])))

(define empty-k
  (lambda ()
    '(empty-k)))

(define append-k
  (lambda (a k^)
    `(append-k ,a ,k^)))

(define append-anf-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (apply-ko ko s out)]
      [(== `(,a . ,d) l)
       (append-anf-cpso d s (append-k a) out)])))

(define append-anfo
  (lambda (l s out)
    (append-anf-cpso l s (empty-k) out)))




;;; CPS original (unnested) mk code

;; start
(define appendo
  (lambda (l s out)
    (conde
      [(== '() l)
       (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (appendo d s res)
         (== `(,a . ,res) out))])))



(define appendo-cpso
  (lambda (l s ko out)
    (conde
      [(== '() l) (ko s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (appendo-cps d s (lambda (v out^)
                            (ko `(,a . ,res) out)) ; weird.  Do I just ignore v and out^?  They seem extraneous
                                                   ; is reconnecting the wires somehow equivalent to unifying (== out^ out) and/or (== v res)???  Should check divergence behavior, and compare with behavior of append-anf-cpso.  Also, try reconnecting the wires in append-anf-cpso: is this equivalent to (== out^ out)?
                      res))])))

(define appendo
  (lambda (l s out)
    (appendo-cpso l s (lambda (v out^) (== out^ v)) out)))
