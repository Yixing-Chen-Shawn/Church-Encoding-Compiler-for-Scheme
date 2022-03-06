#lang racket

;; Project 2: A Church encoding compiler that translates Scheme to the
;; Lambda-calculus

(provide church-compile
         ; provided conversions:
         church->nat
         church->bool
         church->listof)

;; Input language:
;
; e ::= (letrec ([x (lambda (x ...) e)]) e)
;     | (let ([x e] ...) e)
;     | (let* ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (e e ...)    
;     | x  
;     | (and e ...) | (or e ...)
;     | (if e e e)
;     | (prim e) | (prim e e)
;     | datum
; datum ::= nat | (quote ()) | #t | #f 
; nat ::= 0 | 1 | 2 | ... 
; x is a symbol
; prim is a primitive operation in list prims
; The following are *extra credit*: -, =, sub1  
(define prims '(+ * - = add1 sub1 cons car cdr null? not zero?))

; This input language has semantics identical to Scheme / Racket, except:
;   + You will not be provided code that yields any kind of error in Racket
;   + You do not need to treat non-boolean values as #t at if, and, or forms
;   + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr), 
;                                           or binary (+ - * = cons)
;   + There will be no variadic functions or applications---but any fixed arity is allowed

;; Output language:

; e ::= (lambda (x) e)
;     | (e e)
;     | x
;
; also as interpreted by Racket

;; Using the following decoding functions:

; A church-encoded nat is a function taking an f, and x, returning (f^n x)
(define (church->nat c-nat)
  ((c-nat add1) 0))

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
(define (church->bool c-bool)
  ((c-bool #t) #f))
  ;;((c-bool (lambda (_) #t)) (lambda (_) #f)))

; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning when-cons applied on the car and cdr elements
; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning the when-null thunk, applied on a dummy value (arbitrary value that will be thrown away)
(define ((church->listof T) c-lst)
  ; when it's a pair, convert the element with T, and the tail with (church->listof T)
  ((c-lst (lambda (a) (lambda (b) (cons (T a) ((church->listof T) b)))))
   ; when it's null, return Racket's null
   (lambda (_) '())))

;; generate church numerals from a natural number
(define (nat->church-nat n)
  (define (h n)
    (match n
      [0 'x]
      [n `(f ,(h (- n 1)))]))
  `(lambda (f) (lambda (x) ,(h n))))

;; Write your church-compiling code below:
(define prog
  '(let* ([a 2] [b 3])
     (let* ([b 5] [c b])
       (* a (* b c)))))

(define prog-1 '(let ([f (lambda (a b c) (+ a (+ b c)))])
                (f (f 0 0 5) (f 10 15 20) (f 25 30 35))))


; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)
(define (churchify e)
  (match e
    [`(letrec ([,var-name ,binding-expr]) ,e-body)
     (churchify `(let ([,var-name (Y (lambda (,var-name) ,(churchify binding-expr)))]) ,e-body))]
    [`(let ([,var-names ,binding-exprs] ...) ,let-body) (churchify (foldl (lambda (x y acc)
                                                                            `((lambda (,x) ,acc) ,y)) let-body var-names binding-exprs))]
    [`(let ([,var-name ,binding-expr]) ,let-body)
   ;; can translate to lambda calculus...
   `((lambda (,var-name) ,(churchify binding-expr)) ,(churchify let-body))]
    [`(let () ,let-body) (churchify `(lambda () let-body))]
    [`(let* ([,var-names ,binding-exprs] ...) ,let-body) (churchify (foldr (lambda (x y acc)
                                                                             `((lambda (,x) ,acc) ,y)) let-body var-names binding-exprs))]
    [`(let* ([,var-name ,binding-expr]) ,let-body)
   ;; can translate to lambda calculus...
   `((lambda (,var-name) ,(churchify binding-expr)) ,(churchify let-body))]
    [`(let* () ,let-body) (churchify `(lambda () let-body))]
    [`(add1 ,x) (churchify `(+ 1 ,(churchify x)))]
    [`(sub1 ,x) (churchify `(- ,(churchify x) 1))]
    ;; when guard is evaluated down to #t, it will just be churchified to `(lambda (a) (lambda (b) a))
    ;; after beta reduction twice for two arguements
    ;; firstly it will return (lambda (b) (lambda () ,(churchify t-body)))
    ;; secondly, since b is not bound anywhere, it will just return (lambda () ,(churchify t-body))
    ;; same logic for when guard is #f
    [`(if ,guard ,t-body ,f-body) `(((,(churchify guard) (lambda () ,(churchify t-body))) (lambda () ,(churchify f-body))))]
    [`#t `(lambda (a) (lambda (b) a))]
    [`#f `(lambda (a) (lambda (b) b))]
    [`(= ,a ,b) (churchify `(and (zero? (- ,a ,b)) (zero? (- ,b ,a))))]
    ;;cons := λx . λy . λz . z x y
    [`(cons ,a ,b) `(lambda (when-cons) (lambda (when-null) ((when-cons ,(churchify a)) ,(churchify b))))]
    [''() '(lambda (when-cons) (lambda (when-null) (when-null (lambda (f) (lambda (x) (f x))))))]
    ;;if e is  (lambda (a) (lambda (b) a)), then after reduction
    ;;(((lambda (a) (lambda (b) a)) (lambda (a) (lambda (b) b))) (lambda (a) (lambda (b) a)))
    ;;((lambda (b) (lambda (a) (lambda (b) b))) (lambda (a) (lambda (b) a)))
    ;;(lambda (a) (lambda (b) b))
    ;;after churchify, it will evaluate down to #f
    ;;vice versa for when e is #t
    [`(not ,e) (churchify `((,e (lambda (a) (lambda (b) b))) (lambda (a) (lambda (b) a))))]
    [`(and) `(lambda (a) (lambda (b) a))]
    ;; and is short circuit, just check if we have false already, if so, return.
    ;; otherwise, we cons and into the rest of list, then keep churchifying into lamda expr.
    ;; (and #t #f)
    ;;(((lambda (a) (lambda (b) a)) (lambda (a) (lambda (b) b))) (lambda (a) (lambda (b) b)))
    ;;((lambda (b) (lambda (a) (lambda (b) b))) (lambda (a) (lambda (b) b)))
    ;;(lambda (a) (lambda (b) b)) cuz there not bound occuring for var b.
    [`(and . ,e)
     (if (equal? (churchify (car e)) `(lambda (a) (lambda (b) b)))
         `(lambda (a) (lambda (b) b))
         `((,(churchify (car e)) ,(churchify `(and . ,(cdr e)))) (lambda (a) (lambda (b) b))))]
    [`(or) `(lambda (a) (lambda (b) b))]
    [`(or . ,e)
     (if (equal? (churchify (car e)) `(lambda (a) (lambda (b) a)))
         `(lambda (a) (lambda (b) a))
         ;; the logic here is if first is #f, it will do the following beta reduction, and get identity function.
         ;;why? beacuse the result is just gonna depend on what the next (churchify `(or . ,(cdr e))) evaluated to.
         ;;((lambda (a) (lambda (b) b)) (lambda (a) (lambda (b) a)))
         ;;(lambda (b) b)
         ;;sub b with (churchify `(or . ,(cdr e))), it returns just (churchify `(or . ,(cdr e)))
         ;; if the first is #t, it will just ,no matter what the (churchify `(or . ,(cdr e))) evaluated downt to
         ;; it will simple return (lambda (a) (lambda (b) a)) which is #t,
         ;; for some reasons, it could not achieve short circuiting
         ;; so i used if to pre-check if #t is occured or not. 
         ;;((lambda (a) (lambda (b) a)) (lambda (a) (lambda (b) a)))
         ;;(lambda (b) (lambda (a) (lambda (b) a)))
         `((,(churchify (car e)) (lambda (a) (lambda (b) a))) ,(churchify `(or . ,(cdr e)))))]
    ;;car := λz . z (λx . λy . x)
    ;;cdr := λz . z (λx . λy . y)
    [`(car ,lst) `((,(churchify lst) (lambda (x) (lambda (y) x))) (lambda (_) a))]
    [`(cdr ,lst) `((,(churchify lst) (lambda (x) (lambda (y) y))) (lambda (_) a))]
    ;;NULL := λp.p (λx.λy.FALSE)
    [`(null? ,lst) `((lambda (p) ((p (lambda (x) (lambda (y) (lambda (t) (lambda (f) f))))) (lambda (_) (lambda (t) (lambda (f) t))))) ,(churchify lst))]
    ;;ISZERO := λn.n (λx.FALSE) TRUE
    [`(zero? ,e) `((,(churchify e) (lambda (x) (lambda (t) (lambda (f) f)))) (lambda (t) (lambda (f) t)))]
    [`(lambda () ,e-body) `(lambda (_) ,(churchify e-body))]
    [`(lambda (,x) ,e-body)
     `(lambda (,x) ,(churchify e-body))]
    [`(lambda (,x ,ys ...) ,e-body)
     `(lambda (,x) ,(churchify `(lambda ,ys ,e-body)))]
    [(? number? n) (nat->church-nat n)]
    [`(,e0) `(,(churchify e0) (lambda (x) x))]
    [`(,e0 ,e1) `(,(churchify e0) ,(churchify e1))]
    [`(,e0 ,e1 ,e2) (churchify `((,e0 ,e1) ,e2))]
    [`(,e0 ,e1 ,e2 ...) (churchify `((,e0 ,e1) ,@e2))]
    [_ e]))
#|(letrec ([is-even? (lambda (n)
                       (or (zero? n)
                           (odd? (sub1 n))))]) (is-even? 4))
|#
; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (churchify
   `(let ([+ (lambda (n) (lambda (k) (lambda (f) (lambda (x) ((k f) ((n f) x))))))]
          [- (lambda (m) (lambda (n)
                                 ((n (lambda (n)
                                       (lambda (f)
                                         (lambda (x)
                                           (((n (lambda (g) (lambda (h) (h (g f)))))
                                             (lambda (u) x))
                                            (lambda (u) u)))))) m)))]
          [* (lambda (n) (lambda (m) (lambda (f) (lambda (x) ((m (n f)) x)))))]
          [Y ((lambda (x) (x x)) (lambda (y) (lambda (f) (f (lambda (x) (((y y) f) x))))))])
      ,program)))
