#lang racket

(require "compose-simple.rkt")

;; List a = (cons a (List a)) | null

;; Stream a = 'head -> a
;;          & 'tail -> Stream a

;; takes : (Stream a, Nat) -> List a
(define*
  [(takes s 0) = null]
  [(takes s 1) = (list (s 'head))]
  [(takes s n) = (cons (s 'head)
                       (takes (s 'tail) (- n 1)))])

;; drops : (Stream a, Nat) -> Stream a
(define*
  [(drops s 0) = s]
  [(drops s n) = (drops (s 'tail) (- n 1))])

;; index : (Stream a, Nat) -> a
(define (index s n) ((drops s n) 'head))

;; zeroes : Stream 0
(define*
  [(zeroes 'head) = 0]
  [(zeroes 'tail) = zeroes])

;; count : Nat -> Stream Nat
(define*
  [((count n) 'head) = n]
  [((count n) 'tail) = (count (+ n 1))])

;; stutter : Stream Nat
(define*
  [ ((stutter n) 'head)        = n]
  [(((stutter n) 'tail) 'head) = n]
  [(((stutter n) 'tail) 'tail) = (stutter (+ n 1))])

;; always : a -> Stream a
(define*
  [((always x) 'head) = x]
  [((always x) 'tail) = (always x)])

;; maps : ((a -> b), Stream a) -> Stream b
(define*
  [((maps f xs) 'head) = (f (xs 'head))]
  [((maps f xs) 'tail) = (maps f (xs 'tail))])

;; iterate : ((a -> a), a) -> Stream a
(define*
  [((iterate f x) 'head) = x]
  [((iterate f x) 'tail) = (iterate f (f x))])

(define nats (iterate (λ(x) (+ x 1)) 0))
(define squares (maps (λ(x) (* x x)) nats))


;; zigzag : (Stream a, Stream a) -> Stream a
(define*
  [ ((zigzag xs ys) 'head)        = (xs 'head)]
  [(((zigzag xs ys) 'tail) 'head) = (ys 'head)]
  [(((zigzag xs ys) 'tail) 'tail) = (zigzag (xs 'tail) (ys 'tail))])

;; evens : Stream a -> Stream a
;; odds  : Stream a -> Stream a
(define*
  [((evens xs) 'head) = (xs 'head)]
  [((evens xs) 'tail) = (odds (xs 'tail))])

(define (odds xs) (evens (xs 'tail)))

;; Composable evaluation

;; Expr = (list 'num Number)
;;      | (list 'add Expr Expr)
;;      | (list 'mul Expr Expr)

(define expr1 '(add (mul (num 2) (num 3)) (num 4)))

;; expr? : Any -> Bool
(define*
  [(expr? (list 'num n))   = (number? n)]
  [(expr? (list 'add l r)) = (and (expr? l) (expr? r))]
  [(expr? (list 'mul l r)) = (and (expr? l) (expr? r))]
  [(expr? _)               = false])

;; eval : Expr -> Number
(define*
  [(eval (list 'num n))   = n]
  [(eval (list 'add l r)) = (+ (eval l) (eval r))]
  [(eval (list 'mul l r)) = (* (eval l) (eval r))])

;; eval* : Expr -> Number
(define eval*
  (λ* [(eval (list 'num n))   = n]
      [(eval (list 'add l r)) = (+ (eval l) (eval r))]
      [(eval (list 'mul l r)) = (* (eval l) (eval r))]))

(define-object list-nums
  [(self (list 'num n))   = (list n)]
  [(self (list 'add l r)) = (append (self l) (self r))]
  [(self (list 'mul l r)) = (append (self l) (self r))])

(define list-nums+sub
  (list-nums
   'compose
   (object [(self (list 'sub l r)) = (append (self l) (self r))])))

;; eval-num : (list 'num Number) -> Number
(define-object
  [(eval-num 'eval (list 'num n)) = n])

;; eval-add : (list 'add e e) <: e -> Number
(define-object (eval-add <: meta)
  [(self 'eval (list 'add l r)) = (+ (self 'eval l) (self 'eval r))])

;; eval-mul : (list 'mul e e) <: e -> Number
(define eval-mul
  (object [(self 'eval (list 'mul l r)) = (* (self 'eval l) (self 'eval r))]))

(define eval-arith
  (eval-num 'compose eval-add eval-mul))

(define-object
  [(eval-sub 'eval (list 'sub l r)) = (- (eval-sub 'eval l) (eval-sub 'eval r))])

(define eval-arith+sub
  (eval-arith 'compose eval-sub))

;; eval-arith : (list 'num Number) -> Number
;;            & (list 'add e e) <: e -> Number
;;            & (list 'mul e e) <: e -> Number

;; eval-arith : ((list 'num Number) | (list 'add e e) | (list 'mul e e)) <: e -> Number

;; eval-arith : Expr -> Number

(eval-arith 'eval expr1)

(eval-arith+sub 'eval (list 'sub expr1 '(num 1)))

;; TODO: Figure out how types work with composition and partial objects that handle only a specific subset of cases, especially with recursive types like Expr


;; Expr = ...
;;      | (list 'var Symbol)

;; expr2 : Expr
(define expr2 '(add (var x) (mul (num 3) (var y))))

;; env-xy : Symbol |-> Number
(define env-xy '((x . 10) (y . 20)))

;; eval-var : ((Symbol |-> Number), (list 'var Symbol)) -> Number
(define-object
  [(eval-var 'eval env (list 'var x)) = (dict-ref env x)])

(define eval-alg-wrong
  (eval-arith 'compose eval-var))

(define (fix-environment evaluator env)
  (object
   [(_ 'eval expr) = (evaluator 'eval env expr)]))

(define (fix-environment* evaluator-ext env)
  (object
   [(_ 'eval expr) (try-apply-forget evaluator-ext 'eval env expr)]))

(define-object eval-alg
  [(_ 'eval env expr)
   =
   (((fix-environment* (eval-var 'unplug) env) 'compose eval-arith)
    ' eval expr)])

(eval-alg 'eval env-xy '(var y))

(eval-alg 'eval env-xy expr1)

(eval-alg 'eval env-xy expr2)

(define (with-environment eval-ext)
  (object
   [(self 'eval env expr)
    (with-self
        (override-λ* self
         [(_ 'eval sub-expr) = (self 'eval env sub-expr)])
      (try-apply-forget eval-ext 'eval expr))]))

(define eval-alg*
  ((with-environment (eval-arith 'unplug)) 'compose eval-var))

(eval-alg* 'eval env-xy '(var y))
(eval-alg* 'eval env-xy expr1)
(eval-alg* 'eval env-xy expr2)


(define-object eval-add-safe
  [(eval 'eval (list 'add l r))
   = (eval 'add (eval 'eval l) (eval 'eval r))]
  [(eval 'add x y)
   (try-if (and (number? x) (number? y)))
   = (+ x y)])

(define-object eval-mul-safe
  [(eval 'eval (list 'mul l r))
   = (eval 'mul (eval 'eval l) (eval 'eval r))]
  [(eval 'mul x y)
   (try-if (and (number? x) (number? y)))
   = (* x y)])

(define eval-arith-safe
  (eval-num 'compose eval-add-safe eval-mul-safe))

(eval-arith-safe 'eval expr1)

(define-object
  [(leave-variables 'eval (list 'var x)) = (list 'var x)])

(define (operation? s)
  (or (equal? s 'add) (equal? s 'mul)))

(define-object reform-operations
  [(reform op l r) (try-if (and (operation? op) (number? l))) = (reform op (list 'num l) r)]
  [(reform op l r) (try-if (and (operation? op) (number? r))) = (reform op l (list 'num r))]
  [(reform op l r) (try-if (operation? op))                   = (list op l r)])

(define-object reform-operations*
  [(reform op l r) (try-if (operation? op))
                   (extension
                    [_ (try-if (number? l)) = (reform op (list 'num l) r)]
                    [_ (try-if (number? r)) = (reform op l (list 'num r))]
                    [_                     = (list op l r)])])

(define constant-fold
  (eval-arith-safe 'compose leave-variables reform-operations*))


(define expr3 '(add (add (num 1) (num 1))
                    (mul (var x)
                         (mul (num 2) (add (num 2) (num 3))))))

(constant-fold 'eval expr1)
(constant-fold 'eval expr2)
(constant-fold 'eval expr3)
