#lang racket

(require "extend.rkt")


;; List a = (cons a (List a)) | null

;; Stream a = 'head -> a
;;          & 'tail -> Stream a

;; takes : (Stream a, Nat) -> List a
(define*
  [(takes s 0) null]
  [(takes s 1) (list (s 'head))]
  [(takes s n) (cons (s 'head)
                     (takes (s 'tail) (- n 1)))])

;; drops : (Stream a, Nat) -> Stream a
(define*
  [(drops s 0) s]
  [(drops s n) (drops (s 'tail) (- n 1))])

;; index : (Stream a, Nat) -> a
(define (index s n) ((drops s n) 'head))

;; zeroes : Stream 0
(define*
  [(zeroes 'head) 0]
  [(zeroes 'tail) zeroes])

;; count : Nat -> Stream Nat
(define*
  [((count n) 'head) n]
  [((count n) 'tail) (count (+ n 1))])

;; stutter : Stream Nat
(define*
  [ ((stutter n) 'head)        n]
  [(((stutter n) 'tail) 'head) n]
  [(((stutter n) 'tail) 'tail) (stutter (+ n 1))])

;; always : a -> Stream a
(define*
  [((always x) 'head) x]
  [((always x) 'tail) (always x)])

;; maps : ((a -> b), Stream a) -> Stream b
(define*
  [((maps f xs) 'head) (f (xs 'head))]
  [((maps f xs) 'tail) (maps f (xs 'tail))])

;; iterate : ((a -> a), a) -> Stream a
(define*
  [((iterate f x) 'head) x]
  [((iterate f x) 'tail) (iterate f (f x))])

(define nats (iterate (λ(x) (+ x 1)) 0))
(define squares (maps (λ(x) (* x x)) nats))

;; zigzag : (Stream a, Stream a) -> Stream a
(define*
  [ ((zigzag xs ys) 'head)        (xs 'head)]
  [(((zigzag xs ys) 'tail) 'head) (ys 'head)]
  [(((zigzag xs ys) 'tail) 'tail)
   (zigzag (xs 'tail) (ys 'tail))])

;; evens : Stream a -> Stream a
;; odds  : Stream a -> Stream a
(define*
  [((evens xs) 'head) (xs 'head)]
  [((evens xs) 'tail) (odds (xs 'tail))])

(define (odds xs) (evens (xs 'tail)))



;; Composable evaluation

;; Expr = (list 'num Number)
;;      | (list 'add Expr Expr)
;;      | (list 'mul Expr Expr)

(define expr1 '(add (mul (num 2) (num 3)) (num 4)))

;; expr? : Any -> Bool
(define*
  [(expr? (list 'num n))   (number? n)]
  [(expr? (list 'add l r)) (and (expr? l) (expr? r))]
  [(expr? (list 'mul l r)) (and (expr? l) (expr? r))]
  [(expr? _)               false])

;; eval : Expr -> Number
(define*
  [(eval (list 'num n))   n]
  [(eval (list 'add l r)) (+ (eval l) (eval r))]
  [(eval (list 'mul l r)) (* (eval l) (eval r))])

;; eval* : Expr -> Number
(define eval*
  (λ* [(eval (list 'num n)) n]
      [(eval (list 'add l r)) (+ (eval l) (eval r))]
      [(eval (list 'mul l r)) (* (eval l) (eval r))]))


(define*
  [(list-nums (list 'num n)) (list n)]
  [(list-nums (list 'add l r))
   (append (list-nums l) (list-nums r))]
  [(list-nums (list 'mul l r))
   (append (list-nums l) (list-nums r))])

(define list-nums+sub
  (list-nums
   'compose
   (λ* [(self (list 'sub l r)) (append (self l) (self r))])))


;; eval-num : (list 'num Number) -> Number
(define*
  [(eval-num (list 'num n)) n])

;; eval-add : (list 'add e e) <: e -> Number
(define* (eval-add :> meta)
  [(self (list 'add l r)) (+ (self l) (self r))])

;; eval-mul : (list 'mul e e) <: e -> Number
(define eval-mul
  (λ* [(self (list 'mul l r)) (* (self l) (self r))]))

(define*
  [(eval-sub (list 'sub l r)) (- (eval-sub l) (eval-sub r))])

(define eval-arith
  (eval-num 'compose eval-add eval-mul))

(define eval-arith+sub
  (eval-arith 'compose eval-sub))
;; eval-arith : (list 'num Number) -> Number
;;            & (list 'add e e) <: e -> Number
;;            & (list 'mul e e) <: e -> Number

;; eval-arith : ((list 'num Number) | (list 'add e e) | (list 'mul e e)) <: e -> Number

;; eval-arith : Expr -> Number

(eval-arith expr1)

;; TODO: Figure out how types work with composition and partial objects that handle only a specific subset of cases, especially with recursive types like Expr



;; Expr = ...
;;      | (list 'var Symbol)

;; expr2 : Expr
(define expr2 '(add (var x) (mul (num 3) (var y))))

;; env-xy : Symbol |-> Number
(define env-xy '((x . 10) (y . 20)))

;; eval-var : ((list 'var Symbol), (Symbol |-> Number)) -> Number
(define*
  [(eval-var (list 'var x) env) (dict-ref env x)])

(define eval-alg-wrong
  (eval-arith 'compose eval-var))





(define (with-environment evaluator)
  (λ* [((self => resume-outer-cases) exp env)
       ((λ* [(_ ==> continue-with-new-self)
             (continue-with-new-self (λ(sub-exp) (self sub-exp env)))]
            [import evaluator]
            [(_ exp) ((resume-outer-cases) exp env)])
        exp)]))



;; TODO: Can the resumption code be more automatic, to implicitly fall through on failure automatically?

(define eval-alg
  ((with-environment (eval-arith 'unplug)) 'compose eval-var))

(eval-alg '(var y) env-xy)

(eval-alg expr2 env-xy)



(define* (eval-add-safe)
  [(eval (list 'add l r))
   (eval 'add (eval l) (eval r))]
  [(eval 'add (? number? x) (? number? y))
   (+ x y)])

(define* (eval-mul-safe)
  [(eval (list 'mul l r))
   (eval 'mul (eval l) (eval r))]
  [(eval 'mul (? number? x) (? number? y))
   (* x y)])

(define eval-arith-safe
  (eval-num 'compose eval-add-safe eval-mul-safe))

(eval-arith-safe expr1)

(define*
  [(leave-variables (list 'var x)) (list 'var x)])

(define (operation? s) (or (equal? s 'add) (equal? s 'mul)))

(define* (reform-operations)
  [(reform (? operation? op) (? number? l) r) (reform op (list 'num l) r)]
  [(reform (? operation? op) l (? number? r)) (reform op l (list 'num r))]
  [(reform (? operation? op) l r)             (list op l r)])

(define constant-fold
  (eval-arith-safe 'compose leave-variables reform-operations))

;; TODO: Types?!?!

(define expr3 '(add (add (num 1) (num 1))
                    (mul (var x)
                         (mul (num 2) (add (num 2) (num 3))))))

(constant-fold expr3)
