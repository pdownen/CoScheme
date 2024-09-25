#lang racket

(require "extend.rkt")

;; Stream a = 'head -> a
;;          & 'tail -> Stream a

;; takes : (Stream a, Nat) -> List a
(define (takes s n)
  (cond [(= n 0) '()]
        [(= n 1) (list (s 'head))]
        [else (cons (s 'head) (takes (s 'tail) (- n 1)))]))

;; drops : (Stream a, Nat) -> Stream a
(define (drops s n)
  (cond [(= n 0) s]
        [else (drops (s 'tail) (- n 1))]))

;; index : (Stream a, Nat) -> a
(define (index s n) ((drops s n) 'head))

(define*
  [(zeroes 'head) 0]
  [(zeroes 'tail) zeroes])

(define*
  [ ((stutter n) 'head)        n]
  [(((stutter n) 'tail) 'head) n]
  [(((stutter n) 'tail) 'tail) (stutter (+ n 1))])

(define eval-num
  (λ* [(eval (list 'num n))
       (begin
         (printf "found a number: (eval '(num ~a)) = ~a~n" n n)
         n)]))

(define eval-add
  (λ* [(eval (list 'add l r))
       (begin
         (printf "adding two sub-expressions: ~a, ~a~n" l r)
         (define n (eval l))
         (printf "Result of left sub-expression: (eval '~a) = ~a~n" l n)
         (define m (eval r))
         (printf "Result of right sub-expression: (eval '~a) = ~a~n" r m)
         (printf "Returning (eval '(add ~a ~a)) = ~a~n" l r (+ n m))
         (+ n m))]))

(define eval-mul
  (λ* [(eval (list 'mul l r))
       (begin (printf "multiplying two sub-expressions: ~a, ~a~n" l r)
              (define n (eval l))
              (printf "Result of left sub-expression: (eval '~a) = ~a~n" l n)
              (define m (eval r))
              (printf "Result of right sub-expression: (eval '~a) = ~a~n" r m)
              (printf "Returning (eval '(mul ~a ~a)) = ~a~n" l r (* n m))
              (* n m))]))

(define eval-arith (eval-num 'compose eval-add eval-mul))

(define eval-var
  (λ* [(eval (list 'var x) env)
       (begin
         (printf "looking up variable ~a in environment ~a~n" x env)
         (define n (dict-ref env x))
         (printf "Returning (eval '(var ~a) ~a) = ~a~n" x env n)
         n)]))

(define (with-environment evaluator)
  (λ* [((self => resume-outer-cases) exp env)
       ((λ* [(_ ==> continue-with-new-self)
             (begin
               (printf "hiding environment ~a to evaluate ~a~n" env exp)
               (continue-with-new-self (λ(sub-exp) (self sub-exp env))))]
            [import
             (begin
               (printf "running environment-free evaluator~n")
               evaluator)]
            [(_ exp)
             (begin
               (printf "revealing environment ~a to evaluate ~a~n" env exp)
               ((resume-outer-cases) exp env))])
        exp)]))

(define eval-alg (eval-var 'compose (with-environment (eval-arith 'unplug))))

(eval-alg '(var y) '((x . 1) (y . 2)))

(eval-alg '(add (var x) (mul (num 3) (var y))) '((x . 1) (y . 2)))


(define eval-add-safe
  (λ* [(eval (list 'add l r)) (eval 'add (eval l) (eval r))]
      [(eval 'add (? number? x) (? number? y)) (+ x y)]))

(define eval-mul-safe
  (λ* [(eval (list 'mul l r)) (eval 'mul (eval l) (eval r))]
      [(eval 'mul (? number? x) (? number? y)) (* x y)]))

(define eval-arith-safe (eval-num 'compose eval-add-safe eval-mul-safe))

(eval-arith-safe '(add (num 2) (mul (num 3) (num 4))))

(define leave-variables
  (λ* [(_ (list 'var x)) (list 'var x)]))

(define (operation? s) (or (equal? s 'add) (equal? s 'mul)))

(define reform-operations
  (λ* [(reform (? operation? op) (? number? l) r) (reform op (list 'num l) r)]
      [(reform (? operation? op) l (? number? r)) (reform op l (list 'num r))]
      [(reform (? operation? op) (? list? l) (? list? r)) (list op l r)]))

(define constant-fold (eval-arith-safe 'compose leave-variables reform-operations))

(constant-fold '(add (add (num 1) (num 1)) (mul (var x) (mul (num 2) (add (num 1) (num 1))))))

