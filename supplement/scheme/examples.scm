#!r6rs

(import (rnrs)
        (composable))

;;;;;;;;;;;;;;;;;;;;;;;
;; Stream processing ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; List a = (cons a (List a)) | null

;; Stream a = 'head -> a
;;          & 'tail -> Stream a

;; takes : (Stream a, Nat) -> List a
;; take a prefix of a stream and return it as a list
(define*
  [(takes s 0) = (list)]
  [(takes s 1) = (list (s 'head))] ; special case for 1 avoids 'tail projection
  [(takes s n) = (cons (s 'head)
                       (takes (s 'tail) (- n 1)))])

;; drops : (Stream a, Nat) -> Stream a
;; drop a prefix of a stream
(define*
  [(drops s 0) = s]
  [(drops s n) = (drops (s 'tail) (- n 1))])

;; index : (Stream a, Nat) -> a
;; return the element of a stream at the given index
(define (index s n) ((drops s n) 'head))

;; zeroes : Stream 0
;; the stream of all 0s
(define*
  [(zeroes 'head) = 0]
  [(zeroes 'tail) = zeroes])
;; zeroes = (stream 0 0 0 0 0 ...)

;; count : Nat -> Stream Nat
;; a stream that counts numbers starting from the given one
(define*
  [((count n) 'head) = n]
  [((count n) 'tail) = (count (+ n 1))])
;; (count n) = (stream n (+ n 1) (+ n 2) (+ n 3) ...)

;; stutter : Stream Nat
;; like count, but repeats each number twice before moving on
(define*
  [ ((stutter n) 'head)        = n]
  [(((stutter n) 'tail) 'head) = n]
  [(((stutter n) 'tail) 'tail) = (stutter (+ n 1))])
;; (stutter n) = (stream n n (+ n 1) (+ n 1) (+ n 2) (+ n 2) ...)

;; always : a -> Stream a
;; the stream that is always repeats the same given value
(define*
  [((always x) 'head) = x]
  [((always x) 'tail) = (always x)])
;; (always x) = (stream x x x x x ...)

;; maps : ((a -> b), Stream a) -> Stream b
;; modify all the elements of a stream by a given function
(define*
  [((maps f xs) 'head) = (f (xs 'head))]
  [((maps f xs) 'tail) = (maps f (xs 'tail))])
;; (maps f (stream x1 x2 x3 ...)) = (stream (f x1) (f x2) (f x3) ...)

;; iterate : ((a -> a), a) -> Stream a
;; generate a stream by iterating the given function over and over on the starting element
(define*
  [((iterate f x) 'head) = x]
  [((iterate f x) 'tail) = (iterate f (f x))])
;; (iterate f x) = (stream x (f x) (f (f x)) (f (f (f x))) ...)

;; nats, squares : Stream Nat
(define nats (iterate (lambda(x) (+ x 1)) 0))
;; nats = (stream 0 1 2 3 4 5 ...)
(define squares (maps (lambda(x) (* x x)) nats))
;; squares = (stream 0 1 4 9 16 25 ...)

;; zigzag : (Stream a, Stream a) -> Stream a
(define*
  [ ((zigzag xs ys) 'head)        = (xs 'head)]
  [(((zigzag xs ys) 'tail) 'head) = (ys 'head)]
  [(((zigzag xs ys) 'tail) 'tail) = (zigzag (xs 'tail) (ys 'tail))])
;; (zigzag (stream x1 x2 x3 ...) (stream y1 y2 y3))
;; = (stream x1 y1 x2 y2 x3 y3 ...

;; evens : Stream a -> Stream a
;; odds  : Stream a -> Stream a
(define*
  [((evens xs) 'head) = (xs 'head)]
  [((evens xs) 'tail) = (odds (xs 'tail))])

(define (odds xs) (evens (xs 'tail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Composable evaluation ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expr = `(num ,Number)
;;      | `(add ,Expr ,Expr)

;; expr0 : Expr
(define expr0 '(add (num 1) (add (num 2) (num 3))))

;; expr? : Any -> Bool
(define*
  [(expr? ('num n))   = (number? n)]
  [(expr? ('add l r)) = (and (expr? l) (expr? r))]
  [(expr? _)          = #f])

;; eval : Expr -> Number
(define*
  [(eval `(num ,n))    = n]
  [(eval `(add ,l ,r)) = (+ (eval l) (eval r))])

;; eval-lam* : Expr -> Number
;; alternative definition via an anonymous λ*
(define eval-lam*
  (lambda*
   [(eval (num n))   = n]
   [(eval ('add l r)) = (+ (eval l) (eval r))]))

;; list-nums : Expr -> List Number
;; return a list of all the numeric literals in an expression
(define* list-nums
  [(self ('num n))   = (list n)]
  [(self ('add l r)) = (append (self l) (self r))])

(expr? expr0)
(eval expr0)
(eval-lam* expr0)
(list-nums expr0)

;; list-nums* : Expr -> List Number
;; same as list-nums, but as an object inheriting extra functionality for composition
(define-object
  [(list-nums* `(num ,n))    = (list n)]
  [(list-nums* `(add ,l ,r)) = (append (list-nums* l) (list-nums* r))])

;; eval* : Expr -> Number
;; same as eval, but now defined as the composition of two separate objects
(define-object
  [(eval-num `(num ,n)) = n])
  
(define-object
  [(eval-add `(add ,l ,r)) = (+ (eval-add l) (eval-add r))])

(define eval* (eval-num 'compose eval-add))

;; Extending arithmetic expressions with multiplication

;; Expr = ... | `(mul ,Expr ,Expr)

;; The extra cases of eval and list-num to handle multiplication

(define-object eval-mul
  [(eval-mul `(mul ,l ,r)) = (* (eval-mul l) (eval-mul r))])

(define-object
  [(list-mul `(mul ,l ,r)) = (append (list-mul l) (list-mul r))])

;; Composing these new cases with the existing code

(define eval-arith
  (eval* 'compose eval-mul))

(define list-nums-arith
  (list-nums* 'compose list-mul))

;; expr1 : Expr
(define expr1 '(add (mul (num 2) (num 3)) (num 4)))

(eval-arith expr1)
(list-nums-arith expr1)

;; Extending arithmetic expressions *again* with subtraction

;; Expr = ... | `(sub ,Expr ,Expr)

;; The extra cases of eval and list-num to handle subtraction

(define-object eval-sub
  [(self ('sub l r)) = (- (self l) (self r))])

(define list-sub
  (object
   [(self `(sub ,l ,r)) = (append (self l) (self r))]))

;; Composing the new cases with the existing code
(define eval-arith+sub
  (eval-arith 'compose eval-sub))

(define list-nums-arith+sub
  (list-nums-arith 'compose list-sub))

;; expr1-sub1 : Expr
(define expr1-sub1 `(sub ,expr1 (num 1)))

(eval-arith+sub expr1-sub1)
(list-nums-arith+sub expr1-sub1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Threading an environment ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Extending expressions with variables

;; Expr = ... | ('var Symbol)

;; expr2 : Expr
(define expr2 '(add (var x) (mul (num 3) (var y))))

;; env-xy : ((Symbol . Number) ...)
(define env-xy '((x . 10) (y . 20)))
  
(define*
  [(lookup ((key1 . val1) . env) key)
   (try-if (eq? key1 key))            = val1]
  [(lookup ((key1 . val1) . env) key) = (lookup env key)])

;; To evaluate a variable, an environment is needed to look up its value
(define-object
  [(eval-var env ('var x)) = (lookup env x)])

;; Directly composing the existing arithmetic evaluator with variable evaluation does not give the desired result, because they expect different numbers of parameters (one wants an environment, one doesn't).
(define eval-alg-wrong
  (eval-arith 'compose eval-var))
;; To correctly compose these mutually-recursive objects, one needs to be modified so they both have the same interface.

;; One way to match the interfaces is to extend the arithmetic evaluator (which only expects an expression) with an environment. The new evaluator will take an extra environment parameter, which is only used to pass along again on recursive calls.
(define (with-environment eval-ext)
  (object
   [(self env expr)
    (with-self
        (override-lambda* self
         [(_ sub-expr) = (self env sub-expr)])
      (try-apply-forget eval-ext expr))]))

;; We can now successfully compose arithmetic and variable evaluation by first "unplugging" the arithmetic evaluator to get the composable extension, and then extending it with an environment.
(define eval-alg
  ((with-environment (eval-arith 'unplug)) 'compose eval-var))

(eval-alg env-xy '(var y))
(eval-alg env-xy expr1)
(eval-alg env-xy expr2)

;; A second way to match the interfaces is to fix the environment up front, when the evaluator first starts, and reuse it at every base case when a variable is encountered.
(define (fix-environment evaluator-ext env)
  (object
   [(_ expr) (try-apply-forget evaluator-ext env expr)]))

;; This time, we can successfully compose arithmetic and variable evaluation by fixing the environment into the variable evaluator so that it only expects an expression argument, and then compose it with the aritmetic evaluator.
(define-object eval-alg*
  [(_ env expr)
   =
   (((fix-environment (eval-var 'unplug) env) 'compose eval-arith)
    expr)])

(eval-alg* env-xy '(var y))
(eval-alg* env-xy expr1)
(eval-alg* env-xy expr2)

;;;;;;;;;;;;;;;;;;;;;;;;
;; Partial evaluation ;;
;;;;;;;;;;;;;;;;;;;;;;;;

;; The arithmetic evaluator might over-commit: if evaluating a sub-expression doesn't return a number, then the arithmetic operation would fail. Instead, the arithmetic operation should only happen if both sub-expression evaluate to numbers.

;; A safer version of addition and multiplication can be defined by first evaluating the two sub-expressions, and then calling a separate 'add or 'mult method which only occurs if both results are numbers.

(define-object eval-add-safe
  [(self ('add l r))
   = (self 'add (self l) (self r))]
  [(self 'add x y)
   (try-if (and (number? x) (number? y)))
   = (+ x y)])

(define-object eval-mul-safe
  [(self ('mul l r))
   = (self 'mul (self l) (self r))]
  [(self 'mul x y)
   (try-if (and (number? x) (number? y)))
   = (* x y)])

(define-object eval-sub-safe
  [(self `(sub ,l ,r))
   = (self 'sub (self l) (self r))]
  [(self 'sub x y)
   (try-if (and (number? x) (number? y)))
   = (- x y)])

(define eval-arith-safe
  (eval-num 'compose eval-add-safe eval-mul-safe eval-sub-safe))

;; The safe version of evaluation works just like before on arithmetic expressions without variables.
(eval-arith-safe expr1)

;; However, it cannot be applied directly to expressions with variables. Instead, we need to compose additional behavior that handles the new base case for variables, and then says how to handle the non-numeric 'add or 'mul cases. We could install code to handle the extra cases in-place as:
((eval-arith-safe
  'compose
  (object [(_ `(var ,x)) = `(var ,x)]
          [(_ 'add x y)  = `(add ,x ,y)]
          [(_ 'mul x y)  = `(mul ,x ,y)]))
 expr2)
;; This is almost what we want, except that the result '(add (var x) (mul 3 (var y))) isn't quite a well-formed expression, since it should contain '(mul (num 3) (var y)) instead of '(mul 3 (var y)).

;; The case for handling variables by just leaving them alone and returning them as-is can be factored out from the above application.
(define-object
  [(leave-variables `(var ,x)) = `(var ,x)])

;; Finally, we want to reform operations as another well-formed Expr tree if one or both of the sub-expressions are not numbers.
(define (operation? s)
  (or (equal? s 'add) (equal? s 'mul) (equal? s 'sub)))

;; If the respective operation op ('add, 'mul, or 'sub) cannot be performed numerically, then at least one argument is not a number. If the other argument *is* a number n, it should be turned back into a well-formed expression `(num ,n). Afterward, the operation should be reformed as a syntax tree `(,op ,l ,r).
(define-object reform-operations
  [(reform op l r) (try-if (and (operation? op) (number? l))) = (reform op `(num ,l) r)]
  [(reform op l r) (try-if (and (operation? op) (number? r))) = (reform op l `(num ,r))]
  [(reform op l r) (try-if (operation? op))                   = (list op l r)])

;; If the respective operation op ('add, 'mul, or 'sub) cannot be performed numerically, then at least one argument is not a number. If the other argument *is* a number n, it should be turned back into a well-formed expression `(num ,n). Afterward, the operation should be reformed as a syntax tree `(,op ,l ,r).
(define-object reform-operations*
  [(reform op l r) (try-if (operation? op))
                   (extension
                    [_ (try-if (number? l)) = (reform op `(num ,l) r)]
                    [_ (try-if (number? r)) = (reform op l `(num ,r))]
                    [_                      = (list op l r)])])

;; Constant folding (i.e., partially evaluating up to operations blocked by variables) can then be composed from the "safe" arithmetic evaluator with handlers to leave variables alone and to reform blocked operations.
(define constant-fold
  (eval-arith-safe 'compose leave-variables reform-operations*))

;; expr3 : Expr
(define expr3 '(add (add (num 1) (num 1))
                    (mul (var x)
                         (mul (num 2) (add (num 2) (num 3))))))

(constant-fold expr1)
(constant-fold expr1-sub1)
(constant-fold expr2)
(constant-fold expr3)
