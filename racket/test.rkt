#lang racket

(require "composable.rkt")

(define*
  [(away-from0 x) (try-if (>= x 0)) = (+ x 1)]
  [(away-from0 x) (try-if (<= x 0)) = (- x 1)])

(define*
  [((counter x) 'add y) = (counter (+ x y))]
  [((counter x) 'get)   = x])

(define*
  [(map* f xs) = ((map* f) xs)]
  [(map* f) (nest)
    (extension
     [(go `())         = `()]
     [(go `(,x . ,xs)) = `(,(f x) . ,(go xs))])])

(define* id*
  [(apply id* args) = args])

(define*
  [(obj x)      = x]
  [(obj x y)    (try-if (number? x))
                (try-if (number? y))
                = (+ x y)]
  [(obj f . xs) (try-if (procedure? f))
                = (map f xs)]
  [(obj . args) = args])

(define*
  [(fact 0)                     = 1]
  [(fact n) (try-if (number? n)) = (* n (fact (- n 1)))])

(define (double x) (+ x x))

(define (divides x y)
  (= (modulo x y) 0))

(define-object (fizz-buzz-wrong <: meta)
  [(_ 'show n) (try-if (divides n 3)) = "fizz"]
  [(_ 'show n) (try-if (divides n 5)) = "buzz"]
  [(_ 'show n)                       = (number->string n)])

(define-object fizz-buzz-both
  [(_ 'show n) (try-if (divides n 3)) (try-if (divides n 5)) = "fizzbuzz"])

(define fizz-buzz
  (fizz-buzz-both 'compose fizz-buzz-wrong))


(define*
  [(zeroes 'head) = 0]
  [(zeroes 'tail) = zeroes])

(define*
  [(((stutter n) 'tail) 'tail) = (stutter (+ n 1))]
  [(((stutter n) 'tail) 'head) = n]
  [ ((stutter n) 'head)        = n])

(define*
  [(takes strm 0) = (list)]
  [(takes strm 1) = (list (strm 'head))]
  [(takes strm n) (try-if (number? n))
                  = (cons (strm 'head) (takes (strm 'tail) (- n 1) ))])
