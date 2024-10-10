#!r6rs

(import (rnrs)
        (compose))

(define*
  [(map* f xs) do ((map* f) xs)]
  [(map* f) (nest)
    (extension
     [(go '())      do '()]
     [(go (x . xs)) do (cons (f x) (go xs))])])

(define* id*
  [(apply id* args) do args])

(define*
  [(obj x)                                             do x]
  [(obj x y) (try-if (number? x)) (try-if (number? y)) do (+ x y)]
  [(obj f . xs) (try-if (procedure? f))                do (map f xs)]
  [(obj . args)                                        do args])

(define*
  [(fact 0)                      do 1]
  [(fact n) (try-if (number? n)) do (* n (fact (- n 1)))])

(define (double x) (+ x x))

(define (divides x y)
  (= (mod x y) 0))

(define-object (fizz-buzz-wrong extends meta)
  [(_ 'show n) (try-if (divides n 3)) do "fizz"]
  [(_ 'show n) (try-if (divides n 5)) do "buzz"]
  [(_ 'show n)                        do (number->string n)])

(define-object fizz-buzz-both
  [(_ 'show n) (try-if (divides n 3)) (try-if (divides n 5)) do "fizzbuzz"])

(define fizz-buzz
  (fizz-buzz-both 'compose fizz-buzz-wrong))


(define*
  [(zeroes 'head) do 0]
  [(zeroes 'tail) do zeroes])

(define*
  [ ((stutter n) 'head)        do n]
  [(((stutter n) 'tail) 'head) do n]
  [(((stutter n) 'tail) 'tail) do (stutter (+ n 1))])

(define*
  [(takes 0 strm) do (list)]
  [(takes 1 strm) do (list (strm 'head))]
  [(takes n strm) (try-if (number? n))
                  do (cons (strm 'head) (takes (- n 1) (strm 'tail)))])
