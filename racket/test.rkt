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
 
 (define-object (fizz-buzz-wrong !<: meta)
   [(_ 'show n) (try-if (divides n 3)) = "fizz"]
   [(_ 'show n) (try-if (divides n 5)) = "buzz"]
   [(_ 'show n)                        = (number->string n)])

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

(define*
  [((zips-with f xs ys) 'head) = (f (xs 'head) (ys 'head))]
  [((zips-with f xs ys) 'tail) = (zips-with f (xs 'tail) (ys 'tail))])

(define*
  [ (fibs 'head)        = 0]
  [((fibs 'tail) 'head) = 1]
  [((fibs 'tail) 'tail) = (zips-with + fibs (fibs 'tail))])

(define* queue
  [ (self 'new)            = (self '() '())]
  [((self in  out) 'enq x) = (self (cons x in) out)]
  [((self '() '()) 'deq)   = (error "Invalid dequeue: empty queue")]
  [((self in  '()) 'deq)   = ((self '() (reverse in)) 'deq)]
  [((self in  out) 'deq)   = (cons (car out) (self in (cdr out)))])

(define ((import-object super-obj) sub-ext)
  (compose sub-ext (super-obj 'unplug)))

(define (construct state obj)
  (extension
   [self try (with-self
                 (λ args (apply (apply self state) args))
               (obj 'unplug))]))

(define-object
  [((fs-object p . _) 'path) = p])

(define-object (file* <: (import-object fs-object))
  [((file p txt) 'text) = txt]
  [((file p txt) 'size) = (string-length ((file p txt) 'text))])

(define-object (directory* <: (import-object fs-object))
  [((apply dir p cts) 'contents) = cts]
  [((apply dir p cts) 'overhead) = 8]
  [((apply dir p cts) 'size)
   = (apply +
            ((apply dir p cts) 'overhead)
            (map (λ(o) (o 'size)) ((apply dir p cts) 'contents)))])

(define-object (<: (import-object fs-object))
  [(file p txt) (construct (list p txt))
   (object
    [(self 'text) = txt]
    [(self 'size) = (string-length (self 'text))])])

(define-object (directory <: (import-object fs-object))
  [(apply dir p cts) (construct (cons p cts))
   (object
    [(self 'contents) = cts]
    [(self 'overhead) = 8]
    [(self 'size)
     = (apply +
              (self 'overhead)
              (map (λ(o) (o 'size)) (self 'contents)))])])

(define-object (fancy-directory <: (import-object directory))
  [((fancy-dir p . cts) 'overhead) = 128])

(define-object (<: (import-object file))
  [(static-link p lnk) (construct (list p lnk))
   (object
    [(_ 'link) = lnk]
    [(_ 'text) = "..."]
    [(_ 'size) = 8])])

(define ham (file "hamlet.txt" "Words, words, words...."))
(define guide (file "guide.txt" "Don't Panic"))
(define books (directory* "Books" ham guide))
(define shortcut (static-link "shortcut.txt" "Books/guide.txt"))
(define docs (fancy-directory "Documents" shortcut books))