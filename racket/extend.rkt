#lang racket

(provide extension lambdas λ* define*
         extend introspect meta)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hierarchy of Abstraction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Codata = Base case

;; Codata is a domain-specific object like:   Stream a = 'head -> a & 'tail -> Stream a

;; Template = Codata -> Codata

;; The argument of a template fills in the "self" pointer (late binding), and the returned codata object says what to do in specific cases. More generally, you might imagine that a template takes a partially-formed "self" object and defines behavior for additional cases, in this case you would have

;; Template = Codata -> Codata'

;; where the type "Codata" describes the old self and Codata' describes the new self.

;; Extension = Template -> Template'
;; Extension = Template -> Codata -> Codata'

;; An Extension takes a Template and extends it with more cases. It is important to use a Template parameter without an unbound "self" rather than a base Codata type, because this Extension will add more cases of behavior, and the beginning Template should be able to learn and use this extended behavior any time it wants to recurse in on itself. This is what makes it possible for an earlier case of an object to recurse on itself in a way that uses a later case added "afterward" by an Extension.

;; You can view an Extension as a transformation from a Template (an Codata object that does not yet know itself) and a future version of itself (which may be extended further still beyond this point) into the final Codata type object.


;; empty-extension : Extension
;; don't change anything
(define (empty-extension base) base)

;; empty-base : Template
;; nothing is defined
(define (empty-base self) (error "comatch: no clause matching context"))


;; extend : Extension -> Template -> Template
;; add more methods to a Template, but avoid fixing ones "self" to allow for future extensions
(define (extend extension base) (extension base))

;; Extension composition is just ordinary function composition

;; introspect : Template -> Codata
;; know thyself
(define (introspect template)
  (letrec [(self (template (λ args (apply self args))))]
    self))

;; plug : Extension -> Codata
;; plug an open-ended extension to get a usable object of the expected Codata type. First, extend the empty base template to close off the possibility of future extensions, and then plug in itself for its "self" to enable recursion
(define (plug extend) (introspect (extend empty-base)))


;; The main macro, that defines how to compile the code of an extension into a concrete object (a Template transformer)
(define-syntax extension
  (syntax-rules (try-next-from-here => try-next-with-new-self ==> import <= context)
    [(extension [import ext]) ext]
    [(extension [<= ext]) ext]
    [(extension [(try-next-with-new-self self base) chain ... body])
     (extension [(self ==> base) chain ... body])]
    [(extension [(self ==> base) chain ... body])
     (λ(base) (λ(self) (extend-with-chain [chain ... body] (inline (base self)))))]
    [(extension [(try-next-from-here copat continue) chain ... body])
     (extension [copat (try-next-from-here continue) chain ... body])]
    [(extension [(copat => continue) chain ... body])
     (extension [copat (=> continue) chain ... body])]
    [(extension [(context k copat) chain ... body])
     (extension [copat (context k) chain ... body])]
    [(extension [(copat pats ... . end) chain ... body])
     (extension [copat (pats ... . end) chain ... body])]
    [(extension [self chain ... body])
     (λ(base) (λ(self) (extend-with-chain [chain ... body] (inline (base self)))))]
    [(extension) empty-extension]
    [(extension clause1 clause2 clauses ...)
     (compose (extension clause1) (extension clause2) (extension clauses) ...)]))

;; The special case of an extension with only one branch: there is only one possible shape of context that could match, but it might be distributed over a nested chain of curried function calls that need to be applied one at a time
(define-syntax extend-with-chain
  (syntax-rules (inline try-next-from-here => context)
    [(extend-with-chain [(try-next-from-here continue) chain ... body] base)
     (extend-with-chain [(=> continue) chain ... body] base)]
    [(extend-with-chain [(=> continue) chain ... body] (inline base))
     (let [(continue (λ() base))]
       (extend-with-chain [chain ... body] base))]
    [(extend-with-chain [(=> continue) chain ... body] base)
     (let [(continue (λ() base))]
       (extend-with-chain [chain ... body] continue))]
    [(extend-with-chain [(context k) chain ... body] base)
     (call/cc (λ(k) (extend-with-chain [chain ... body] base)))]
    [(extend-with-chain [(pats ...) chain ... body] (inline base))
     (λ args
       (match args
         [(list pats ...)
          (extend-with-chain [chain ... body] (inline (apply base args)))]
         [_ (apply base args)]))]
    [(extend-with-chain [(pats ... . end) chain ... body] (inline base))
     (λ args
       (match args
         [(list-rest pats ... end)
          (extend-with-chain [chain ... body] (inline (apply base args)))]
         [_ (apply base args)]))]
    [(extend-with-chain [body] base) body]
    [(extend-with-chain chain base-expr)
     ((λ(base) (extend-with-chain chain (inline base))) base-expr)]))

;; unplug : Extension -> Extension
;; The 'unplug method remembers an extension, so you can ask the object for it later
(define (unplug ext)
  (extension
   [(self 'unplug) ext]))

;; adapt : Extension; depends on 'unplug
;; The 'adapt method lets you apply a (Extension -> Extension) modifier to the Extension you get by "unplug"ging the object itself, and then re-"plug"s the modified Extension again.
(define adapt
  (extension
   [(self 'adapt mod) (plug (meta (mod (self 'unplug))))]))

;; composition : Extension; depends on 'unplug
;; The 'compose method lets you pass in a list of other objects (which can all be "unplug"ged) and combines them together into a single object that shares all their behavior. Precedence of overlapping methods is resolved left-to-right, starting from this object itself, and then proceeding through each one of the arguments from first to last.
(define composition
  (extension
   [(self 'compose) self]
   [(self 'compose . os) (plug (meta (apply compose
                                            (self 'unplug)
                                            (map (λ(o) (o 'unplug)) os))))]))

;; meta : Extension -> Extension
;; Combines the 'unplug, 'adapt, and 'compose methods above with the methods of the given extension itself
(define (meta ext) (compose ext (unplug ext) composition adapt))

(define default-extension (make-parameter meta))

;; Syntactic sugar to automatically plug Extensions to get usable Codata objects. The optional ":>" modifier lets you apply mods (of type Extension -> Extension) to the Extension before its plugged. For example, the "meta" modifier remembers the Extension before it was plugged, letting you "unplug" it from the closed-off Codata object to recover the open-ended Extension again; very useful for doing unplanned ad-hoc composition later.
(define-syntax lambdas
  (syntax-rules (modify-extension :>)
    [(lambdas (modify-extension mod) clauses ...) (plug (mod (extension clauses ...)))]
    [(lambdas (:> mod) clauses ...) (plug (mod (extension clauses ...)))]
    [(lambdas clauses ...)
     (lambdas (:> (default-extension)) clauses ...)]))

;; Shorthand λs = lambdas
(define-syntax-rule (λ* clauses ...) (lambdas clauses ...))

;; More syntactic sugar to write a top-level definition via a series of clauses, matched top/left to bottom/right. The name of the defined object is taken from the "self" name in the head of the first clause.
(define-syntax define*
  (syntax-rules (:>)
    [(define* (name :> mod) clauses ...)
     (define name (lambdas (:> mod) clauses ...))]
    [(define* (:> mod) [(copat pats ... . end) chain ... body] clauses ...)
     (define* (:> mod) [copat (pats ... . end) chain ... body] clauses ...)]
    [(define* (:> mod) [name chain ... body] clauses ...)
     (define* (name :> mod) [name chain ... body] clauses ...)]
    [(define* (name) clauses ...)
     (define* (name :> (default-extension)) clauses ...)]
    [(define* clauses ...) (define* (:> (default-extension)) clauses ...)]))

