#!r6rs

(library (compose)

(export define* lambda* override-lambda* define-object object <: extends meta
        extension apply-extension template apply-template
        chain nest comatch try always-do try-if try-match
        try-lambda try-case-lambda try-match-lambda try-apply-remember try-apply-forget
        empty-extension empty-template choose commit merge
        introspect plug closed-cases selfless with-self self-modify)

(import (rnrs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hierarchy of Abstraction ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Codata = Base case

;; Codata is a domain-specific object like:   Stream a = 'head -> a & 'tail -> Stream a

;; Template = Codata -> Codata

;; The argument of a template fills in the "self" pointer (late binding), and the returned codata object says what to do in specific cases. More generally, you might imagine that a template takes a partially-formed "self" object and defines behavior for additional cases, in this case you would have

;; Tempalte = Codata -> Codata'

;; where the type "Codata" describes the old self and Codata' describes the new self.

;; Extension = Template -> Template'
;; Extension = Template -> Codata -> Codata'

;; An Extension takes a Template and extends it with more cases. It is important to use a Template parameter without an unbound "self" rather than a base Codata type, because this Extension will add more cases of behavior, and the beginning Template should be able to learn and use this extended behavior any time it wants to recurse in on itself. This is what makes it possible for an earlier case of an object to recurse on itself in a way that uses a later case added "afterward" by an Extension.

;; You can view an Extension as a transformation from a Template (an Codata object that does not yet know itself) and a future version of itself (which may be extended further still beyond this point) into the final Codata type object.


;; empty-extension : Extension
;; don't change anything
(define (empty-extension next) next)

;; empty-template : Template
;; nothing is defined
(define (empty-template self) (raise (cons 'comatch self)))

;; empty-object : Codata
;; I don't exist
(define empty-object (lambda args (raise (cons 'empty-object args))))

;; extend-template : Extension -> Template -> Template
;; add more methods to a Template, and override any duplicates, but avoid fixing its "self" to allow for future extensions
(define (extend-template ext next) (ext next))

;; surround-object : Template -> Codata -> Codata
;; introduce new behvaior around a Codata object, only using that object when the Template recurses in on itself.
(define (surround-object tmpl obj) (tmpl obj))

;; handle-with : Template -> Extension -> Template
;; handle all the cases where the extension falls through by continuing on with the given handler.
(define (handle-with handler ext) (ext handler))

;; resume-as : Codata -> Template -> Codata
;; run a template 
(define (resume-as self tmpl) (tmpl self))

;; Extension composition is just ordinary function composition

;; introspect : Template -> Codata
;; know thyself
(define (introspect tmpl)
  (letrec [(self (tmpl (lambda args (apply self args))))]
    self))

;; selfless : Template -> Codata
;; doesn't care about itself
(define (selfless tmpl) (tmpl empty-object))

;; closed-cases : Extension -> Template
;; closes off an open-ended extension to get a template with a fixed number of cases by terminating the sequence of potential copattern match with a failure.
(define (closed-cases ext) (ext empty-template))

;; plug : Extension -> Codata
;; plug an open-ended extension to get a usable object of the expected Codata type. First, extend the empty base template to close off the possibility of future extensions, and then plug in itself for its "self" to enable recursion
(define (plug ext) (introspect (closed-cases ext)))

;; choose : Template -> Extension
;; make an extension which definitively chooses this template and ignores all remaining copattern-matching alternatives
(define (choose tmpl) (lambda (next) tmpl))

;; commit : Value -> Extension
;; commit to a final answer in the middle of copattern matching by throwing away the remaining possibilities that could be tried.
(define (commit value) (choose (selfless value)))

;; merge : (Extension ...) -> Extension
;; merge any number of extensions into a single one that chooses between the matching alternative based on the context of its call-site.
(define (merge . exts)
  (cond
    [(for-all procedure? exts)
     (lambda(self)
       (letrec ([apply-all
                 (lambda (exts self)
                   (cond [(null? exts) self]
                         [(pair? exts) ((car exts) (apply-all (cdr exts) self))]))])
         (apply-all exts self)))]
    [else (raise (cons 'merge exts))]))

(define (self-modify new-self ext)
  (try next old-self (apply-extension ext next new-self)))

(define (with-self new-self ext)
  (try next old-self (apply-extension ext (non-rec (next old-self)) new-self)))

(define (nest ext)
  (try next there
   (letrec ([here (apply-extension
                   ext
                   (non-rec (next there))
                   (lambda args (apply here args)))])
     here)))


;;;;;;;;;;;;;;;;;;;;;;;
;; Small-step macros ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Extensions may fail, in which case they fall through to the base case which will be provided later (as their first argument). This way, extensions let us represent potentially-failing operations as first-class values that compose with other extensions explaining what to do in the failure case. Each operation is a single step that tries to do one thing: if it succeeds, it continues to the next step in the chain, but if it fails, it falls through to the provided base case.

;; While we would ideally want to abstract out the success case as well, some of these operations will bind some variables to be used in the success case, so they need to be macros to allow for binding variables in function parameters or patterns. 

(define-syntax define-syntax-rule
  (syntax-rules ()
    [(define-syntax-rule (name . pattern) template)
     (define-syntax name
       (syntax-rules ()
         [(name . pattern) template]))]))

(define-syntax try
  (syntax-rules ()
    [(try ext)
     ext]
    [(try next tmpl)
     (lambda(next) tmpl)]
    [(try next self expr)
     (lambda(next) (lambda(self) expr))]))

(define-syntax-rule
  (always-do expr)
  (try _ _ expr))

(define-syntax continue
  (syntax-rules ()
    [(continue tmpl)
     tmpl]
    [(continue self expr)
     (lambda(self) expr)]))

(define-syntax-rule
  (non-rec expr)
  (continue _ expr))

(define-syntax-rule
  (apply-template tmpl self)
  (tmpl self))

(define-syntax-rule
  (apply-extension ext next self)
  ((ext next) self))

;; try-if : Bool -> Extension -> Extension
;; Test the given boolean expression: if it is true, run the given extension, and if it is false, fall through to the next option.  To ensure a predictable evaluation order, this is defined as a macro so that the expression which returns the success extension only runs when the check is true.
(define-syntax-rule
  (try-if check ext)
  (try next self
       (if check
           (apply-extension ext next self)
           (apply-template next self))))

(define-syntax-rule
  (try-let ([name expr] ...) ext)
  (try next self
       (let ([name expr] ...) (apply-extension ext next self))))

;; try-match : Expr -> Pattern -> Extension -> Extension
;; Attempt to match the given expression against the pattern: if the match is successful, run the given extension under the pattern's bindings, and the match fails, fall through to the next option.
(define-syntax try-match
  (lambda(stx)
    (syntax-case stx (quote)
      [(try-match expr #t ext)
       #'(try-if expr ext)]
      [(try-matchexpr #f ext)
       #'(try-if (not expr) ext)]
      [(try-match expr lit ext)
       (let ([raw (syntax->datum #'lit)])
         (or (number? raw)
             (char? raw)
             (string? raw)))
       #'(try-if (eq? lit expr) ext)]
      [(try-match expr name ext)
       (identifier? #'name)
       #'(try-let ([name expr]) ext)]
      [(try-match expr (quote sexp) ext)
       #'(try-if (equal? (quote sexp) expr) ext)]
      [(try-match expr () ext)
       #'(try-if (null? expr) ext)]
      [(try-match expr (pat1 . pats) ext)
       #'(try next self
              (let ([val expr])
                (try-match-inline val (pat1 . pats) ext)))])))

(define-syntax try-match-inline
  (lambda(stx)
    (syntax-case stx (quote)
      [(try-match-inline val (quote sexp) ext)
       #'(try-if (equal? (quote sexp) val) ext)]
      [(try-match-inline val (pat1 . pats) ext)
       #'(try-if
          (pair? val)
          (try-let ([first (car val)]
                    [rest (cdr val)])
            (try-match-inline first pat1 (try-match-inline rest pats ext))))]
      [(try-match-inline val pat ext)
       #'(try-match val pat ext)])))

(define-syntax try-match*
  (syntax-rules ()
    [(try-match* () () ext)
     ext]
    [(try-match* (exp1 . exps) (pat1 . pats) ext)
     (try-match exp1 pat1 (try-match* exps pats ext))]
    [(try-match* exp pat ext)
     (try-match exp pat ext)]))

;; try-case-lambda : Formals -> Extension -> Extension
;; Attempt to be a lambda that binds the given parameters: if the correct number of arguments are applied, run the given extension with the parameters bound to the arguments, and otherwise fall through to the next option. Note that the form (try-lambda rest-id ext) accepts any number of arguments, so it always succeeds.
(define-syntax try-case-lambda
  (lambda(stx)
    (syntax-case stx ()
      [(try-case-lambda rest-id ext)
       (identifier? #'rest-id)
       #'(try next self
              (lambda rest-id
                (apply-extension
                 ext
                 (lambda(self) (apply (apply-template next self) rest-id))
                 self)))]
      [(try-case-lambda (arg-id ...) ext)
       (for-all symbol? (syntax->datum #'(arg-id ...)))
       #'(try next self
              (case-lambda
                [(arg-id ...)
                 (apply-extension
                  ext
                  (lambda(self) ((apply-template next self) arg-id ...))
                  self)]
                [args (apply (apply-template next self) args)]))]
      [(try-case-lambda (arg-id ... . rest-id) ext)
       (for-all symbol? (syntax->datum #'(arg-id ... rest-id)))
       #'(try next self
              (case-lambda
                [(arg-id ... . rest-id)
                 (apply-extension
                  ext
                  (lambda(self) (apply (apply-template next self) arg-id ... rest-id))
                  self)]
                [args (apply (apply-template next self) args)]))])))

;; try-match-lambda : Patterns -> Extension -> Extension
;; Attempt to be a lambda that matches its arguments against the given patterns: if the number and shape of the arguments fits the pattern list, then run the given success extension under the bindings introduced by the patterns, and otherwise fall through to the next option.
(define-syntax try-match-lambda
  (lambda(stx)
    (syntax-case stx ()
      [(try-match-lambda (arg-id ...) (name . pats) ext)
       (identifier? #'name)
       #'(try-match-lambda (arg-id ... name) pats ext)]
      [(try-match-lambda (arg-id ...) (pat1 . pats) ext)
       #'(try-match-lambda (arg-id ... arg) pats (try-match-inline arg pat1 ext))]
      [(try-match-lambda named-args () ext)
       #'(try-case-lambda named-args ext)]
      [(try-match-lambda (arg-id ...) rest-id ext)
       (identifier? #'rest-id)
       #'(try-case-lambda (arg-id ... . rest-id) ext)]
      [(try-match-lambda pattern-args ext)
       #'(try-match-lambda () pattern-args ext)])))

;; try-lambda : Formals/Patterns -> Extension -> Extension
;; Automatically figure out the form of the given named or matched parameters use the correct form of trial lambda-abstraction.
(define-syntax try-lambda
  (lambda(stx)
    (syntax-case stx ()
      [(try-lambda rest-id ext)
       (identifier? #'rest-id)
       #'(try-case-lambda rest-id ext)]
      [(try-lambda (arg-id ... . end) ext)
       (and (for-all symbol? (syntax->datum #'(arg-id ...)))
            (or (identifier? #'end)
                (null? (syntax->datum #'end))))
       #'(try-case-lambda (arg-id ... . end) ext)]
      [(try-lambda params ext)
       #'(try-match-lambda params ext)])))

(define-syntax try-apply-remember
  (syntax-rules ()
    [(try-apply-remember ext arg ...)
     (try next self
          ((apply-extension-inline ext next self) arg ...))]
    [(try-apply-remember ext arg ... . rest)
     (try next self
          (apply (apply-extension-inline ext next self) arg ... rest))]))

(define-syntax try-apply-forget
  (syntax-rules ()
    [(try-apply-forget ext arg ...)
     (try next self
          ((apply-extension ext (lambda(self) (lambda _ (next self))) self) arg ...))]
    [(try-apply-forget ext arg ... . rest)
     (try next self
          (apply (apply-extension ext (lambda(self) (lambda _ (next self))) self) arg ... rest))]))

;;;;;;;;;;;;;;;;;;;;;
;; Big-step Macros ;;
;;;;;;;;;;;;;;;;;;;;;

;; initial-comatch : Copattern -> Extension -> Extension
;; Expand out the copattern expression of an extension to do copattern-matching.
;; Note: using an initial comatch after some other operations (especially lambda-abstractions) gives access to the *original* "self" of the overall object rather than the view from this point. This could be either intentional or confusing behavior. To properly view the self in a copattern-match after being nested within other operations, use `comatch`.
(define-syntax comatch
  (lambda(stx)
    (syntax-case stx (apply)
      [(comatch (apply copat args) ext)
       (identifier? #'args)
       #'(comatch copat (try-case-lambda args ext))]
      [(comatch (apply copat arg1 arg ... rest) ext)
       #'(comatch copat (try-lambda(arg ... . rest) ext))]
      [(comatch (copat arg ... . end) ext)
       #'(comatch copat (try-lambda(arg ... . end) ext))]
      [(comatch underscore ext)
       (eq? '_ (syntax->datum #'underscore))
       #'ext]
      [(comatch name ext)
       (identifier? #'name)
       #'(try next name (apply-extension ext next name))])))


(define-syntax chain
  (syntax-rules (= do try)
    [(chain (op ...) step ... ext)
     (op ... (chain step ... ext))]
    [(chain do expr)
     (always-do expr)]
    [(chain = expr)
     (always-do expr)]
    [(chain try ext)
     ext]
    [(chain ext)
     ext]))


(define-syntax-rule
  (extension [copat step ...] ...)
  (merge [chain (comatch copat) step ...] ...))

(define-syntax template
  (syntax-rules (continue else)
    [(template clause ... [continue . default])
     ((extension clause ...) (continue . default))]
    [(template clause ... [else default])
     ((extension clause ...) (non-rec default))]
    [(template clause ...)
     (closed-cases (extension clause ...))]))


;;;;;;;;;;;;;;;;;;;;;;
;; Meta Programming ;;
;;;;;;;;;;;;;;;;;;;;;;

;; unplug : Extension -> Extension
;; The 'unplug method remembers an extension, so you can ask the object for it later
(define (unplug ext)
  (extension
   [(self 'unplug) do ext]))

;; adapt : Extension; depends on 'unplug
;; The 'adapt method lets you apply a (Extension -> Extension) modifier to the Extension you get by "unplug"ging the object itself, and then re-"plug"s the modified Extension again.
(define adapt
  (extension
   [(self 'adapt mod) do (plug (meta (mod (self 'unplug))))]))

;; composition : Extension; depends on 'unplug
;; The 'compose method lets you pass in a list of other objects (which can all be "unplug"ged) and combines them together into a single object that shares all their behavior. Precedence of overlapping methods is resolved left-to-right, starting from this object itself, and then proceeding through each one of the arguments from first to last.
(define composition
  (extension
   [(self 'compose)      do self]
   [(self 'compose . os) do (plug (meta (apply merge
                                               (self 'unplug)
                                               (map (lambda(o) (o 'unplug)) os))))]))

;; meta : Extension -> Extension
;; Combines the 'unplug, 'adapt, and 'compose methods above with the methods of the given extension itself
(define (meta ext) (merge ext (unplug ext) composition adapt))

(define default-object-modifier meta)

;;;;;;;;;;;;;;;;;
;; Main Macros ;;
;;;;;;;;;;;;;;;;;

(define-syntax-rule
  (lambda* clause ...)
  (introspect (template clause ...)))

(define-syntax-rule
  (override-lambda* old clause ...)
  (lambda* clause ... [else old]))

(define-syntax define*
  (lambda(stx)
    (syntax-case stx (apply)
      [(define* [(apply copat args) step ...] clause ...)
       (identifier? #'args)
       #'(define* [copat (try-case-lambda args) step ...] clause ...)]
      [(define* [(apply copat arg1 arg ... args) step ...] clause ...)
       #'(define* [copat (try-lambda arg1 arg ... args) step ...] clause ...)]
      [(define* [(copat arg ... . end) step ...] clause ...)
       #'(define* [copat (try-lambda(arg ... . end)) step ...] clause ...)]
      [(define* [name step ...] clause ...)
       (identifier? #'name)
       #'(define name (lambda* [name step ...] clause ...))]
      [(define* name clause ...)
       (identifier? #'name)
       #'(define name (lambda* clause ...))])))

(define-syntax extends
  (syntax-rules ()))

(define-syntax <:
  (syntax-rules ()))

(define-syntax object
  (syntax-rules (extends <:)
    [(object (<: mod) clause ...)
     (plug (mod (extension clause ...)))]
    [(object (<: mod ...) clause ...)
     (plug (compose (mod ...) (extension clause ...)))]
    [(object (extends mod ...) clause ...)
     (object (<: mod ...) clause ...)]
    [(object clause ...)
     (plug (default-object-modifier (extension clause ...)))]))

(define-syntax define-object
  (lambda(stx)
    (syntax-case stx (extends <: apply)
      [(define-object (<: mod ...) [(apply copat arg1 arg ... args) step ...] clause ...)
       #'(define-object (<: mod ...) [copat (try-lambda arg1 arg ... args) step ...] clause ...)]
      [(define-object (<: mod ...) [(apply copat args) step ...] clause ...)
       (identifier? #'args)
       #'(define-object (<: mod ...) [copat (try-case-lambda args) step ...] clause ...)]
      [(define-object (<: mod ...) [(copat arg ... . end) step ...] clause ...)
       #'(define-object (<: mod ...) [copat (try-lambda(arg ... . end)) step ...] clause ...)]
      [(define-object (<: mod ...) [name step ...] clause ...)
       (identifier? #'name)
       #'(define-object (name <: mod ...) [name step ...] clause ...)]
      [(define-object (name <: mod ...) clause ...)
       (identifier? #'name)
       #'(define name (object (<: mod ...) clause ...))]
      [(define-object (extends mod ...) clause ...)
       #'(define-object (<: mod ...) clause ...)]
      [(define-object (name extends mod ...) clause ...)
       (identifier? #'name)
       #'(define-object (name <: mod ...) clause ...)]
      [(define-object name clause ...)
       (identifier? #'name)
       #'(define-object (name extends default-object-modifier) clause ...)]
      [(define-object clause ...)
       #'(define-object (extends default-object-modifier) clause ...)])))

)