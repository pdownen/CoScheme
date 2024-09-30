#lang racket

(provide define* λ* override-λ* define-object object meta
         extension apply-extension template apply-template
         chain comatch try always-do guard match-guard
         try-λ try-case-λ try-match-λ try-apply-remember try-apply-forget
         empty-extension empty-template choose commit merge
         introspect plug closed-cases selfless with-self self-modify)

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
(define (empty-template self) (error "comatch: no clause matching context"))

;; extend-template : Extension -> Template -> Template
;; add more methods to a Template, but avoid fixing ones "self" to allow for future extensions
(define (extend-template extension next) (extension next))

;; Extension composition is just ordinary function composition

;; introspect : Template -> Codata
;; know thyself
(define (introspect template)
  (letrec [(self (template (λ args (apply self args))))]
    self))

;; closed-cases : Extension -> Template
;; closes off an open-ended extension to get a template with a fixed number of cases by terminating the sequence of potential copattern match with a failure.
(define (closed-cases extension) (extension empty-template))

;; plug : Extension -> Codata
;; plug an open-ended extension to get a usable object of the expected Codata type. First, extend the empty base template to close off the possibility of future extensions, and then plug in itself for its "self" to enable recursion
(define (plug extension) (introspect (closed-cases extension)))

;; selfless : Value -> Template
;; make a selfless template that returns a final value and does not refer to itself
(define (selfless value) (lambda (self) value))

;; choose : Template -> Extension
;; make an extension which definitively chooses this template and ignores all remaining copattern-matching alternatives
(define (choose template) (lambda (next) template))

;; commit : Value -> Extension
;; commit to a final answer in the middle of copattern matching by throwing away the remaining possibilities that could be tried.
(define (commit value) (choose (selfless value)))

;; merge : (Extension ...) -> Extension
;; merge any number of extensions into a single one that chooses between the matching alternative based on the context of its call-site.
(define merge compose)

(define (with-self new-self ext)
  (try next old-self (apply-extension ext (λ(_) (next old-self)) new-self)))

(define (self-modify new-self ext)
  (try next old-self (apply-extension ext next new-self)))


;;;;;;;;;;;;;;;;;;;;;;;
;; Small-step macros ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Extensions may fail, in which case they fall through to the base case which will be provided later (as their first argument). This way, extensions let us represent potentially-failing operations as first-class values that compose with other extensions explaining what to do in the failure case. Each operation is a single step that tries to do one thing: if it succeeds, it continues to the next step in the chain, but if it fails, it falls through to the provided base case.

;; While we would ideally want to abstract out the success case as well, some of these operations will bind some variables to be used in the success case, so they need to be macros to allow for binding variables in function parameters or patterns. 

(define-syntax try
  (syntax-rules ()
    [(try ext)
     ext]
    [(try next tmpl)
     (λ(next) tmpl)]
    [(try next self expr)
     (λ(next) (λ(self) expr))]))

(define-syntax try-inline
  (syntax-rules ()
    [(try-inline (next-val self-val) ext)
     (apply-extension-inline ext next-val self-val)]
    [(try-inline (next-val self-val) next-id tmpl)
     (let-inline-alias ([next-id next-val]) (apply-template-inline tmpl self-val))]
    [(try-inline (next-val self-val) next-id self-id expr)
     (let-inline-alias ([next-id next-val] [self-id self-val]) expr)]))

(define-syntax-rule
  (always-do expr)
  (try _ _ expr))

(define-syntax-rule
  (always-do-inline (next self) expr)
  expr)

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
          ((apply-extension ext (λ(self) (λ _ (next self))) self) arg ...))]
    [(try-apply-forget ext arg ... . rest)
     (try next self
          (apply (apply-extension ext (λ(self) (λ _ (next self))) self) arg ... rest))]))

;; guard : Bool -> Extension -> Extension
;; Test the given boolean expression: if it is true, run the given extension, and if it is false, fall through to the next option.  To ensure a predictable evaluation order, this is defined as a macro so that the expression which returns the success extension only runs when the check is true.
(define-syntax-rule
  (guard check ext)
  (if check
      ext
      empty-extension))

(define-syntax guard-inline
  (syntax-rules ()
    [(guard-inline (next self) check ext)
     (if check
         (apply-extension-inline ext next self)
         (apply-template-inline next self))]
    [(guard-inline (next) check ext)
     (if check
         (apply-extension-inline ext next)
         next)]))

;; match-guard : Expr -> Pattern -> Extension -> Extension
;; Attempt to match the given expression against the pattern: if the match is successful, run the given extension under the pattern's bindings, and the match fails, fall through to the next option.
(define-syntax-rule
  (match-guard expr pat ext)
  (match expr
    [pat ext]
    [_ empty-extension]))

(define-syntax match-guard-inline
  (syntax-rules ()
    [(match-guard-inline (next self) expr pat ext)
     (match expr
       [pat (apply-extension-inline ext next self)]
       [_ (apply-template-inline next self)])]
    [(match-guard-inline (next) expr pat ext)
     (match expr
       [pat (apply-extension-inline ext next)]
       [_ next])]))
  
;; try-case-λ : Formals -> Extension -> Extension
;; Attempt to be a lambda that binds the given parameters: if the correct number of arguments are applied, run the given extension with the parameters bound to the arguments, and otherwise fall through to the next option. Note that the form (try-λ rest-id ext) accepts any number of arguments, so it always succeeds.
(define-syntax-rule
  (try-case-λ params ext)
  (try next self (try-case-λ-inline (next self) params ext)))

(define-syntax (try-case-λ-inline stx)
  (syntax-case stx ()
    [(try-case-λ-inline (next) params ext)
     #'(λ(self) (try-case-λ-inline (next self) params ext))]
    [(try-case-λ-inline (next self) rest-id ext)
     (identifier? #'rest-id)
     #'(λ rest-id
         (apply-extension-inline
          ext
          (λ(self) (apply (apply-template-inline next self) rest-id))
          self))]
    [(try-case-λ-inline (next self) (arg-id ...) ext)
     (andmap identifier? (syntax->list #'(arg-id ...)))
     #'(case-λ
        [(arg-id ...)
         (apply-extension-inline
          ext
          (λ(self) ((apply-template-inline next self) arg-id ...))
          self)]
        [args (apply (apply-template-inline next self) args)])]
    [(try-case-λ-inline (next self) (arg-id ... . rest-id) ext)
     (andmap identifier? (syntax->list #'(arg-id ... rest-id)))
     #'(case-λ
        [(arg-id ... . rest-id)
         (apply-extension-inline
          ext
          (λ(self) (apply (apply-template-inline next self) arg-id ... rest-id))
          self)]
        [args (apply (apply-template-inline next self) args)])]))

;; try-match-λ : Patterns -> Extension -> Extension
;; Attempt to be a lambda that matches its arguments against the given patterns: if the number and shape of the arguments fits the pattern list, then run the given success extension under the bindings introduced by the patterns, and otherwise fall through to the next option.
(define-syntax-rule
  (try-match-λ params ext)
  (try next self (try-match-λ-inline (next self) params ext)))

(define-syntax try-match-λ-inline
  (syntax-rules ()
    [(try-match-λ-inline (next) params ext)
     (λ(self) (try-match-λ-inline (next self) params ext))]
    [(try-match-λ-inline (next self) (pattern ...) ext)
     (match-λ*
      [(and args (list pattern ...))
       (apply-extension-inline
        ext
        (λ(self) (apply (apply-template-inline next self) args))
        self)]
      [args (apply (apply-template-inline next self) args)])]
    [(try-match-λ-inline (next self) (pattern ... . rest-id) ext)
     (match-λ*
      [(and args (list-rest pattern ... rest-id))
       (apply-extension-inline
        ext
        (λ(self) (apply (apply-template-inline next self) args))
        self)]
      [args (apply (apply-template-inline next self) args)])]))

;; try-λ : Formals/Patterns -> Extension -> Extension
;; Automatically figure out the form of the given named or matched parameters use the correct form of trial λ-abstraction.
(define-syntax-rule
  (try-λ params ext)
  (try next self (try-λ-inline (next self) params ext)))

(define-syntax (try-λ-inline stx)
  (syntax-case stx ()
    [(try-λ-inline (next) params ext)
     #'(λ(self) (try-λ-inline (next self) params ext))]
    [(try-λ-inline (next self) rest-id ext)
     (identifier? #'rest-id)
     #'(try-case-λ-inline (next self) rest-id ext)]
    [(try-λ-inline (next self) (arg-id ... . end) ext)
     (and (andmap identifier? (syntax->list #'(arg-id ...)))
          (or (identifier? #'end)
              (null? (syntax->datum #'end))))
     #'(try-case-λ-inline (next self) (arg-id ... . end) ext)]
    [(try-λ-inline (next self) params ext)
     #'(try-match-λ-inline (next self) params ext)]))

;; comatch : Copattern -> Extension -> Extension
;; Expand out the copattern expression of an extension to do copattern-matching. The first argument is a flag `initial` or `nested`.
;; `initial` means that this is the *first* operation that the object itself tries to do, so that the second "self" parameter to the extension is *exactly* the same value as the object itself. Thus, this second parameter can be bound as-is to the name in the head of the copattern.
;; `nested` here means that other operations could have come first, so that the second "self" parameter to the extension might be *different* from the view of the object at this point in time. Thus, the head of the copattern is bound to a new recursive object that reflects its current state.
;; Note1: a nested comatch as the first operations is equivalent in behavior to an initial comatch. However, the generated code is different, potentially with different cost.
;; Note2: using an initial comatch after some other operations (especially λ-abstractions) gives access to the *original* "self" of the overall object rather than the view from this point. This could be either intentional or confusing behavior, hence the explicit distinction between comatch initial versus comatch nested.
(define-syntax (comatch stx)
  (syntax-case stx (initial nested apply _)
    [(comatch mode (apply copat args) ext)
     (identifier? #'args)
     #'(comatch mode copat (try-case-λ args ext))]
    [(comatch mode (apply copat arg1 arg ... rest) ext)
     #'(comatch mode copat (try-λ(arg ... . rest) ext))]
    [(comatch mode (copat arg ... . end) ext)
     #'(comatch mode copat (try-λ(arg ... . end) ext))]
    [(comatch mode _ ext)
     #'ext]
    [(comatch initial name ext)
     (identifier? #'name)
     #'(try next name (apply-extension-inline ext next name))]
    [(comatch nested name ext)
     (identifier? #'name)
     #'(try next self (letrec ([name (apply-extension-inline ext next self)]) name))]))

(define-syntax (comatch-inline stx)
  (syntax-case stx (initial nested apply _)
    [(comatch-inline inlined mode (apply copat args) ext)
     (identifier? #'args)
     #'(comatch-inline inlined mode copat (try-case-λ args ext))]
    [(comatch-inline inlined mode (apply copat arg1 arg ... rest) ext)
     #'(comatch-inline inlined mode copat (try-λ(arg ... . rest) ext))]
    [(comatch-inline inlined mode (copat arg ... . end) ext)
     #'(comatch-inline inlined mode copat (try-λ(arg ... . end) ext))]
    [(comatch-inline inlined mode _ ext)
     #'(apply-extension-inline ext . inlined)]
    [(comatch-inline (next self) initial name ext)
     (identifier? #'name)
     #'(let-inline-alias ([name self]) (apply-extension-inline ext next . self))]
    [(comatch-inline (next) initial name ext)
     (identifier? #'name)
     #'(λ(name) (apply-extension-inline ext next name))]
    [(comatch-inline (next . self) nested name ext)
     (identifier? #'name)
     #'(letrec ([name (apply-extension-inline ext next . self)]) name)]))


(define-syntax chain
  (syntax-rules (= try)
    [(chain ext)
     ext]
    [(chain (op ...) step ... ext)
     (op ... (chain step ... ext))]
    [(chain = expr)
     (always-do expr)]
    [(chain try ext)
     ext]))

(define-syntax chain-inline
  (syntax-rules (= try)
    [(chain-inline inlined ext)
     (apply-extension-inline ext . inlined)]
    [(chain-inline inlined (op ...) step ... ext)
     (apply-extension-inline (op ... (chain step ... ext)) . inlined)]
    [(chain-inline inlined = expr)
     (always-do-inline inlined expr)]
    [(chain-inline inlined try ext)
     (apply-extension-inline . inlined)]))


(define-syntax extension
  (syntax-rules ()
    [(extension [copat step ...])
     (chain (comatch initial copat) step ...)]
    [(extension)
     empty-extension]
    [(extension clause1 clause2 clause ...)
     (merge (extension clause1) (extension clause2) (extension clause) ...)]))

(define-syntax extension-inline
  (syntax-rules ()
    [(extension-inline (next-val . self-val) [copat step ...])
     (chain-inline (next-val . self-val) (comatch initial copat) step ...)]
    [(extension-inline (next-val . self-val))
     (apply-template-inline next-val . self-val)]
    [(extension-inline (next-val self-val) clause1 clause2 clause ...)
     ((λ(next) (extension-inline (next self-val) clause1))
      (extension-inline (next-val) clause2 clause ...))]))

(define-syntax template
  (syntax-rules (else)
    [(template)
     empty-template]
    [(template [else default])
     default]
    [(template [else self default])
     (λ(self) default)]
    [(template clause)
     (extension-inline (empty-template) clause)]
    [(template clause1 clause ...)
     ((extension clause1) (template clause ...))]))

(define-syntax template-inline
  (syntax-rules (else)
    [(template-inline (self))
     (apply-template-inline empty-template self)]
    [(template-inline (self) [else default])
     (apply-template-inline default self)]
    [(template-inline (self) [else name default])
     (let-inline-alias ([name self]) default)]
    [(template-inline (self) clause)
     (apply-extension-inline (empty-template self) clause)]
    [(template-inline (self) clause1 clause ...)
     ((λ(next) extension-inline (next self) clause1) (template clause ...))]))


(define-syntax-rule
  (apply-template tmpl self)
  (tmpl self))

(define-syntax-rule
  (apply-extension ext next self)
  ((ext next) self))

(define-for-syntax (one-or-two? n)
  (or (eq? n 1) (eq? n 2)))

(define-for-syntax extension-operation-inline
  (list [list #'extension   one-or-two? #'extension-inline]
        [list #'chain       one-or-two? #'chain-inline]
        [list #'comatch     one-or-two? #'comatch-inline]
        [list #'try         one-or-two? #'try-inline]
        [list #'always-do   one-or-two? #'always-do-inline]
        [list #'try-λ       one-or-two? #'try-λ-inline]
        [list #'try-case-λ  one-or-two? #'try-case-λ-inline]
        [list #'try-match-λ one-or-two? #'try-match-λ-inline]
        [list #'guard       one-or-two? #'guard-inline]
        [list #'match-guard one-or-two? #'match-guard-inline]))

(define-syntax (apply-extension-inline stx)
  (syntax-case stx (λ)
    [(apply-extension-inline (λ(name) tmpl) next . self)
     #'(let-inline-alias ([name next]) (apply-template-inline tmpl . self))]
    [(apply-extension-inline (op arg ... . end) inlined ...)
     (and
      (identifier? #'op)
      (let ([inlined-version (assoc #'op extension-operation-inline free-identifier=?)])
        (and inlined-version
             ((cadr inlined-version) (syntax->list #'(inlined ...))))))
     (with-syntax ([op-inline
                    (caddr (assoc #'op extension-operation-inline free-identifier=?))])
         #'(op-inline (inlined ...) arg ... . end))]
    [(apply-extension-inline ext next self)
     #'(apply-extension ext next self)]
    [(apply-extension-inline ext next)
     #'(ext next)]
    [(apply-extension-inline ext)
     #'ext]))

(define-for-syntax template-operation-inline
  (list [list #'template #'template-inline]))

(define-syntax (apply-template-inline stx)
  (syntax-case stx (λ)
    [(apply-template-inline (λ(name) expr) self)
     #'(let-inline-alias ([name self]) expr)]
    [(apply-template-inline (op arg ... . end) self)
     (and
      (identifier? #'op)
      (assoc #'op template-operation-inline free-identifier=?))
     (with-syntax ([op-inline
                    (cadr (assoc #'op template-operation-inline free-identifier=?))])
         #'(op-inline (self) arg ... . end))]
    [(apply-template-inline tmpl self)
     #'(apply-template tmpl self)]
    [(apply-template-inline tmpl)
     #'tmpl]))

(define-syntax (let-inline-alias stx)
  (syntax-case stx (_)
    [(let-inline-alias () () expr)
     #'expr]
    [(let-inline-alias (bind ...) () expr)
     #'(let (bind ...) expr)]
    [(let-inline-alias (bind ...) ([_ val] todo ...) expr)
     #'(let-inline-alias (bind ...) (todo ...) expr)]
    [(let-inline-alias (bind ...) ([same name] todo ...) expr)
     (and (identifier? #'same) (identifier? #'name) (bound-identifier=? #'same #'name))
     #'(let-inline-alias (bind ...) (todo ...) expr)]
    [(let-inline-alias (bind ...) (real todo ...) expr)
     #'(let-inline-alias (bind ... real) (todo ...) expr)]
    [(let-inline-alias (todo ...) expr)
     #'(let-inline-alias () (todo ...) expr)]))


;; unplug : Extension -> Extension
;; The 'unplug method remembers an extension, so you can ask the object for it later
(define (unplug ext)
  (extension
   [(self 'unplug) = ext]))

;; adapt : Extension; depends on 'unplug
;; The 'adapt method lets you apply a (Extension -> Extension) modifier to the Extension you get by "unplug"ging the object itself, and then re-"plug"s the modified Extension again.
(define adapt
  (extension
   [(self 'adapt mod) = (plug (meta (mod (self 'unplug))))]))

;; composition : Extension; depends on 'unplug
;; The 'compose method lets you pass in a list of other objects (which can all be "unplug"ged) and combines them together into a single object that shares all their behavior. Precedence of overlapping methods is resolved left-to-right, starting from this object itself, and then proceeding through each one of the arguments from first to last.
(define composition
  (extension
   [(self 'compose)      = self]
   [(self 'compose . os) = (plug (meta (apply merge
                                              (self 'unplug)
                                              (map (λ(o) (o 'unplug)) os))))]))

;; meta : Extension -> Extension
;; Combines the 'unplug, 'adapt, and 'compose methods above with the methods of the given extension itself
(define (meta ext) (merge ext (unplug ext) composition adapt))

(define default-object-modifier (make-parameter meta))

;; Top-level and entry-point macros

(define-syntax-rule
  (λ* clause ...)
  (introspect (template clause ...)))

(define-syntax-rule
  (override-λ* old clause ...)
  (λ* clause ... [else _ old]))

(define-syntax (define* stx)
  (syntax-case stx (apply)
    [(define* [(apply copat args) step ...] clause ...)
     (identifier? #'args)
     #'(define* [copat (try-case-λ args) step ...] clause ...)]
    [(define* [(apply copat arg1 arg ... args) step ...] clause ...)
     #'(define* [copat (try-λ arg1 arg ... args) step ...] clause ...)]
    [(define* [(copat arg ... . end) step ...] clause ...)
     #'(define* [copat (try-λ(arg ... . end)) step ...] clause ...)]
    [(define* [name step ...] clause ...)
     (identifier? #'name)
     #'(define name (λ* [name step ...] clause ...))]
    [(define* name clause ...)
     (identifier? #'name)
     #'(define name (λ* clause ...))]))

(define-syntax object
  (syntax-rules (<:)
    [(object (<: mod) clause ...)
     (plug (mod (extension clause ...)))]
    [(object clause ...)
     (plug ((default-object-modifier) (extension clause ...)))]))

(define-syntax (define-object stx)
  (syntax-case stx (<: apply)
    [(define-object (<: mod) [(apply copat args) step ...] clause ...)
     (identifier? #'args)
     #'(define-object (<: mod) [copat (try-case-λ args) step ...] clause ...)]
    [(define-object (<: mod) [(apply copat arg1 arg ... args) step ...] clause ...)
     #'(define-object (<: mod) [copat (try-λ arg1 arg ... args) step ...] clause ...)]
    [(define-object (<: mod) [(copat arg ... . end) step ...] clause ...)
     #'(define-object (<: mod) [copat (try-λ(arg ... . end)) step ...] clause ...)]
    [(define-object (<: mod) [name step ...] clause ...)
     (identifier? #'name)
     #'(define-object (name <: mod) [name step ...] clause ...)]
    [(define-object (name <: mod) clause ...)
     #'(define name (object (<: mod) clause ...))]
    [(define-object name clause ...)
     (identifier? #'name)
     #'(define-object (name <: (default-object-modifier)) clause ...)]
    [(define-object clause ...)
     #'(define-object (<: (default-object-modifier)) clause ...)]))

