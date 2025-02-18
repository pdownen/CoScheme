# Review 1

### Section 1

✅ I think it's a little strange that the title, abstract and introduction focus so much on corecursion, when that does not seem to be the major focus for the rest of the paper. Yes, it's an important contribution of the paper, but most of the rest of the paper focuses more on the expression problem and the composable pattern language, with corecursion just as a feature of the pattern language. It seems to me you should find a motivation that brings the rest of what you've done to the fore.

> I changed our introduction a lot, I will change the little summary in the end and the abstract latter. I am planing to move all the coinductive discussion to section 2.

❓One page 2, you switch from the Haskell definition of fibs using pattern syntax and laziness, to the Agda definition using copatterns. There may be a good chance here to motivate the need for copattern syntax, i.e., why should one not just continue to define fibs in the Haskell way but declare that Stream is a coinductive type?

> Is saying that they restore the duality enough? I moved this to section 2, but I think this is still and odd placement.

### Section 2

✅ When you first define eval-arith, you have a footnote stating that the recursive calls to eval-mul must somehow know how to call eval-num and eval-add. True, but this is an absolutely vital part of your design, and should not be relegated to a footnote for the astute reader! Furthermore, the footnote explains the problem (the system must somehow do X) but not the solution (open recursion). You should be stating clearly that functions in your system use open recursion so that the recursive call to eval-mul actually invokes eval-arith in this case. This is also your chance to introduce the "self" parameter, which currently makes its firs appearance without any explanation in an example on the following page.

> Section 2.2

✅In eval-add-safe, the syntax for declaring clauses seems to change and I do not understand the semantics. On the previous page you have

   (define-object [(eval-add `(add ,l ,r)) = ...])

and on this page

   (define-object eval-add-safe [(self 'eval ('add l r)) = ...])

where now there is an extra argument 'eval. How do these two definitions manage to have the same type (as it were)? Now I notice that eval-add-safe in the extra materials does not have an 'eval argument, so maybe this is a mistake.

> Section 2.2?

✅Here it gradually becomes apparent that you use an object metaphor throughout the library: functions are defined with define-object, and atoms such as 'add are analogous to messages which the objects accept. This also helps me to understand why the strange syntax for composition - (o1 'compose o2) rather than (compose o1 o2) - it's because (I think) 'compose is just a message that all objects implement. But you don't point out this object metaphor in the paper until Section 3, which made the syntax a lot harder to grasp for me. Please bring it up when introducing your library!

> Section 2.2

Perhaps I'm being a bit nitpicky, but it seems like the way constant-fold is implemented is rather complicated. All the difficulties arise because numbers can appear in the expression tree in two forms: either as e.g. '(num 3) or as just a numeric literal 3. eval-arith expects its argument to use the first form but returns the second form, leading to noncompositionality and chaos. If numeric literals were represented as just e.g. 3 instead of '(num 3), then things would get simpler. Alternatively, one could do constant folding by just recursing through the expression tree and calling eval-arith at each node; if it returns a number x, then constant folding returns `(num ,x). I mean, it is impressive that your system can express such a complex composition quite easily, but I find myself a bit distracted since I'm not sure the complexity is really needed here.

Have you tried modelling any mutually recursive functions?

The tutorial style of this section is nice, but for a deeper understanding - particularly in a PLT paper - I want to also know what the primitive operations of the library are. Which operations are built in, and which are syntactic sugar (and for what)? For example, you introduce define*, define-object and object, but it's not entirely clear to me how they relate. This is a big problem when you get to section 3.2, where it's not clear if the core calculus really matches the expansive library that you've introduced in section 2. Tentative suggestion: Section 2 could be followed by a section where you show how to implement the library in terms of a few primitives operations (which hopefully will be the same ones appearing in section 3). Then the paper has a clear structure: "library -> reducing the library to primitives -> implementing the primitives using continuations".

### Section 3

What is comatch?

✅Typo: "compose eval-add with another evaluator handling a diferent case, like eval-add" - eval-add twice

✅"and can be further expanded into built-in Racket primitives like so": this should be its own sentence (maybe even its own paragraph). It is unrelated to the first half of the sentence.

 #### Section 3.2

Here I have a huge amount of trouble following what is going on! Not the technical details of the translation itself, which are fine, but rather how it connects to the rest of the paper.

The basic problem is that most of the operations of the core calculus, such as lambda*, extension, and template, have not appeared in the paper up to this point. It is not clear how the library can be desugared to the core calculus, partly because it is not even clear what the operations mean. Unfortunately, the operations are introduced not using an example program, or with a precise definition, but rather by a sort of informal explanation of roughly what they do, which only gives me a rather fuzzy idea of what is going on. I do not understand (from the explanation in the text) the meaning of lambda* or template, or the description of the (= M) operation: "looks odd out of context but expresses the equational nature of copattern matching when used in examples". 

Suggestion 1: Use examples! Ideally I want to see how one of the example functions defined earlier looks in terms of this core calculus. Use the example to make your explanations simpler and more precise. It is very hard to give a clear and precise explanation in prose without a concrete object such as an example to refer to.

Suggestion 2: Consider introducing some of these core operations already in section 2 (if they exist in the library). E.g., show how other operations are implemented in terms of template and extension. Right now it is difficult to see how the core calculus relates to the overall library.

The formalism of the translation itself is easy enough to understand (though I am still not sure how to use template and extension). Two comments: 1) what is fail? (an operation that raises an exception?) 2) what do you mean by Q[x]? (I interpret it as replacing □ with x but I don't see where it's defined in the paper.)

-- Section 5

I had not previously seen the idea of proving a translation correct by reasoning about the equational theories of the two languages. Cool!

# Review 2

✅ p.2, `fibs`: I expected to see a discussion of how the library knows there are enough cases in `fibs` to constitute a well-founded definition. Say explicitly that the library here does not check, that it's up to the user to decide.

> Moved this dicussion to the preamble in sec 2.

✅p.2 "We show a new method for implementing copatterns as a collection of macros": it sounds like macros are the interesting part, but that is not the case. OCaml copatterns used macros too, as we discover in an offhand way in the next paragraph. Split into two sentences? (new technique. using macros.) Acknowledge the macros in [14] at the first reference?

p.2 Replicating your ideas in Idris, Lean 4, or Rhombus would be interesting future work. They all have decent metaprogramming support.

✅p.3 "Similarly, infinite streams ....": Awkward, especially since the "two constructed forms" for lists do not match the "two different behaviors" in this sentence. I would delete the List discussion and focus only on streams.

✅p.3 Perhaps worth citing Languages as Libraries because you have written a library that effectively provides a language.

✅p.3 "The simplest of a stream": typo, also this is an abrupt switch back to streams in the middle of a paragraph on copatterns.

p.3 All the codeblocks would benefit from informal signatures along the lines of the `Stream a` definition at the top of the page. (In the HTDP tradition, types can guide the design even if one refuses to use a type checker.)

p.6 `'unplug`: There is evidently an API of messages at play. Present the API. (Supplement calls these Extensions.)

✅p.7 "recurse on itself" --> "recur"

✅p.7 Put `define expr2` and all similar definitions on their own line. Also the call to `eval-arith` nearby has a typo, it says `expr` instead of `expr2`.

✅p.7 "for the first time": I do not know what you mean by this. Is this pointing to a research contribution?

✅p.7 "check by the": typo

✅p.8 The supplement is ok, but the definition of `constant-fold` here is not strong enough to rewrite `expr3` as the paper claims. We need `reform-operations*` to handle `mul` and (I think) recursively rewrite.

> Should we expand the examples to cover all cases?

p.8 In Rhombus, it might be possible to unify the pattern language and expression language instead of having two similar-but-not-the-same languages (`('var x)` vs `(list 'var x)`).

✅p.9 "Because we cannot gain any information from a static type ...": Awkward start of paragraph; the relation between this thought and the paragraph title is unclear.

✅p.10 "Textually, the vertical": should this be "horizontal"?

p.10 Where is `comatch` defined?

✅p.11 "In order to compose `eval-add` with another evaluator ... like `eval-add`": typo

✅p.11 "Racket primitives": name the primitives so that readers know what to look for in the code

> primitives -> definition

p.12 Fig 1: why not show the source language first? very confusing choice.

✅p.13 "The familiar syntactic sugar else M": I don't see what is familiar about this except the name "else". For example, if I were to write factorial in Python I would use an "else" that makes a recursive call.

p.13 The types at the bottom of this page would be more helpful if the appeared before the details of the source language.

p.14 Fig 3: Very jarring that there are 4 titles in this figure but it defines only 3 translation metafunctions.

✅❓p.14 Why show both sides of the `=\eta`s? At least swap the right and left sides, so readers get the short version before slogging through the long better-for-Scheme one.

> I changed the column order

✅p.15 "fig 3 However": typo

p.15 "(otherwise a run-time error may be encountered)": YIKES! "may" is far scarier than "will"

p.16 "merge is the regular definition of first-class function composition": so why not call in compose?

✅p.17 "compare the value x against ...": x must be a variable, if it was a value we could check for null.

p.18 Why is proposition 1 applying the source-to-target translation to target terms? Something is very wrong.

✅p.19 "makes the it possible": typo

✅p.19 "lisp" -> "Lisp"

✅p.19 "we leave the equation of a complete and minimal equational theory": awkward

> Equation -> Definition

p.20 "et al.": list all authors

p.20 Two more related work suggestions:

* Function Inheritance: Monadic Memoization Mixins (another look at modifying recursive definitions), https://www.semanticscholar.org/paper/Function-Inheritance-%3A-Monadic-Memoization-Mixins-Brown-Cook/d2bf5dc5c6c6bff91d10a0e2dceaaa13c2064765

* CoCaml: Functional Programming with Regular Coinductive Types (interpreter for a CBV language with coinductive data), https://www.cs.cornell.edu/~kozen/Papers/CoCaml.pdf

> I will cite those in section 2

# Review 3

As a small suggestion, is possible, it would be interesting if in the overview, the macro expanded code was presented for comparison.

The topic is very interesting and it would make a great TFP talk! 
Further, the submission is very complete (comes with both formalization and implementation), but promises a great paper! 

As a small suggestion, is possible, it would be interesting if in the overview, the macro expanded code was presented for comparison