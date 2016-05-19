CIC
===

A Redex model of CIC as specified in [Chapter 4 of the Coq reference manual](https://coq.inria.fr/doc/Reference-Manual006.html#Cic-inductive-definitions).

We currently model the following parts of the CIC spec:

* CC; Caveats:
  - Use `(@ e e)` instead of juxtaposition for application syntax.
  - Missing global assumptions and definitions.
* βιδζη conversion
* Subtyping
* Infinite hierarchy of Type
* Predicative Set
* Impredicative Prop
* Parameterized indexed inductive families;
  Caveats: 
  - Missing some trivial checks due to focus on other features; see notes in model.
  - Missing mutually inductive families, since they can be encoded via indexed families; see, e.g., [The Rooster and the Syntactic Bracket](https://arxiv.org/abs/1309.5767) for the construction.
* Strict positivity checking
* Dependent pattern matching
* Allowed elimination sorts, including "Prop-extended" (elimination to any sort from empty and singleton Prop)
* Recursive functions;
  Caveats:
  - Missing mutually recursive functions.
  - Expects recursive functions to be well-defined on their first argument.
* Termination checking

We do not plan to model:

* Coinductive families
