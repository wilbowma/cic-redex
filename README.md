CIC
===

A model of CIC as specified in Chapter 4 of the Coq reference manual[¹].

We currently model the following parts of the CIC spec:

* CC
* βιδζη conversion
* Subtyping
* Infinite hierarchy of Type
* Predicative Set
* Impredicative Prop
* Parameterized indexed inductive families[²,³]
* Strict positivity checking
* Dependent pattern matching
* Allowed elimiation sorts, with empty and singleton Prop
* Recursive functions[⁴,⁵]
* Termination checking

[¹]: [CIC specification](https://coq.inria.fr/doc/Reference-Manual006.html#Cic-inductive-definitions)
[²]: Missing some trivial checks due to focus on other features; see notes in model
[³]: Does not support mutually inductive families yet, since they can be encoded via indexed families. See e.g. [The Rooster and the Syntactic Bracket](https://arxiv.org/abs/1309.5767) for the construction.
[⁴]: Does not support mutually recursive functions yet.
[⁵]: Expects recursive functions to be defined on their first argument, unlike in the specification.

We do not plan to model:

* Coinductive families
