# Formalization of Category Theory in Coq

## Design choices
* Type of objects and Setoid of morphisms. Tried other configurations and this one seems best.
* Using typeclasses and universe polymorphism where possible.
* Axioms:
  - `functional_extensionality` — only needed to prove that the category `CoqSet` has exponentials and indexed products.
  - `proof_irrelevance` — only needed to prove `Dual (Dual C) = C`.
  - `propositional_extensionality` — only needed to prove that epimorphisms in Set are surjections.

## Accomplished
* Basics: defined categories and proved properties of different kinds of morphisms.
* Functors: defined different kinds of functors, proved their properties, defined the category of functors and the category of categories.
* Natural transformations: defined functor categories, characterized natural isomorphisms.
* Universal constructions:
  - initial, terminal and zero objects
  - products, coproducts and biproducts
  - indexed products, coproducts and biproducts (where the index can be any type)
  - equalizers and coequalizers
  - pullbacks and pushouts
  - exponentials

  The definitions are quite far from what you can find in a typical textbook a- they are equational and stated in a way that strongly resembles the rules of type theory (formation, introduction, elimination, computation and uniqueness), but with the uniqueness rules being "symmetric".

  This is one of my greatest accomplishments — after changing, improving and correcting the definitions a gazillion times I'm starting to be pretty sure that they are correct and convenient. However, they're not perfect yet: there are issues with coherence conditions.
* Defined and proved properties of these categories:
  - `CoqSetoid` - this formalization's equivalent of Set, the category of sets and functions. We use setoids because our categories actually have a setoid of morphisms and not simply a set.
  - `Rel` - category of types and relations.
  - `Sgr` - category of semigroups.
  - `Mon` - category of monoids.
  - `Grp` - category of groups.
  - `Pros` - category of preorders.
  - `Pos` - category of posets.

  Also defined other hierarchies based not on `CoqSetoid`, but rather on `CoqSet` (the category of types and functions). I also wanted to make an `Apartoid`-based hierarchy (where an `Apartoid` is a type together with an apartness relation; morphisms are functions which reflect the apartness).
* Got some quite useful general tactics:
  - `proper` — a tactic for solving instances of `Proper`
  - `solve_equiv` —  a tactic for proving that a relation is an `Equivalence`
  - `cat` — a tactic for working with categories in general. It can prove the category laws for many categories, perform simplification of equations on morphisms, etc.
  - `product_simpl`/`coproduct_simpl`/`equalizer_simpl`/`coequalizer_simpl`/`pullback_simpl`/`pushout_simpl`/`exponential_simpl` etc. - tactics for simplifying morphisms involving these constructions
  - `solve_product`/`solve_coproduct`/`solve_exponential` - faster versions of the above simplification tactics which can solve goals by themselves
  - Tactics for particular categories (`sgr`, `mon`, `grp`, `pros`, `pos`, etc.) — they can, for example, elegantly destruct objects and morphisms of these categories, perform some simplifications and finish easy goals. Additionally, reflective tactics for solving semigroup/monoid/group equations are integrated into them.

## TODO

### Research
* Formalize more of this paper: http://www.cs.ox.ac.uk/ralf.hinze/SSGIP10/Notes.pdf
* Investigate how useful is `SProp`.
* Investigate how useful is HoTT-based approach.
* Investigate the Reynolds programme.

### General ideas
* Read Bartosz Milewski's book on category theory.
* Define adjoints.
* Implement monoidal categories.
* Implement enriched categories.
* Implement concrete categories and use them for theorems about individual categories.
* Distributive categories.

### Maintenance
* Investigate alternative definitions of universal constructions from `Universal/AlternativeDefinitions.v`.
* Investigate how much duality can be used to cut down the amount of code without sacrificing nice naming.
* Investigate whether (co)equalizers and pullbacks/pushouts are `Proper`.
* Prove more properties of universal constructions (like these for equalizers).
* Check if it's possible to do "continuous reification".
* Stop using dependent types for doing reification of `Cat`.
* Implement morphisms of various categories using records/classes instead of sigma types.

### Instances
* Solve the dependent type problems with setoid coproducts.
* Implement indexed (co)products and coequalizers of Apartoids.
* Characterize morphisms and universal constructions of setoids/apartoids etc.
* Find a general boilerplate for a file with a concrete category — apply it to all instances.
* Define heterogenous apartoids.

## Tips for future me
* If Coq doesn't see that some morphism is `Proper`, put the corresponding theorem in context using `pose`, eg. `pose (P := Proper_fpair)`. This likely has something to do with registering morphisms as `Proper`. I should read the docs...
* Unique up to unique isomorphism means an isomorphism compatible with structure. In the case of products, for example, it has to be compatible with the projections (they are the structure), but not with the pairing (I think pairing is a property, not structure).
* Coherences for dependent stuff can be stated by lifting standard equivalences to heterogenous ones. Coherence for objects can be stated using these heterogenous equivalences on their identity morphisms.
