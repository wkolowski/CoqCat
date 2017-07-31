# Formalization of Category Theory in Coq

Design choices:
 * Type of objects and Setoid of morphisms. Tried other configurations and this one seems best.
 * Axioms:
     - Indefinite description — very convenient, a real ass-saver.
     - Functional extensionality — in general, working with custom extensional equalities is painful. Needed to prove that the category CoqSet has exponentials and all products.
     - Proof irrelevance — needed for example to prove that CoqSet has equalizers.
     - JMeq_eq — needed to prove that taking the dual category is involution with respect to equality.
 * Tried to stick to using normal equality (eq), but it's increasingly difficult. Did tests of other possible equality relations.
 * Using typeclasses and universe polymorphism where possible.

Accomplished:
 * Basics: defined categories and proved properties of different kinds of morphisms.
 * Universal constructions: initial, terminal and zero objects, products, coproducts, biproducts (both binary and general), equalizers and coequalizers together with more or less of their properties. This is one of my greatest accomplishments — after changing, improving and correcting the definitions a gazillion times I'm starting to be pretty sure that they are correct and convenient. However, they're not perfect yet: there are issues with coherence conditions.
 * Functors: defined different kinds of functors, proved their properties, defined the category of categories.
 * Natural transformations: defined functor categories, characterized natural isomorphisms.
 * Defined and proved properties of these categories: Set, Rel, Sgr, Mon, Grp, Pros, Pos etc. Also got other hierarchies based not on Set, but rather on Setoid, Apartoid etc (or rather I wanted to make an Apartoid-based hierarchy, but it's not done yet).
 * Got some quite useful general tactics:
   * cat — working with categories in general (it can solve the category laws for many categories). It has a reflective component for solving morphism equations.
   * Tactics for particular categories (sgr, mon, grp, pros, pos etc.) — they can, for example, elegantly destruct objects and morphisms of these categories and perform some simplifications. Additionally, reflective tactics for solving semigroup/monoid/group equations are integrated into them.
   * proper — solving instances of proper
   * solve_equiv —  proving that a relation is an equivalence
   * init/term — rewriting with with initial/terminal objects
   * fpair/copair — rewriting with products/coproducts
   * functor — simplification for functors
   * iso — working with isomorphisms
   * curry — rewriting with exponential objects

General TODO:
 * Define adjoints.
 * Do stuff related to distributive categories.
 * Refactor the products and coproducts — put them in separate files in a new directory. Make a new file about finite (and not just binary) products/coproducts and put there the theorems that relate binary products/coproducts with initial and terminal objects (or not).
 * Port all properties of universal constructions to skolemized definitions.
 * Use more duality.
 * Prove more properties of universal constructions (like these for equalizers).
 * Revise equalities and equivalences and write a few more (like JMequiv_dep).
 * Possibly reimplement the fpair and copair tactics using reification.
 * Check if it's possible to do "continuous reification".
 * Stop using dependent types for doing reification of Cat.
 * Implement morphisms of various categories using classes instead of sigma types.

Instances:
 * Solve the dependent type problems with setoid coproducts.
 * Implement big (co)products and coequalizers of Apartoids.
 * Characterize morphisms and universal constructions of setoids/apartoids etc.
 * Find a general boilerplate for a file with concrete category — apply it to all instances.
 * Define heterogenous apartoids.
 * Refactor the directory structure.

Further ideas:
 * Implement concrete categories and use them for theorems about individual categories.
 * Implement monoidal categories.
 * Implement enriched categories.

TODO from Bartosz Milewski's blog:
 * 2-Categories — 2015-04-07
 * Limit as a Natural Isomorphism — 2015-04-15
 * Representable Functors — 2015-07-29
 * The Yoneda Lemma — 2015-09-01
 * Yoneda Embedding — 2015-10-28

Tips for future me:
 * If Coq doesn't see that some morphism is Proper, put the corresponding theorem in context using pose, eg. pose (P := fpair_Proper). This likely has something to do with registering morphisms as Proper. I should read the docs...
 * Unique up to unique isomorphism means an isomorphism compatible with structure. In the case of products, for example, it has to be compatible with the projections (they are the structure), but no with the pairing (I think pairing is a property, not structure).
 * Coherences for dependent stuff can be stated by lifting standard equivalences to heterogenous ones. Coherence for objects can be stated using these heterogenous equivalences on their identity morphisms.
