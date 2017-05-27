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
 * Got different directories for differents designs of the algebraic/order hierarchy (one based on types, setoids, apartoids etc.).

Accomplished:
 * Basics: defined categories and proved properties of different kinds of morphisms.
 * Universal constructions: initial, terminal and zero objects, products, coproducts, biproducts (both binary and general), equalizers and coequalizers together with more or less of their properties. Not perfect yet: there are issues with coherence conditions.
 * Functors: defined different kinds of functors, proved their properties, defined the category of categories.
 * Natural transformations: defined functor categories, characterized natural isomorphisms.
 * Defined and proved properties of these categories: Set, Rel, Sgr, Mon, Grp, Pros, Pos etc. Also got other hierarchies based not on Set, but rather on Setoid, Apartoid etc.
 * Automation: got some quite useful general tactics for working with categories (cat) and also tactics for particular categories (sgr, mon, grp, pros, pos etc.) — they can, for example, elegantly destruct objects of these categories. Also got some automation for solving instances of Proper, proving equivalences and rewriting with pairings and copairings.

General TODO:
 * Implement a tactic to decide equality of morphisms based on a tactic that decides whether two elements of a monoid are equal (as described in CPDT). This will be very hard, but fruitful.
 * Settle all the matters with axioms forever (is the combination indefinite description + proof irrelevance + functional extensionality ok?).
 * Define representability and adjoints.
 * Do stuff related to distributive categories.
 * Refactor the products and coproducts — put them in separate files in a new directory. Make a new file about finite (and not just binary) products/coproducts and put there the theorems that relate binary products/coproducts with initial and terminal objects.
 * Port all properties of universal constructions to skolemized definitions.
 * Use more duality.

Instances:
 * Solve the dependent type problems with setoid coproducts.
 * Implement big (co)products and coequalizers of Apartoids.
 * Characterize morphisms and universal constructions of setoids/apartoids etc.
 * Find a general boilerplate for a file with concrete category — apply it to all instances.
 * Define heterogenous apartoids.
 * Implement prosets and semigroups wth respect to setoids/apartoids etc.
 * Refactor the directory structure.

Further ideas:
 * Implement concrete categories and use them for theorems about individual categories.
 * Implement better pullbacks and pushouts.
 * Implement limits and colimits.
 * Implement monoidal categories.
 * Implement enriched categories.

Tips for future me:
 * If Coq doesn't see that some morphism is Proper, put the corresponding theorem in context using pose, eg. pose (P := fpair_Proper). This likely has something to do with registering morphisms as Proper. I should read the docs...
 * Unique up to unique isomorphism means an isomorphism compatible with structure. In the case of products, for example, it has to be compatible with the projections (they are the structure), but no with the pairing (I think pairing is a property, not structure).
 * Coherences for dependent stuff can be stated by lifting standard equivalences to heterogenous ones. Coherence for objects can be stated using these heterogenous equivalences on their identity morphisms.
