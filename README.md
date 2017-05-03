# Formalization of Category Theory in Coq

Design choices:
 * Type of objects and Setoid of morphisms. Tried other configurations and this one seems best.
 * Axioms: indefinite description, duality (because couldn't prove it as a theorem), possibly proof irrelevance and or functional extensionality.
 * Tried to stick to using normal equality (eq), but it's increasingly difficult. Did tests of other possible equality relations.
 * Using typeclasses and universe polymorphism where possible.
 * Got different branches for differents designs of the algebraic/order hierarchy (one based on types, setoids, apartoids etc.).

Accomplished:
 * Basics: defined categories and proved properties of different kinds of morphisms.
 * Universal constructions: initial, terminal and zero objects, products, coproducts, biproducts (both binary and general), equalizers and coequalizers together with more or less of their properties.
 * Functors: defined different kinds of functors, proved their properties, defined the category of categories.
 * Natural transformations: defined functor categories, characterized natural isomorphisms.
 * Defind and proved properties of these categories: Set, Rel, Sgr, Mon, Grp, Pros, Pos etc. Also got other hierarchies based not on Set, but rather on Setoid, Apartoid etc.
 * Automation: got some quite useful genral tactics for working with categories (cat) and also tactics for particular categories (sgr, mon, grp, pros, pos etc.) - these can, for example, elegantly destruct objects of these categories.

Fix:
 * Prove that dual is involution with respect to equality and then remove the axiom I'm currently using.
 * Write new unique ismorphicness theorems for products (the isos have to be compatible with the projections).
 * Check whether big\_product is properly defined (there was an error in big\_product\_skolem).
 * Give some structure to the modules, e.g. Sgr should be called Instances.Set.Sgr. Solution: each subdirectory has to have its own makefile...
 * Maybe I should use Proper more? Looks like having "Proper ..." in context makes rewriting easy. Maybe there should be separate Proper instances for each variable, like x == x' -> R x y -> R x' y?
 * Make sure everything works with the new makefile.

General:
 * Implement a tactic to decide equality of morphisms based on a tactic that decides whether two elements of a monoid are equal (was it described in Coq'Art?). This will be very hard, but fruitful.
 * Define dual instances for big products/coproducts/biproducts, equalizers and coequalizers.
 * Settle all the maters with axioms forever (is the combination indefinite description + proof irrelevance + functional extensionality ok?).

Instances:
 * Define slice categories.
 * Solve the dependent type problems with setoid coproducts.
 * Implement big (co)products and coequalizers of Apartoids.
 * Characterize morphisms and universal constructions of setoids/apartoids etc.
 * Find a general boilerplate for a file with concrete category — apply it to all instances.
 * Define heterogenous apartoids.
 * Implement prosets and semigroups wth respect to setoids/apartoids etc.
 * Implement some examples of functors (like the Hom functor).

Further ideas:
 * Implement concrete categories and use them for theorems about individual categories.
 * Implement better pullbacks and pushouts.
 * Implement limits and colimits.
 * Implement monoidal categories.
 * Implement enriched categories.

Stuff from Awodey's book: 7-8 page 10 (functors between deloopings of Pros are Pros homomorphisms), page 14 (Cayley's Theorem), 3 page 17 onwards.
