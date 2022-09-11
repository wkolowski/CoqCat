From Cat Require Export Cat.
From Cat.Universal Require Export Product.

Class isExponential
  {C : Cat} {hp : HasProducts C} (A B : Ob C)
  (E : Ob C) (eval : Hom (product E A) B)
  (curry : forall {E2 : Ob C}, Hom (product E2 A) B -> Hom E2 E)
  : Prop :=
{
  exp_comp :
    forall {E' : Ob C} (f : Hom (product E' A) B),
      curry f ×' id A .> eval == f;
  equiv_exponential :
    forall {E' : Ob C} (f g : Hom E' E),
      f ×' id A .> eval == g ×' id A .> eval -> f == g;
}.

#[export] Hint Mode isExponential ! ! ! ! ! ! ! : core.
#[export] Hint Mode isExponential ! - ! ! - - - : core.

Lemma equiv_exponential' :
  forall
    {C : Cat} {hp : HasProducts C} {A B : Ob C}
    {E : Ob C} {eval : Hom (product E A) B}
    {curry : forall {E2 : Ob C}, Hom (product E2 A) B -> Hom E2 E}
    {isExp : isExponential A B E eval (@curry)}
    {E' : Ob C} (h1 h2 : Hom E' E),
      h1 == h2 <-> h1 ×' id A .> eval == h2 ×' id A .> eval.
Proof.
  split.
  - now intros ->.
  - now intros; apply equiv_exponential.
Qed.

Definition uncurry
  {C : Cat} {hp : HasProducts C} {A B : Ob C}
  {E : Ob C} {eval : Hom (product E A) B}
  {curry : forall {E2 : Ob C}, Hom (product E2 A) B -> Hom E2 E}
  {isExp : isExponential A B E eval (@curry)}
  [E' : Ob C] (f : Hom E' E)
  : Hom (product E' A) B := f ×' (id A) .> eval.

Section Exponential.

Context
  {C : Cat} {hp : HasProducts C} {A B : Ob C}
  {E : Ob C} {eval : Hom (product E A) B}
  {curry : forall {E2 : Ob C}, Hom (product E2 A) B -> Hom E2 E}
  {isE : isExponential A B E eval (@curry)}
  [E' Z : Ob C].

Arguments curry {E2} _.

#[export]
Instance Proper_curry :
  Proper (equiv ==> equiv) (@curry E').
Proof.
  now intros x y H; rewrite equiv_exponential', !exp_comp.
Defined.

#[export]
Instance Proper_uncurry : Proper (equiv ==> equiv) (uncurry (E' := E')).
Proof.
  now unfold uncurry; intros f g ->.
Qed.

Lemma universal_property :
  forall (f : Hom (product E' A) B) (g : Hom E' E),
    curry f == g <-> g ×' id A .> eval == f.
Proof.
  split.
  - now intros <-; rewrite exp_comp.
  - now intros; rewrite equiv_exponential', exp_comp.
Qed.

Lemma computation_rule :
  forall f : Hom (product E A) B,
    curry f ×' id A .> eval == f.
Proof.
  now intros f; rewrite exp_comp.
Qed.

Lemma uniqueness_rule :
  forall (f : Hom (product E' A) B) (g : Hom E' E),
    g ×' id A .> eval == f -> g == curry f.
Proof.
  now intros; rewrite equiv_exponential', exp_comp.
Qed.

Lemma curry_uncurry :
  forall f : Hom E' E,
    curry (uncurry f) == f.
Proof.
  now intros f; rewrite equiv_exponential', exp_comp.
Qed.

Lemma uncurry_curry :
  forall f : Hom (product E' A) B,
    uncurry (curry f) == f.
Proof.
  now unfold uncurry; intros f; rewrite exp_comp.
Qed.

Lemma curry_eval :
  curry eval == id E.
Proof.
  now rewrite equiv_exponential', exp_comp, ProductFunctor_fmap_id, comp_id_l.
Qed.

End Exponential.

Ltac exponential_simpl :=
  repeat (rewrite
    ?equiv_exponential', ?exp_comp, ?curry_uncurry, ?uncurry_curry, ?curry_eval,
    ?ProductFunctor_fmap_comp_l, ?ProductFunctor_fmap_comp_r, ?ProductFunctor_fmap_id,
    ?comp_id_l, ?comp_id_r, ?comp_assoc).

Lemma isExponential_uiso :
  forall
    (C : Cat) (hp : HasProducts C) (A B : Ob C)
    (E1 : Ob C) (eval1 : Hom (product E1 A) B)
    (curry1 : forall Z : Ob C, Hom (product Z A) B -> Hom Z E1)
    (E2 : Ob C) (eval2 : Hom (product E2 A) B)
    (curry2 : forall Z : Ob C, Hom (product Z A) B -> Hom Z E2),
      isExponential A B E1 eval1 curry1 ->
      isExponential A B E2 eval2 curry2 ->
        exists !! f : Hom E1 E2, isIso f /\ f ×' id A .> eval2 == eval1.
Proof.
  intros.
  exists (curry2 E1 eval1).
  repeat split.
  - exists (curry1 E2 eval2).
    now rewrite !equiv_exponential', !ProductFunctor_fmap_comp_l, !comp_assoc, !exp_comp,
      !ProductFunctor_fmap_id, !comp_id_l.
  - now rewrite exp_comp.
  - now intros; rewrite equiv_exponential', exp_comp.
Qed.

Arguments isExponential_uiso {C hp A B E1 eval1 curry1 E2 eval2 curry2} _ _.

Lemma isExponential_iso :
  forall
    (C : Cat) (hp : HasProducts C) (A B : Ob C)
    (E1 : Ob C) (eval1 : Hom (product E1 A) B)
    (curry1 : forall Z : Ob C, Hom (product Z A) B -> Hom Z E1)
    (E2 : Ob C) (eval2 : Hom (product E2 A) B)
    (curry2 : forall Z : Ob C, Hom (product Z A) B -> Hom Z E2),
      isExponential A B E1 eval1 curry1 ->
      isExponential A B E2 eval2 curry2 ->
        E1 ~ E2.
Proof.
  intros. destruct (isExponential_uiso H H0). cat.
Qed.

Class HasExponentials (C : Cat) {hp : HasProducts C} : Type :=
{
  expOb : Ob C -> Ob C -> Ob C;
  eval  : forall {A B : Ob C}, Hom (product (expOb A B) A) B;
  curry : forall {A B : Ob C} {Z : Ob C}, Hom (product Z A) B -> Hom Z (expOb A B);
  HasExponentials_isExponential :>
    forall {A B : Ob C}, isExponential A B (expOb A B) (@eval A B) (@curry A B);
}.

Arguments expOb {C hp HasExponentials} _ _.
Arguments eval  {C hp HasExponentials A B}.
Arguments curry {C hp HasExponentials A B Z} _.

#[export] Hint Resolve HasExponentials_isExponential : typeclass_instances.

Lemma curry_comp :
  forall
    {C : Cat} {hp : HasProducts C} {he : HasExponentials C}
    [X Y Z A : Ob C] (f : Hom Y Z) (g : Hom Z A),
      curry (eval (A := X) .> f .> g) == curry (eval .> f) .> curry (eval .> g).
Proof.
  intros.
  rewrite equiv_exponential', exp_comp.
  now rewrite ProductFunctor_fmap_comp_l, !comp_assoc, exp_comp, <- !comp_assoc, exp_comp.
Qed.

Lemma uncurry_id :
  forall {C : Cat} {hp : HasProducts C} {he : HasExponentials C} {A B : Ob C},
    uncurry (id (expOb A B)) == eval.
Proof.
  intros. unfold uncurry.
  now rewrite ProductFunctor_fmap_id, comp_id_l.
Qed.

Ltac solve_exponential := intros; repeat
match goal with
| |- context [Proper] => proper; intros
| |- context [curry (eval .> (_ .> _))] =>
        rewrite <- (comp_assoc eval); rewrite curry_comp
| |- curry _ == id _ => rewrite <- curry_eval
| |- curry _ == curry _ => apply Proper_curry
| |- _ .> _ == _ .> _ => try (f_equiv; auto; fail)
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- ?x == ?x => reflexivity
end.

Lemma HasExponentials_unique :
  forall
    {C : Cat} {hp : HasProducts C}
    (he : HasExponentials C) (he' : HasExponentials C) (A B : Ob C),
      @expOb C hp he A B ~ @expOb C hp he' A B.
Proof.
  intros. eapply isExponential_iso; typeclasses eauto.
Qed.

(* TODO: bifunctor *)

#[refine]
#[export]
Instance ExponentialFunctor
  {C : Cat} {hp : HasProducts C} {he : HasExponentials C} (A : Ob C) : Functor C C :=
{
  fob := fun B : Ob C => expOb A B;
  fmap := fun (A B : Ob C) (f : Hom A B) => curry (eval .> f)
}.
Proof.
  all: solve_exponential.
Defined.