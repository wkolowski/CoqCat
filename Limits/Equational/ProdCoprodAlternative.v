From Cat Require Export Cat.

Set Implicit Arguments.

Class HasProducts (C : Cat) : Type :=
{
  prodOb : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (prodOb A B) A;
  outr : forall {A B : Ob C}, Hom (prodOb A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
  fpair_Proper :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  universal :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B) (h : Hom X (prodOb A B)),
      fpair f g == h <-> f == h .> outl /\ g == h .> outr
}.

Arguments prodOb {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

(** (outl x, outr x) = x *)
Lemma fpair_id :
  fpair outl outr == id (prodOb A B).
Proof.
  rewrite universal, !id_left.
  split; reflexivity.
Qed.

(** outl (x, y) = x *)
Lemma fpair_outl :
  fpair f g .> outl == f.
Proof.
  destruct (universal f g (fpair f g)) as [[<- _] _]; reflexivity.
Qed.

(** outr (x, y) = y *)
Lemma fpair_outr :
  fpair f g .> outr == g.
Proof.
  destruct (universal f g (fpair f g)) as [[_ <-] _]; reflexivity.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  intros h.
  rewrite universal, !comp_assoc, fpair_outl, fpair_outr.
  split; reflexivity.
Qed.

End HasProducts.

Ltac prod := intros; try split;
repeat match goal with
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply fpair_Proper
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- fpair _ _ == id (prodOb _ _) => rewrite <- fpair_id; apply fpair_Proper
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Ltac prod' := cbn; intros; try split;
repeat match goal with
| |- context [fpair _ _ == _] => rewrite universal
| H : fpair _ _ == _ |- _ => rewrite universal in H
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply fpair_Proper
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- fpair _ _ == id (prodOb _ _) => rewrite <- fpair_id; apply fpair_Proper
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; cat
end.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (prodOb X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. prod. Qed.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. prod. Qed.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  finl : forall {A B : Ob C}, Hom A (coprodOb A B);
  finr : forall {A B : Ob C}, Hom B (coprodOb A B);
  copair :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  copair_Proper :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@copair A B X);
  universal' :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X) (h : Hom (coprodOb A B) X),
      copair f g == h <-> f == finl .> h /\ g == finr .> h
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments finl     {C HasCoproducts A B}.
Arguments finr     {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Section HasCoproducts.

Context
  [C : Cat] [hp : HasCoproducts C]
  [A B X Y : Ob C]
  (f : Hom A X) (g : Hom B X).

Lemma copair_id :
  copair finl finr == id (coprodOb X Y).
Proof.
  rewrite universal'.
  cat.
Qed.

Lemma copair_finl :
  finl .> copair f g == f.
Proof.
  destruct (universal' f g (copair f g)) as [[<- _] _]; reflexivity.
Qed.

Lemma copair_finr :
  finr .> copair f g == g.
Proof.
  destruct (universal' f g (copair f g)) as [[_ <-] _]; reflexivity.
Qed.

Lemma copair_post :
  forall h : Hom X Y,
    copair (f .> h) (g .> h) == copair f g .> h.
Proof.
  intros h.
  rewrite universal', <- !comp_assoc, copair_finl, copair_finr.
  split; reflexivity.
Qed.

End HasCoproducts.

Ltac coprod := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [finl .> copair _ _] => rewrite copair_finl
| |- context [finr .> copair _ _] => rewrite copair_finr
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply copair_Proper
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply copair_Proper
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Ltac coprod' := intros; try split;
repeat match goal with
| |- context [copair _ _ == _] => rewrite universal'
(* | |- context [_ == copair _ _] =>  *)
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [finl .> copair _ _] => rewrite copair_finl
| |- context [finr .> copair _ _] => rewrite copair_finr
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply copair_Proper
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply copair_Proper
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; cat
end.

Lemma copair_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) == copair (h1 .> finl) (h2 .> finr) .> copair f g.
Proof.
  intros.
  rewrite
    universal',
    <- !comp_assoc, copair_finl, copair_finr,
    !comp_assoc, copair_finl, copair_finr.
  split; reflexivity.
Qed.

Class HasBiproducts (C : Cat) : Type :=
{
  products :> HasProducts C;
  coproducts :> HasCoproducts C;
  product_is_coproduct : forall X Y : Ob C, prodOb X Y = coprodOb X Y
}.

Coercion products : HasBiproducts >-> HasProducts.
Coercion coproducts : HasBiproducts >-> HasCoproducts.

(** * Duality *)

#[refine]
#[export]
Instance HasProducts_Dual {C : Cat} (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  prodOb := @coprodOb C hp;
  fpair := @copair C hp;
  outl := @finl C hp;
  outr := @finr C hp;
}.
Proof. all: cbn; coprod'; cat. Defined.

#[refine]
#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coprodOb := @prodOb C hp;
  copair := @fpair C hp;
  finl := @outl C hp;
  finr := @outr C hp;
}.
Proof.
  - cat.
  - prod'.
Defined.

#[refine]
#[export]
Instance HasBiproducts_Dual (C : Cat) (hb : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  products := HasProducts_Dual (@coproducts C hb);
  coproducts := HasCoproducts_Dual (@products C hb);
}.
Proof.
  intros. destruct hb. cbn in *. rewrite product_is_coproduct0. reflexivity.
Defined.

(** * Equivalence of equational and traditional definitions *)

From Cat Require Limits.ProdCoprod.

Module Equiv.

#[refine]
#[export]
Instance hp_hpeq (C : Cat) (hp : ProdCoprod.HasProducts C) : HasProducts C :=
{
  prodOb := @ProdCoprod.prodOb C hp;
  outl := @ProdCoprod.proj1 C hp;
  outr := @ProdCoprod.proj2 C hp;
  fpair := @ProdCoprod.fpair C hp;
}.
Proof.
  split.
  - intros <-. ProdCoprod.fpair.
  - intros [-> ->]. ProdCoprod.fpair.
Defined.

#[refine]
#[export]
Instance hpeq_hp (C : Cat) (hp_eq : HasProducts C) : ProdCoprod.HasProducts C :=
{
  prodOb := @prodOb C hp_eq;
  proj1 := @outl C hp_eq;
  proj2 := @outr C hp_eq;
  fpair := @fpair C hp_eq;
}.
Proof.
  unfold ProdCoprod.product_skolem, setoid_unique. prod'.
Defined.

#[refine]
#[export]
Instance hp_hpeq' (C : Cat) (hp : ProdCoprod.HasCoproducts C) : HasCoproducts C :=
{
  coprodOb := @ProdCoprod.coprodOb C hp;
  finl := @ProdCoprod.coproj1 C hp;
  finr := @ProdCoprod.coproj2 C hp;
  copair := @ProdCoprod.copair C hp;
}.
Proof.
  split.
  - intros <-. ProdCoprod.copair.
  - intros [-> ->]. ProdCoprod.copair.
Defined.

#[refine]
#[export]
Instance hpeq_hp' (C : Cat) (hp_eq : HasCoproducts C) : ProdCoprod.HasCoproducts C :=
{
  coprodOb := @coprodOb C hp_eq;
  coproj1 := @finl C hp_eq;
  coproj2 := @finr C hp_eq;
  copair := @copair C hp_eq;
}.
Proof.
  coprod'.
Defined.

#[refine]
#[export]
Instance hb_hbeq (C : Cat) (hb : ProdCoprod.HasBiproducts C) : HasBiproducts C :=
{
  products := @hp_hpeq C (@ProdCoprod.products C hb);
  coproducts := @hp_hpeq' C (@ProdCoprod.coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

#[refine]
#[export]
Instance hbeq_hb (C : Cat) (hb : HasBiproducts C) : ProdCoprod.HasBiproducts C :=
{
  ProdCoprod.products := @hpeq_hp C (@products C hb);
  ProdCoprod.coproducts := @hpeq_hp' C (@coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

End Equiv.