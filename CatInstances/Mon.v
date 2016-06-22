Require Import Omega.
Require Import ProofIrrelevance.
Require Import ZArith.
Require Import Ring.
Require Import Sgr.
Require Import CatInstances.

Class Monoid {A : Type} : Type :=
{
    sgr_ :> @Sgr A;
    e : A;
    neutr_left : forall a : A, e & a = a;
    neutr_right : forall a : A, a & e = a
}.

Definition Monoid_Sgr `(_ : Monoid) := sgr_.
Coercion Monoid_Sgr : Monoid >-> Sgr.

Theorem mon_id_unique_l : forall `(A : Monoid) (a : A),
    (forall x : A, a & x = x) -> a = e.
intros. specialize (H e). rewrite neutr_right in H. assumption.
Qed.

Theorem mon_id_unique_r : forall `(A : Monoid) (a : A),
    (forall x : A, x & a = x) -> e = a.
intros. specialize (H e). rewrite neutr_left in H. symmetry; assumption.
Qed.

(*Theorem mon_id_unique_strong_l : forall `(A : Monoid) (a : A) (x : A),
    a & x = x -> a = e.
intros.
assert (a & x = e & x). rewrite H, neutr_left. trivial.
*)
Print HomSgr.

Class HomMon `(A : Monoid) `(B : Monoid) : Type :=
{
    f_ : HomSgr (sgr_) (sgr_);
    pres_e : f_ e = e 
}.

Definition HomMon_Fun `(_ : HomMon) := f_.
Coercion HomMon_Fun : HomMon >-> HomSgr.

Print HomMon.

Instance HomMonCat `(M : Monoid) : @CatHom unit.
split. intros. exact M.
Defined.

Instance CompMonCat `(M : Monoid) : @CatComp unit (HomMonCat M).
split; unfold Hom, HomMonCat; intros _ _ _ f g.
exact (f & g).
Defined.

Instance IdMonCat `(M : Monoid) : @CatId unit (HomMonCat M).
split; unfold Hom, HomMonCat; intros _. exact e.
Defined.

Instance CatMonCat `(M : Monoid)
    : @Cat unit (HomMonCat M) (CompMonCat M) (IdMonCat M).
split; unfold Hom, HomMonCat, comp, CompMonCat, id, IdMonCat.
intros _ _ _ _ f g h. rewrite op_assoc. trivial.
intros _ _ f. rewrite neutr_left. trivial.
intros _ _ f. rewrite neutr_right. trivial.
Defined.

Instance NatPlus : @Monoid nat.
split with (sgr_ := NatPlus) (e := 0);
intros; simpl; omega.
Defined.

Instance NatMult : @Monoid nat.
split with (sgr_ := NatMult) (e := 1);
intros; simpl; omega.
Defined.

Instance ListApp (A : Type) : @Monoid (list A).
split with (sgr_ := (ListApp A)) (e := nil);
intros; simpl; try rewrite List.app_nil_r; trivial.
Defined.

Instance ZPlus : @Monoid Z.
split with (sgr_ := ZPlus) (e := 0%Z);
intros; simpl; omega.
Defined.

Instance ZMult : @Monoid Z.
split with (sgr_ := ZMult) (e := 1%Z);
intros; simpl; destruct a; omega.
Defined.

(*Instance inj : HomSgr NatMult ZMult.
split with (fun n : nat => Z.of_nat n). 
simpl; induction a, b; trivial.
rewrite mult_0_r. trivial.
simpl. f_equal. repeat rewrite Pos.of_nat_succ.
SearchAbout Pos.of_nat.*)


(*Theorem hom_monoid_pres_e : forall `(A : Monoid) `(B : Monoid) (f : HomMon A B),
    f e = e.
intros. rewrite pres_e. trivial.*)

Theorem epi_sur_counterexample : 
