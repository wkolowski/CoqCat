Require Import Coq.Setoids.Setoid.
(*Require Export CaseTactic.*)

Class CatHom {Ob : Type} : Type :=
{
    Hom : forall (A B : Ob), Type
}.

Class CatComp {Ob : Type} {catHom : CatHom} : Type :=
{
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C
}.

Notation "f .> g" := (comp f g) (at level 50).

Class CatId {Ob : Type} {catHom : CatHom} : Type :=
{
    id : forall A : Ob, Hom A A
}.

Class Cat (Ob : Type) (catHom : @CatHom Ob) (catComp : CatComp) (catId : CatId) : Type :=
{
   comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
       (f .> g) .> h = f .> (g .> h);
   id_left : forall (A B : Ob) (f : Hom A B), id A .> f = f;
   id_right : forall (A B : Ob) (f : Hom A B), f .> id B = f
}.

Record Cat' : Type := mkBareCat
{
    ob_ : Type;
    hom_ : @CatHom ob_;
    cmp_ : CatComp;
    id_ : CatId;
    inst_ : @Cat ob_ hom_ cmp_ id_
}.

Definition Cat_BareCat `(C : Cat) : Cat' := {| ob_ := Ob |}.
(* The rest gets inferred automagically. *)
(*Coercion Cat_BareCat : Cat >-> Cat'.*)

Definition BareCat_Cat (C : Cat') :
    (Cat (ob_ C) (hom_ C) (cmp_ C) (id_ C)) := inst_ C.
Coercion BareCat_Cat : Cat' >-> Cat.

Ltac cat_rw := rewrite id_left || rewrite id_right || rewrite comp_assoc.
Ltac cat_rw' := rewrite id_left || rewrite id_right || rewrite <- comp_assoc.
Ltac cat_simpl := repeat cat_rw.
Ltac cat_simpl' := repeat cat_rw'.
Ltac cat := repeat (intros || cat_rw || auto).

Definition ob `(C : Cat) := Ob.
Definition dom `(C : Cat) {A B : Ob} (_ : Hom A B) := A.
Definition cod `(C : Cat) {A B : Ob} (_ : Hom A B) := B.

Definition End `{C : Cat} {A B : Ob} (f : Hom A B) : Prop := A = B.
Definition Mon `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom X A), g .> f = h .> f -> g = h.
Definition Epi `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom B X), f .> g = f .> h -> g = h.
Definition Bim `{C : Cat} {A B : Ob} (f : Hom A B) : Prop := Mon f /\ Epi f.
Definition Sec `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, f .> g = id A.
Definition Ret `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, g .> f = id B.
Definition Iso `{C : Cat} {A B : Ob} (f : Hom A B ) : Prop :=
   exists g : Hom B A, f .> g = id A /\ g .> f = id B.
Definition Aut `{C : Cat} {A : Ob} (f : Hom A A) : Prop := Iso f.

Definition End' `{C : Cat} (A : Ob) : Type := {f : Hom A A | True}.
Definition Mon' `{C : Cat} (A B : Ob) : Type := {f : Hom A B | Mon f}.
Definition Epi' `{C : Cat} (A B : Ob) : Type := {f : Hom A B | Epi f}.
Definition Sec' `{C : Cat} (A B : Ob) : Type := {f : Hom A B | Sec f}.
Definition Ret' `{C : Cat} (A B : Ob) : Type := {f : Hom A B | Ret f}.
Definition Iso' `{C : Cat} (A B : Ob) : Type := {f : Hom A B | Iso f}.
Definition Aut' `{C : Cat} (A : Ob) : Type := {f : Hom A A | Aut f}.

Definition Iso'_Hom `(C : Cat) (A B : Ob) (f : Iso' A B) := proj1_sig f.
Coercion Iso'_Hom : Iso' >-> Hom.

Definition isomorphic `{C : Cat} (A B : Ob) : Prop := exists f : Hom A B, Iso f.
Definition uniquely_isomorphic `{C : Cat} (A B : Ob) := exists! f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Definition balanced `(C : Cat) : Prop := forall (A B : Ob) (f : Hom A B),
    Iso f <-> Bim f.

(* Kinds of ordinary functions. *)
Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall a a' : A, f a = f a' -> a = a'.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

(* The identity is unique. *)
Theorem id_unique_left : forall `(C : Cat) (A : Ob) (idA : Hom A A),
    (forall (B : Ob) (f : Hom A B), idA .> f = f) -> idA = id A.
intros.
assert (eq1 : idA .> (id A) = id A). apply H.
assert (eq2 : idA .> (id A) = idA); cat.
rewrite <- eq1, eq2; trivial.
Qed.

Theorem id_unique_right : forall `(C : Cat) (B : Ob) (idB : Hom B B),
    (forall (A : Ob) (f : Hom A B), f .> idB = f) -> idB = id B.
intros.
assert (eq1 : id B .> idB = id B). apply H.
assert (eq2 : id B .> idB = idB); cat.
rewrite <- eq1, eq2; trivial.
Qed.

(* Relations between different types of morphisms. *)
Theorem sec_is_mon : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Sec f -> Mon f.
intros. unfold Sec, Mon in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : (h1 .> f) .> g = (h2 .> f) .> g). rewrite eq; trivial.
rewrite comp_assoc, comp_assoc in eq2. rewrite H in eq2.
rewrite id_right, id_right in eq2. assumption.
Qed.

Theorem ret_is_epi : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Ret f -> Epi f.
intros. unfold Ret, Epi in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : g .> (f .> h1) = g .> (f .> h2)). rewrite eq; trivial.
rewrite <- comp_assoc, <- comp_assoc in eq2. rewrite H in eq2.
rewrite id_left, id_left in eq2. assumption.
Qed.

Theorem iso_is_sec : forall `(_ : Cat) (A B : Ob) (f : Hom A B),
    Iso f -> Sec f.
unfold Iso, Sec; intros. destruct H0 as [g [eq1 eq2]].
exists g; assumption.
Qed.

Theorem iso_is_ret : forall `(_ : Cat) (A B : Ob) (f : Hom A B),
    Iso f -> Ret f.
unfold Iso, Ret; intros. destruct H0 as [g [eq1 eq2]].
exists g; assumption.
Qed.

Ltac simpl_mor := cat; match goal with
    | [ H : Mon ?f |- ?g .> ?f = ?h .> ?f ] => f_equal
    | [ H : Epi ?f |- ?f .> ?g = ?f .> ?g ] => f_equal
    | [ H : Sec ?f |- ?g .> ?f = ?h .> ?f ] => f_equal
    | [ H : Ret ?f |- ?f .> ?g = ?f .> ?g ] => f_equal
    | [ H : Iso ?f |- ?g .> ?f = ?h .> ?f ] => f_equal
    | [ H : Iso ?f |- ?f .> ?g = ?f .> ?g ] => f_equal
end.

(*Theorem troll : forall `(_ : Cat) (A B C : Ob) (g h : Hom A B) (f : Hom B C),
   Iso f -> g .> f .> id C = h .> f.
intros. simpl_mor. f_equal. rewrite H.
*)

(* Characterizations. *)
Theorem mon_char : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Mon f <-> forall X : Ob, injective (fun g : Hom X A => g .> f).
unfold Mon, injective; split; intros.
apply H. assumption.
apply H. assumption.
Qed.

Theorem epi_char : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Epi f <-> forall X : Ob, injective (fun g : Hom B X => f .> g).
unfold Epi, injective; split; intros.
apply H. assumption.
apply H. assumption.
Qed.

Theorem iso_iff_sec_ret : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
split. intro; split.
apply iso_is_sec; assumption.
apply iso_is_ret; assumption.
intros. destruct H as [f_sec f_ret].
unfold Mon, Sec, Ret, Iso in *.
destruct f_sec as (g, f_sec). destruct f_ret as (h, f_ret).
assert (eq1 : h .> f .> g = h). repeat (cat || rewrite f_sec).
assert (eq2 : h .> f .> g = g). rewrite f_ret; cat.
assert (eq : g = h). rewrite <- eq1, eq2. trivial.
exists g. split. assumption. rewrite eq. assumption.
Qed.

Theorem iso_iff_sec_epi : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Sec f /\ Epi f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split.
assumption. apply ret_is_epi in H0. assumption.
unfold Iso, Sec, Epi in *. destruct H as [[g eq] H].
exists g. split. assumption.
apply H. rewrite <- comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_iff_mon_ret : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Mon f /\ Ret f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split. Focus 2.
assumption. apply sec_is_mon in H; assumption.
unfold Iso, Sec, Epi in *. destruct H as [H [g eq]].
exists g. split. Focus 2. assumption.
apply H. rewrite comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_inv_unique : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> (exists! g : Hom B A, f .> g = id A /\ g .> f = id B).
split; intros; unfold Iso in H; destruct H as (g, [inv1 inv2]).
exists g. unfold unique; split. split; assumption.
intros h H; destruct H as (iso1, iso2).
assert (eq1 : h .> f .> g = g). rewrite iso2. cat.
assert (eq2 : h .> f .> g = h). rewrite comp_assoc, inv1. cat.
rewrite <- eq1. pattern h at 2. rewrite <- eq2. cat.
unfold Iso. exists g; split; destruct inv1; assumption.
Qed.

(* Composition theorems. *)
Theorem mon_comp : forall `(_ : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Mon f -> Mon g -> Mon (f .> g).
unfold Mon in *; intros. apply H0, H1.
repeat rewrite comp_assoc; assumption.
Qed.

Theorem epi_comp : forall `(_ : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Epi f -> Epi g -> Epi (f .> g).
unfold Epi in *; intros. apply H1, H0.
repeat rewrite <- comp_assoc. assumption.
Qed.

Theorem bim_comp : forall `(_ : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Bim f -> Bim g -> Bim (f .> g).
unfold Bim; intros. destruct H0, H1.
split; [apply mon_comp; assumption | apply epi_comp; assumption].
Qed.

Theorem sec_comp : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Sec f -> Sec g -> Sec (f .> g).
intros. unfold Sec in *. destruct H0 as (h1, eq1). destruct H as (h2, eq2). 
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : g .> (h1 .> h2) = (g .> h1) .> h2). cat.
rewrite HComp. rewrite eq1. cat.
Qed.

Theorem ret_comp : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Ret f -> Ret g -> Ret (f .> g).
intros. unfold Ret in *. destruct H0 as (h1, eq1), H as (h2, eq2).
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : h2 .> (f .> g) = (h2 .> f) .> g). cat.
rewrite HComp. rewrite eq2. cat.
Qed.

Theorem iso_comp : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Iso f -> Iso g -> Iso (f .> g).
intros. apply iso_iff_sec_ret.
apply iso_iff_sec_ret in H. destruct H as (f_sec, f_ret).
apply iso_iff_sec_ret in H0. destruct H0 as (g_sec, g_ret).
split; [apply sec_comp; assumption | apply ret_comp; assumption].
Qed.

Theorem aut_comp : forall `(cat : Cat) (A : Ob) (f : Hom A A) (g : Hom A A),
    Aut f -> Aut g -> Aut (f .> g).
intros; apply iso_comp; assumption.
Qed.

(* Composition properties. *)
Theorem mon_prop : forall `(_ : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Mon (f .> g) -> Mon f.
unfold Mon; intros. apply H0.
repeat rewrite <- comp_assoc. rewrite H1. trivial.
Qed.

Theorem epi_prop : forall `(_ : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Epi (f .> g) -> Epi g.
unfold Epi; intros. apply H0.
repeat rewrite comp_assoc. rewrite H1. trivial.
Qed.

Theorem sec_prop : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Sec (f .> g) -> Sec f.
unfold Sec; intros. destruct H as (h, eq).
exists (g .> h). rewrite <- eq; cat.
Qed.

Theorem ret_prop : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Ret (f .> g) -> Ret g.
unfold Ret; intros. destruct H as (h, eq).
exists (h .> f). cat.
Qed.

Theorem id_is_aut : forall `(C : Cat) (A : Ob), Aut (id A).
unfold Aut, Iso; intros; exists (id A); cat.
Qed.

Instance isomorphic_equiv `(C' : Cat) : Equivalence isomorphic.
split.
(*Case "Reflexivity".*) unfold Reflexive. intro A. unfold isomorphic.
    exists (id A). apply id_is_aut.
(*Case "Symmetry".*) unfold Symmetric. intros A B iso.
    destruct iso as [f [g [eq1 eq2]]]. unfold isomorphic. exists g.
    unfold Iso. exists f; split; assumption.
(*Case "Transitivity".*) unfold Transitive. intros A B C H H'.
    destruct H as [f f_iso], H' as [g g_iso]. unfold isomorphic.
    exists (f .> g). apply iso_comp; assumption.
Defined.

(*Theorem mono_epi_dual : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Mon f <-> Epi f.*)

Inductive locally_small : Cat' -> Prop :=
    | small_c : forall (A : Set) (h : @CatHom A) (c : @CatComp A h)
        (i : @CatId A h) (C : Cat A h c i), locally_small (Cat_BareCat C).
(*Definition large (C : Cat') := ~ small C.*)
