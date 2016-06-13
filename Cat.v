Require Import Coq.Setoids.Setoid.
Require Export CaseTactic.

Class CatHom {Ob : Type} : Type :=
{
    Hom : forall (A B : Ob), Type
}.

Class CatComp {Ob : Type} {catHom : CatHom} : Type :=
{
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C
}.
Class CatId {Ob : Type} {catHom : CatHom} : Type :=
{
    id : forall A : Ob, Hom A A
}.

Notation "f <. g" := (comp g f) (at level 50).
Notation "f .> g" := (comp f g) (at level 50).

Class Cat (Ob : Type) (catHom : @CatHom Ob) (catComp : CatComp) (catId : CatId) : Type :=
{
   comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
       (f .> g) .> h = f .> (g .> h);
   id_left : forall (A B : Ob) (f : Hom A B), id A .> f = f;
   id_right : forall (A B : Ob) (f : Hom A B), f .> id B = f
}.

Ltac cat_rw := rewrite id_left || rewrite id_right || rewrite comp_assoc.
Ltac cat_rw' := rewrite id_left || rewrite id_right || rewrite <- comp_assoc.
Ltac cat_simpl := repeat cat_rw.
Ltac cat_simpl' := repeat cat_rw'.
Ltac cat := repeat (intros || cat_rw || auto).

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

Definition isomorphic `{C : Cat} (A B : Ob) := exists f : Hom A B, Iso f.
Definition uniquely_isomorphic `{C : Cat} (A B : Ob) := exists! f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Definition balanced `(C : Cat) : Prop := forall (A B : Ob) (f : Hom A B),
    Iso f <-> Bim f.

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

Theorem iso_iff_sec_ret : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
split.
intros. unfold Sec, Ret, Iso in *.
destruct H as (g, H). destruct H as [Hl Hr].
split; exists g; assumption.
intros. destruct H as [f_sec f_ret].
assert (f_mon : Mon f). apply sec_is_mon. assumption.
unfold Mon, Sec, Ret, Iso in *.
destruct f_sec as (g, f_sec). destruct f_ret as (h, f_ret).
assert (eq1 : h .> f .> g = h). repeat (cat || rewrite f_sec).
assert (eq2 : h .> f .> g = g). rewrite f_ret; cat.
assert (eq : g = h). rewrite <- eq1, eq2. trivial.
exists g. split. assumption. rewrite eq. assumption.
Qed.

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

Theorem iso_inv_unique : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso f -> (exists! g : Hom B A, f .> g = id A /\ g .> f = id B).
intros; unfold Iso in H; destruct H as (g, [inv1 inv2]).
exists g. unfold unique; split. split; assumption.
intros h H; destruct H as (iso1, iso2).
assert (eq1 : h .> f .> g = g). rewrite iso2. cat.
assert (eq2 : h .> f .> g = h). rewrite comp_assoc, inv1. cat.
rewrite <- eq1. pattern h at 2. rewrite <- eq2. cat.
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

Print sig.

Record BareCat : Type := mkBareCat
{
    _A : Type;
    _h : @CatHom _A;
    _c : CatComp;
    _i : CatId;
    _C : @Cat _A _h _c _i
}.

Print BareCat.