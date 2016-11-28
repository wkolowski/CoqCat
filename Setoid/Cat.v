Require Export Coq.Classes.SetoidClass.
Require Export Coq.Logic.ProofIrrelevance.
Require Export JMeq.

Set Universe Polymorphism.

Class Cat : Type :=
{
    Ob : Type;
    Hom : Ob -> Ob -> Type;
    HomSetoid :> forall A B : Ob, Setoid (Hom A B);
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper :> forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C)
        (h : Hom C D), comp (comp f g) h == comp f (comp g h);
    id : forall A : Ob, Hom A A;
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Arguments Ob _ : clear implicits.

Notation "f .> g" := (comp f g) (at level 50).

Hint Unfold Ob Hom.

Ltac cat_id := rewrite id_left || rewrite id_right.
Ltac cat_split := repeat
match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | _ => split
end.
Ltac cat_assoc := rewrite comp_assoc.
Ltac cat_assoc' := rewrite <- comp_assoc.
Ltac cat_aux := repeat (simpl || cat_split || intros || cat_id || cat_assoc ||
    reflexivity || subst; eauto).
Ltac cat_aux' := repeat (simpl || cat_split || intros || cat_id || cat_assoc' ||
    reflexivity || subst; eauto).
Ltac cat := cat_aux || cat_aux'.

Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
Proof.
  split.
(* Reflexivity *) split.
(* Symmetry *) unfold Symmetric. intros. rewrite H. trivial.
(* Transitivity *) unfold Transitive. intros. rewrite H, H0. trivial.
Defined.

Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B)
    : Setoid A := {| equiv := fun a a' : A => f a == f a' |}.
Proof.
  split.
(* Reflexivity *) unfold Reflexive. reflexivity.
(* Symmetry *) unfold Symmetric. intros. rewrite H. reflexivity.
(* Transitivity *) unfold Transitive. intros. rewrite H, H0. reflexivity.
Defined.

Instance Dual (C : Cat) : Cat :=
{|
    Ob := Ob C;
    Hom := fun A B : Ob C => Hom B A;
    HomSetoid := fun A B : Ob C => {| equiv := fun f g : Hom B A =>
        @equiv (Hom B A) (@HomSetoid C B A) f g |};
    comp := fun (X Y Z : Ob C) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
    id := @id C
|}.
split; unfold HomSetoid, Reflexive, Symmetric, Transitive; intros.
(* Reflexivity *) reflexivity.
(* Symmetry *) rewrite H; reflexivity.
(* Transitivity *) rewrite H, H0; reflexivity.
(* Comp is proper *) unfold Proper, respectful; simpl; intros.
    destruct C. rewrite H, H0. reflexivity.
(* Wut *) (*unfold Proper, respectful, Basics.flip, Basics.impl.
    simpl. intros. rewrite H, H0, H1. reflexivity.*)
(* Category laws *) cat. cat. cat.
Defined.

(*Theorem dual_involution : forall (C : Cat), Dual (Dual C) = C.
Proof.
  unfold Dual; intros. destruct C; simpl.
  f_equal; try apply proof_irrelevance. intros.
  apply proof_irrelevance.
Qed.*)

(*Theorem duality_principle : forall (P : Cat -> Prop),
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
Proof. trivial. Qed.*)

Theorem duality_principle : forall (P : Cat -> Prop),
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
Proof. trivial. Qed.

Definition End {C : Cat} {A B : Ob C} (f : Hom A B) : Prop := A = B.
Definition Mon {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
    forall (X : Ob C) (g h : Hom X A), g .> f == h .> f -> g == h.
Definition Epi {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
    forall (X : Ob C) (g h : Hom B X), f .> g == f .> h -> g == h.
Definition Bim {C : Cat} {A B : Ob C} (f : Hom A B) : Prop := Mon f /\ Epi f.
Definition Sec {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
    exists g : Hom B A, f .> g == id A.
Definition Ret {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
    exists g : Hom B A, g .> f == id B.
(*Definition Ret {C : Cat} {A B : Ob C} (f : Hom A B) : Type :=
    {g : Hom B A | g .> f == id B}.*)
Definition Iso {C : Cat} {A B : Ob C} (f : Hom A B ) : Prop :=
    exists g : Hom B A, f .> g == id A /\ g .> f == id B.
Definition Aut {C : Cat} {A : Ob C} (f : Hom A A) : Prop := Iso f.

Theorem dual_mon_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Mon C A B f <-> @Epi (Dual C) B A f.
unfold Mon, Epi; split; intros.
apply H. unfold comp, Dual in H0. assumption.
apply H. unfold comp, Dual. assumption.
Qed.

Theorem dual_bim_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Bim C A B f <-> @Bim (Dual C) B A f.
intros C A B f; unfold Bim. repeat rewrite (dual_mon_epi).
repeat split; destruct H; assumption.
Qed.

Theorem dual_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Sec C A B f <-> @Ret (Dual C) B A f.
Proof.
  unfold Sec, Ret; split; intros.
  apply H. unfold Hom, comp, id, Dual in H. assumption.
Qed.

Theorem dual_iso_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Iso C A B f <-> @Iso (Dual C) B A f.
unfold Iso; split; intros; destruct H as [g [eq1 eq2]];
exists g; split; assumption.
Qed.

Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A)
    : Prop := P x /\  (forall y : A, P y -> x == y).

Notation "'exists' !! x : A , P" :=
    (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).

Definition isomorphic {C : Cat} (A B : Ob C) :=
    exists f : Hom A B, Iso f.

Definition uniquely_isomorphic {C : Cat} (A B : Ob C) :=
    exists!! f : Hom A B, Iso f. (* /\ forall g : Hom A B, Iso g -> f == g.*)

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Hint Unfold isomorphic uniquely_isomorphic setoid_unique.

Theorem unique_iso_is_iso : forall (C : Cat) (A B : Ob C), A ~~ B -> A ~ B.
unfold uniquely_isomorphic, isomorphic.
intros. destruct H as [f [H _]]. exists f; apply H.
Qed.

Definition balanced `(C : Cat) : Prop :=
    forall (A B : Ob C) (f : Hom A B), Bim f -> Iso f.

(* The identity is unique. *)
Theorem id_unique_left : forall (C : Cat) (A : Ob C) (idA : Hom A A),
    (forall (B : Ob C) (f : Hom A B), idA .> f == f) -> idA == id A.
intros.
assert (eq1 : idA .> (id A) == id A). apply H.
assert (eq2 : idA .> (id A) == idA). cat.
rewrite <- eq1, eq2; reflexivity.
Qed.

Theorem id_unique_right : forall (C : Cat) (B : Ob C) (idB : Hom B B),
    (forall (A : Ob C) (f : Hom A B), f .> idB == f) -> idB == id B.
intros.
assert (eq1 : id B .> idB == id B). apply H.
assert (eq2 : id B .> idB == idB); cat.
rewrite <- eq1, eq2; reflexivity.
Qed.

(* Relations between different types of morphisms. *)
Theorem sec_is_mon : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec f -> Mon f.
intros. unfold Sec, Mon in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : (h1 .> f) .> g == (h2 .> f) .> g). rewrite eq; reflexivity.
rewrite comp_assoc, comp_assoc in eq2. rewrite H in eq2.
rewrite id_right, id_right in eq2. assumption.
Qed.

Theorem ret_is_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Ret f -> Epi f.
intros. unfold Ret, Epi in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : g .> (f .> h1) == g .> (f .> h2)). rewrite eq; reflexivity. 
rewrite <- comp_assoc, <- comp_assoc in eq2. rewrite H in eq2.
rewrite id_left, id_left in eq2. assumption.
Qed.

Theorem iso_is_sec : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Sec f.
unfold Iso, Sec; intros. destruct H as [g [eq1 eq2]].
exists g; assumption.
Qed.

Theorem iso_is_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Ret f.
unfold Iso, Ret; intros. destruct H as [g [eq1 eq2]].
exists g; assumption.
Qed.

(*Ltac simpl_mor := cat; match goal with
    | H : Mon ?f |- ?g .> ?f == ?h .> ?f => destruct H
    | H : Epi ?f |- ?f .> ?g == ?f .> ?g => destruct H
    | H : Sec ?f |- ?g .> ?f == ?h .> ?f => destruct H
    | H : Ret ?f |- ?f .> ?g == ?f .> ?g => destruct H
    | H : Iso ?f |- ?g .> ?f == ?h .> ?f => destruct H
    | H : Iso ?f |- ?f .> ?g == ?f .> ?g => destruct H
end.*)

(* Kinds of ordinary functions. *)
Definition injective {A B : Type} {SA : Setoid A} {SB : Setoid B}
    (f : A -> B) : Prop := forall a a' : A, f a == f a' -> a == a'.

Definition surjective {A B : Type} {S : Setoid B} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a == b.

Definition invertible {A B : Type} (S : Setoid B) (f : A -> B) : Type :=
    forall b : B, {a : A | f a == b}.

Definition bijective {A B : Type} {SA : Setoid A} {SB : Setoid B}
    (f : A -> B) : Prop := injective f /\ surjective f.

(* Characterizations. *)
Theorem mon_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon f <-> forall X : Ob C, injective (fun g : Hom X A => g .> f).
Proof.
  unfold Mon, injective; split; intros.
    apply H. assumption.
    apply H. assumption.
Qed.

Theorem epi_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Epi f <-> forall X : Ob C, injective (fun g : Hom B X => f .> g).
Proof.
  unfold Epi, injective; split; intros; apply H; assumption.
Qed.

Theorem iso_iff_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
Proof.
  split; intros.
    split.
      apply iso_is_sec; auto.
      apply iso_is_ret; auto.
    destruct H as [[g f_sec] [h f_ret]].
      assert (eq1 : h .> f .> g == h). cat. rewrite f_sec. cat.
      assert (eq2 : h .> f .> g == g). rewrite f_ret; cat.
      assert (eq : g == h). rewrite <- eq1, eq2. reflexivity.
      exists g. split. assumption. rewrite eq. assumption.
Qed.

Theorem iso_iff_sec_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Epi f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split.
assumption. apply ret_is_epi in H0. assumption.
unfold Iso, Sec, Epi in *. destruct H as [[g eq] H].
exists g. split. assumption.
apply H. rewrite <- comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_iff_mon_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Mon f /\ Ret f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split. Focus 2.
assumption. apply sec_is_mon in H; assumption.
unfold Iso, Sec, Epi in *. destruct H as [H [g eq]].
exists g. split. Focus 2. assumption.
apply H. rewrite comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_inv_unique : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> (exists g : Hom B A, (f .> g == id A /\ g .> f == id B) /\
    forall g' : Hom B A, f .> g' == id A /\ g' .> f == id B -> g == g').
split; intros; unfold Iso in H. destruct H as (g, [inv1 inv2]).
exists g. split. split; assumption.
intros h H; destruct H as (iso1, iso2).
assert (eq1 : h .> f .> g == g). rewrite iso2. cat.
assert (eq2 : h .> f .> g == h). rewrite comp_assoc, inv1. cat.
rewrite <- eq1, eq2. reflexivity.
unfold Iso. destruct H as [g [[eq1 eq2] H]].
exists g; split; assumption.
Qed.

(*Theorem dual_unique_iso_self : forall (C : Cat) (A B : Ob C),
    @uniquely_isomorphic C A B <-> @uniquely_isomorphic (Dual C) A B.
unfold uniquely_isomorphic; split; simpl; intros.
unfold Iso, Dual; simpl. apply iso_inv_unique.
destruct H as [f [[g [eq1 eq2]]]].
exists g. split. exists f. split; assumption. intros.
destruct H0.
*)

(* Composition theorems. *)
Theorem mon_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Mon f -> Mon g -> Mon (f .> g).
unfold Mon. intros cat A B C f g f_mon g_mon X h1 h2 H.
apply f_mon, g_mon. cat.
Qed.

Theorem epi_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Epi f -> Epi g -> Epi (f .> g).
unfold Epi; intros cat A B C f g f_epi g_epi X h1 h2 H.
apply g_epi, f_epi. cat.
Qed.

Theorem bim_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Bim f -> Bim g -> Bim (f .> g).
unfold Bim; intros. destruct H, H0.
split; [apply mon_comp; assumption | apply epi_comp; assumption].
Qed.

Theorem sec_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Sec f -> Sec g -> Sec (f .> g).
intros. unfold Sec in *. destruct H0 as (h1, eq1). destruct H as (h2, eq2). 
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : g .> (h1 .> h2) == (g .> h1) .> h2). cat.
rewrite HComp. rewrite eq1. cat.
Qed.

Theorem ret_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Ret f -> Ret g -> Ret (f .> g).
intros. unfold Ret in *. destruct H0 as (h1, eq1), H as (h2, eq2).
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : h2 .> (f .> g) == (h2 .> f) .> g). cat.
rewrite HComp. rewrite eq2. cat.
Qed.

Theorem iso_comp : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Iso f -> Iso g -> Iso (f .> g).
intros. apply iso_iff_sec_ret.
apply iso_iff_sec_ret in H. destruct H as (f_sec, f_ret).
apply iso_iff_sec_ret in H0. destruct H0 as (g_sec, g_ret).
split; [apply sec_comp; assumption | apply ret_comp; assumption].
Qed.

Theorem aut_comp : forall (cat : Cat) (A : Ob cat) (f : Hom A A) (g : Hom A A),
    Aut f -> Aut g -> Aut (f .> g).
intros; apply iso_comp; assumption.
Qed.

(* Composition properties. *)
Theorem mon_prop : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Mon (f .> g) -> Mon f.
unfold Mon; intros. apply H.
repeat rewrite <- comp_assoc. rewrite H0. reflexivity.
Qed.

Theorem epi_prop : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Epi (f .> g) -> Epi g.
unfold Epi; intros. apply H.
repeat rewrite comp_assoc. rewrite H0. reflexivity.
Qed.

Theorem sec_prop : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Sec (f .> g) -> Sec f.
unfold Sec; intros. destruct H as (h, eq).
exists (g .> h). rewrite <- eq; cat.
Qed.

Theorem ret_prop : forall (cat : Cat) (A B C : Ob cat) (f : Hom A B) (g : Hom B C),
    Ret (f .> g) -> Ret g.
unfold Ret; intros. destruct H as (h, eq).
exists (h .> f). cat.
Qed.

Theorem id_is_aut : forall (C : Cat) (A : Ob C), Aut (id A).
unfold Aut, Iso; intros; exists (id A); cat.
Qed.

Instance isomorphic_equiv (cat : Cat) : Equivalence isomorphic.
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

Instance Grpd (C : Cat) : Cat :=
{
    Ob := Ob C;
    Hom := fun A B : Ob C => {f : Hom A B | Iso f};
    HomSetoid := fun A B : Ob C =>
        Setoid_kernel_equiv (HomSetoid A B) (@proj1_sig (Hom A B) Iso)
}.
Proof.
  intros. destruct X as [f f_iso], X0 as [g g_iso].
    exists (f .> g). apply iso_comp; assumption.
  unfold Proper, respectful; intros;
    destruct x, y, x0, y0; simpl in *. rewrite H, H0. reflexivity.
  intros; destruct f, g, h; cat.  
  intro. exists (id A). apply id_is_aut.
  intros; destruct f; cat.
  intros; destruct f; cat.
Defined.

(*Print Grpd.*)