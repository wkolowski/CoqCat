Require Export Coq.Classes.SetoidClass.
Require Export JMeq.

Polymorphic Class Cat : Type :=
{
    Ob : Type;
    Hom : forall A B : Ob, Type;
    Hom_Setoid :> forall A B : Ob, Setoid (Hom A B);
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper :> forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    id : forall A : Ob, Hom A A;
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
        comp (comp f g) h == comp f (comp g h);
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Notation "f .> g" := (comp f g) (at level 50).

Ltac cat_rw := rewrite id_left || rewrite id_right || rewrite comp_assoc.
Ltac cat_rw' := rewrite id_left || rewrite id_right || rewrite <- comp_assoc.
Ltac cat_simpl := repeat cat_rw.
Ltac cat_simpl' := repeat cat_rw'.
Ltac cat := repeat (intros || cat_rw || reflexivity || auto).

Ltac cat_simpl2 := rewrite id_left || rewrite id_right.
Ltac cat_rw2 := rewrite comp_assoc.
Ltac cat_rw2' := rewrite <- comp_assoc.
Ltac cat_aux := repeat (simpl || split || intros || cat_simpl2 || cat_rw2 || reflexivity || auto).
Ltac cat_aux' := repeat (simpl || split || intros || cat_simpl2 || cat_rw2' || reflexivity || auto).
Ltac cat2 := cat_aux || cat_aux'.

(*Instance Setoid_TypeEq (A : Type) : Setoid A := {| equiv := eq |}.*)
Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
split.
(* Reflexivity *) split.
(* Symmetry *) unfold Symmetric. intros. rewrite H. trivial.
(* Transitivity *) unfold Transitive. intros. rewrite H, H0. trivial.
Defined.
Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a == f a' |}.
split.
(* Reflexivity *) unfold Reflexive. reflexivity.
(* Symmetry *) unfold Symmetric. intros. rewrite H. reflexivity.
(* Transitivity *) unfold Transitive. intros. rewrite H, H0. reflexivity.
Defined.

Instance Dual (C : Cat) : Cat :=
{|
    Ob := @Ob C;
    Hom := fun A B : Ob => Hom B A;
    Hom_Setoid := fun A B : Ob => {| equiv := fun f g : Hom B A =>
        @equiv (Hom B A) (@Hom_Setoid C B A) f g |};
    comp := fun (X Y Z : Ob) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
    id := @id C
|}.
split; unfold Hom_Setoid, Reflexive, Symmetric, Transitive; intros.
(* Reflexivity *) reflexivity.
(* Symmetry *) rewrite H; reflexivity.
(* Transitivity *) rewrite H, H0; reflexivity.
(* Comp is proper *) unfold Proper, respectful; simpl; intros.
    destruct C. rewrite H, H0. reflexivity.
(* Wut *) (*unfold Proper, respectful, Basics.flip, Basics.impl.
    simpl. intros. rewrite H, H0, H1. reflexivity.*)
(* Category laws *) cat2. cat2. cat2.
Defined.

Theorem duality_principle : forall (P : Cat -> Prop),
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
trivial.
Qed.

Polymorphic Definition dom (C : Cat) {A B : Ob} (_ : Hom A B) := A.
Polymorphic Definition cod (C : Cat) {A B : Ob} (_ : Hom A B) := B.

Polymorphic Definition End {C : Cat} {A B : Ob} (f : Hom A B) : Prop := A = B.
Polymorphic Definition Mon {C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom X A), g .> f == h .> f -> g == h.
Polymorphic Definition Epi {C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom B X), f .> g == f .> h -> g == h.
Polymorphic Definition Bim {C : Cat} {A B : Ob} (f : Hom A B) : Prop := Mon f /\ Epi f.
Polymorphic Definition Sec {C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, f .> g == id A.
Polymorphic Definition Ret {C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, g .> f == id B.
Polymorphic Definition Iso {C : Cat} {A B : Ob} (f : Hom A B ) : Prop :=
   exists g : Hom B A, f .> g == id A /\ g .> f == id B.
Polymorphic Definition Aut {C : Cat} {A : Ob} (f : Hom A A) : Prop := Iso f.

Theorem dual_mon_epi : forall (C : Cat) (A B : Ob) (f : Hom A B),
    @Mon C A B f <-> @Epi (Dual C) B A f.
unfold Mon, Epi; split; intros.
apply H. unfold comp, Dual in H0. assumption.
apply H. unfold comp, Dual. assumption.
Qed.

Theorem dual_bim_self : forall (C : Cat) (A B : Ob) (f : Hom A B),
    @Bim C A B f <-> @Bim (Dual C) B A f.
intros C A B f; unfold Bim. repeat rewrite (dual_mon_epi).
repeat split; destruct H; assumption.
Qed.

Theorem dual_sec_ret : forall (C : Cat) (A B : Ob) (f : Hom A B),
    @Sec C A B f <-> @Ret (Dual C) B A f.
unfold Sec, Ret; split; intros.
apply H. unfold Hom, comp, id, Dual in H. assumption.
Qed.

Theorem dual_iso_self : forall (C : Cat) (A B : Ob) (f : Hom A B),
    @Iso C A B f <-> @Iso (Dual C) B A f.
unfold Iso; split; intros; destruct H as [g [eq1 eq2]];
exists g; split; assumption.
Qed.

Polymorphic Definition isomorphic {C : Cat} (A B : Ob) :=
    exists f : Hom A B, Iso f.
Polymorphic Definition uniquely_isomorphic {C : Cat} (A B : Ob) :=
    exists f : Hom A B, Iso f /\ forall g : Hom A B, Iso g -> f == g.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Theorem unique_iso_is_iso : forall (C : Cat) (A B : Ob), A ~~ B -> A ~ B.
unfold uniquely_isomorphic, isomorphic.
intros. destruct H as [f [H _]]. exists f; apply H.
Qed.

Polymorphic Definition balanced `(C : Cat) : Prop :=
    forall (A B : Ob) (f : Hom A B), Bim f -> Iso f.

(* Kinds of ordinary functions. *)
Polymorphic Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall a a' : A, f a = f a' -> a = a'.

Polymorphic Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Polymorphic Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

(* The identity is unique. *)
Theorem id_unique_left : forall (C : Cat) (A : Ob) (idA : Hom A A),
    (forall (B : Ob) (f : Hom A B), idA .> f == f) -> idA == id A.
intros.
assert (eq1 : idA .> (id A) == id A). apply H.
assert (eq2 : idA .> (id A) == idA). cat.
rewrite <- eq1, eq2; reflexivity.
Qed.

Theorem id_unique_right : forall (C : Cat) (B : Ob) (idB : Hom B B),
    (forall (A : Ob) (f : Hom A B), f .> idB == f) -> idB == id B.
intros.
assert (eq1 : id B .> idB == id B). apply H.
assert (eq2 : id B .> idB == idB); cat.
rewrite <- eq1, eq2; reflexivity.
Qed.

(* Relations between different types of morphisms. *)
Theorem sec_is_mon : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Sec f -> Mon f.
intros. unfold Sec, Mon in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : (h1 .> f) .> g == (h2 .> f) .> g). rewrite eq; reflexivity.
rewrite comp_assoc, comp_assoc in eq2. rewrite H in eq2.
rewrite id_right, id_right in eq2. assumption.
Qed.

Theorem ret_is_epi : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Ret f -> Epi f.
intros. unfold Ret, Epi in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : g .> (f .> h1) == g .> (f .> h2)). rewrite eq; reflexivity. 
rewrite <- comp_assoc, <- comp_assoc in eq2. rewrite H in eq2.
rewrite id_left, id_left in eq2. assumption.
Qed.

Theorem iso_is_sec : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Iso f -> Sec f.
unfold Iso, Sec; intros. destruct H as [g [eq1 eq2]].
exists g; assumption.
Qed.

Theorem iso_is_ret : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Iso f -> Ret f.
unfold Iso, Ret; intros. destruct H as [g [eq1 eq2]].
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
(*Theorem mon_char : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Mon f <-> forall X : Ob, injective (fun g : Hom X A => g .> f).
unfold Mon, injective; split; intros.
simpl in H0. apply H; assumption.
Qed.

Theorem epi_char : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Epi f <-> forall X : Ob, injective (fun g : Hom B X => f .> g).
unfold Epi, injective; split; intros; apply H; assumption.
Qed.*)

Theorem iso_iff_sec_ret : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
split. intro; split.
apply iso_is_sec; assumption.
apply iso_is_ret; assumption.
intros. destruct H as [f_sec f_ret].
unfold Mon, Sec, Ret, Iso in *.
destruct f_sec as (g, f_sec). destruct f_ret as (h, f_ret).
assert (eq1 : h .> f .> g == h). repeat (cat || rewrite f_sec).
assert (eq2 : h .> f .> g == g). rewrite f_ret; cat.
assert (eq : g == h). rewrite <- eq1, eq2. reflexivity.
exists g. split. assumption. rewrite eq. assumption.
Qed.

Theorem iso_iff_sec_epi : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Sec f /\ Epi f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split.
assumption. apply ret_is_epi in H0. assumption.
unfold Iso, Sec, Epi in *. destruct H as [[g eq] H].
exists g. split. assumption.
apply H. rewrite <- comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_iff_mon_ret : forall (C : Cat) (A B : Ob) (f : Hom A B),
    Iso f <-> Mon f /\ Ret f.
split; intros. apply iso_iff_sec_ret in H. destruct H. split. Focus 2.
assumption. apply sec_is_mon in H; assumption.
unfold Iso, Sec, Epi in *. destruct H as [H [g eq]].
exists g. split. Focus 2. assumption.
apply H. rewrite comp_assoc. rewrite eq. cat.
Qed.

Theorem iso_inv_unique : forall (C : Cat) (A B : Ob) (f : Hom A B),
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

(*Theorem dual_unique_iso_self : forall (C : Cat) (A B : Ob),
    @uniquely_isomorphic C A B <-> @uniquely_isomorphic (Dual C) A B.
unfold uniquely_isomorphic; split; simpl; intros.
unfold Iso, Dual; simpl. apply iso_inv_unique.
destruct H as [f [[g [eq1 eq2]]]].
exists g. split. exists f. split; assumption. intros.
destruct H0.
*)

(* Composition theorems. *)
Theorem mon_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Mon f -> Mon g -> Mon (f .> g).
unfold Mon. intros cat A B C f g f_mon g_mon X h1 h2 H.
apply f_mon, g_mon. cat.
Qed.

Theorem epi_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Epi f -> Epi g -> Epi (f .> g).
unfold Epi; intros cat A B C f g f_epi g_epi X h1 h2 H.
apply g_epi, f_epi. cat_simpl'. assumption.
Qed.

Theorem bim_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Bim f -> Bim g -> Bim (f .> g).
unfold Bim; intros. destruct H, H0.
split; [apply mon_comp; assumption | apply epi_comp; assumption].
Qed.

Theorem sec_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Sec f -> Sec g -> Sec (f .> g).
intros. unfold Sec in *. destruct H0 as (h1, eq1). destruct H as (h2, eq2). 
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : g .> (h1 .> h2) == (g .> h1) .> h2). cat.
rewrite HComp. rewrite eq1. cat.
Qed.

Theorem ret_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Ret f -> Ret g -> Ret (f .> g).
intros. unfold Ret in *. destruct H0 as (h1, eq1), H as (h2, eq2).
exists (h1 .> h2). rewrite comp_assoc.
assert (HComp : h2 .> (f .> g) == (h2 .> f) .> g). cat.
rewrite HComp. rewrite eq2. cat.
Qed.

Theorem iso_comp : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Iso f -> Iso g -> Iso (f .> g).
intros. apply iso_iff_sec_ret.
apply iso_iff_sec_ret in H. destruct H as (f_sec, f_ret).
apply iso_iff_sec_ret in H0. destruct H0 as (g_sec, g_ret).
split; [apply sec_comp; assumption | apply ret_comp; assumption].
Qed.

Theorem aut_comp : forall (cat : Cat) (A : Ob) (f : Hom A A) (g : Hom A A),
    Aut f -> Aut g -> Aut (f .> g).
intros; apply iso_comp; assumption.
Qed.

(* Composition properties. *)
Theorem mon_prop : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Mon (f .> g) -> Mon f.
unfold Mon; intros. apply H.
repeat rewrite <- comp_assoc. rewrite H0. reflexivity.
Qed.

Theorem epi_prop : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Epi (f .> g) -> Epi g.
unfold Epi; intros. apply H.
repeat rewrite comp_assoc. rewrite H0. reflexivity.
Qed.

Theorem sec_prop : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Sec (f .> g) -> Sec f.
unfold Sec; intros. destruct H as (h, eq).
exists (g .> h). rewrite <- eq; cat.
Qed.

Theorem ret_prop : forall (cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Ret (f .> g) -> Ret g.
unfold Ret; intros. destruct H as (h, eq).
exists (h .> f). cat.
Qed.

Theorem id_is_aut : forall (C : Cat) (A : Ob), Aut (id A).
unfold Aut, Iso; intros; exists (id A); cat2.
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
    Ob := @Ob C;
    Hom := fun A B : Ob => {f : Hom A B | Iso f};
    Hom_Setoid := fun A B : Ob =>
        Setoid_kernel_equiv (Hom_Setoid A B) (@proj1_sig (Hom A B) Iso)
}.
intros. destruct X as [f f_iso], X0 as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
unfold Proper, respectful; intros;
destruct x, y, x0, y0; simpl in *. rewrite H, H0. reflexivity.
intro. exists (id A). apply id_is_aut.
intros; destruct f, g, h; cat2.
intros; destruct f; cat2.
intros; destruct f; cat2.
Defined.

Print Grpd.
