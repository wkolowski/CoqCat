Require Import Coq.Setoids.Setoid.

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

Theorem ids : forall `(C : Cat) (A : Ob), id A .> id A .> id A = id A.
intros; cat_simpl; trivial. 
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

Instance HomSets : @CatHom Set.
split. exact (fun A B : Set => A -> B).
Defined.

Instance CompSets : @CatComp Set HomSets.
split. exact (fun A B C : Set => fun (f : Hom A B) (g : Hom B C) =>
    fun a : A => g (f a)).
Defined.

Instance IdSets : @CatId Set HomSets.
split. exact (fun A : Set => fun a : A => a).
Defined.

Instance Sets : Cat Set HomSets CompSets IdSets.
split; trivial.
Defined.

Instance HomProp : @CatHom Prop.
split. exact(fun A B : Prop => A -> B).
Defined.

Instance CompProp : @CatComp Prop HomProp.
split. exact (fun A B C : Prop => fun (f : A -> B) (g : B -> C) =>
    fun a : A => g (f a)).
Defined.

Instance IdProp : @CatId Prop HomProp.
split. exact (fun A : Prop => fun a : A => a).
Defined.

Instance Props : Cat Prop HomProp CompProp IdProp.
split; auto.
Defined.

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

Theorem mon_comp : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Mon f -> Mon g -> Mon (f .> g).
intros. unfold Mon in *. intros X h1 h2 eq.
rewrite <- comp_assoc, <- comp_assoc in eq. apply H0 in eq. apply H in eq.
assumption.
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

Definition injective {A B : Type} (f : A -> B) : Prop := forall (a a' : A),
    f a = f a' -> a = a'.

(*Lemma lolz : forall (A B : Type) (f g : A -> B),
    f = g -> (forall a : A, f a = g a).
intros. rewrite H. trivial.
Qed.

Lemma fn_ext : forall (A B : Set) (f g : A -> B),
f = g -> forall a : A, f a = g a.
intros. rewrite H. trivial.
Qed.*)

Axiom fn_ext_axiom : forall {A B : Set} (f g : A -> B),
f = g <-> forall a : A, f a = g a.

Lemma const_fun : forall (A B : Set) (a : A) (b b' : B),
    b = b' <-> (fun _ : A => b) = (fun _ : A => b').
split; intros. rewrite H; trivial.
rewrite fn_ext_axiom in H. apply H. assumption.
Qed.

Theorem Sets_mon_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective in *; split; intros.
assert (H1 : (fun _ : A => a) = (fun _ => a')).
apply H. simpl. rewrite H0. trivial. 
apply const_fun in H1; [assumption | assumption].
apply fn_ext_axiom. intros. apply H. generalize a.
rewrite <- fn_ext_axiom. apply H0.
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

Theorem sec_prop : forall `(cat : Cat) (A B C : Ob) (f : Hom A B) (g : Hom B C),
    Sec (f .> g) -> Sec f.
intros. unfold Sec in *. destruct H as (h, eq).
exists (g .> h). rewrite comp_assoc in eq. assumption.
Qed.

Inductive empty : Set := .

Print eq.


Inductive hom_disc (A : Set) : A -> A -> Prop :=
    | hom_singl : forall a : A, hom_disc A a a.

Instance HomDiscrete (A : Set) : @CatHom A.
split. exact (fun a b : A => a = b).
Defined.

Instance HomDiscrete2 (A : Set) : @CatHom A.
split. exact (hom_disc A).
Defined.

Instance CompDiscrete (A : Set) : @CatComp A (@HomDiscrete A).
split. intros a b c f g; unfold Hom, HomDiscrete.
inversion f. inversion g. trivial.
Defined.

Instance CompDiscrete2 (A : Set) : @CatComp A (@HomDiscrete2 A).
split. intros a b c f g; unfold Hom, HomDiscrete2 in *.
inversion f. inversion g. exact (hom_singl A c).
Defined.

Instance IdDiscrete (A : Set) : @CatId A (@HomDiscrete A).
split. intros a. unfold Hom, HomDiscrete. trivial.
Defined.

Instance IdDiscrete2 (A : Set) : @CatId A (@HomDiscrete2 A).
split. intro a. unfold Hom, HomDiscrete2. constructor.
Defined.

Instance Discrete (A : Set) :
    Cat A (HomDiscrete A) (CompDiscrete A) (IdDiscrete A).
split; unfold Hom, HomDiscrete in *.
intros a b c d f g h. rewrite f, g, h; trivial.
intros a b f. rewrite f; trivial.
intros. rewrite f; trivial.
Defined.

Definition isomorphic `{C : Cat} (A B : Ob) := exists f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).

(* How to formulate this?
Theorem discr_is_thin : forall (A : Set) (C : @Discrete A), 5 = 5. *)

Definition is_product `{C : Cat} {A B : Ob} (P : Ob) (p1 : Hom P A) (p2 : Hom P B) :=
    forall X : Ob, exists u : Hom X P, forall (f : Hom X A) (g : Hom X B),
    f = u .> p1 /\ g = u .> p2.

Theorem product_comm : forall `(C : Cat) (A B : Ob) (P : Ob) (pA : Hom P A)
    (pB : Hom P B), is_product P pA pB -> is_product P pB pA.
unfold is_product in *; intros.
destruct (H X) as (u, H').
exists u. intros. destruct (H' g f) as (eq1, eq2).
split; assumption.
Qed.

Theorem proj_ret : forall `(C : Cat) (A B : Ob) (P : Ob) (pA : Hom P A)
    (pB : Hom P B), is_product P pA pB -> Ret pA.
unfold is_product, Ret in *; intros.
destruct (H A) as (u, H').
exists u. destruct (H' (id A) (u .> pB)) as (eq1, eq2).
rewrite eq1. trivial.
Qed.

(*Theorem product_iso_unique : forall `(C : Cat) (A B : Ob) (P : Ob)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob) (qA : Hom Q A) (qB : Hom Q B),
    is_product P pA pB -> is_product Q qA qB -> P ~ Q.
intros. assert (pA_ret : Ret pA). apply proj_ret with B pB; assumption.
unfold is_product, isomorphic in *.
destruct (H0 P) as (u1, iso1). destruct (H Q) as (u2, iso2).
exists u1. unfold Iso. exists u2. split.
assert (H1 : pA = u1 .> qA). apply (iso1 pA pB).
assert (H2 : qA = u2 .> pA). apply (iso2 qA qB).
rewrite H1 in H2.
assert (Eq : u1 .> u2 .> pA = u1 .> qA). apply iso1; assumption.*)

Definition is_big_product `{C : Cat} (I : Set) (A : I -> Ob) (P : Ob)
    (p : forall i : I, Hom P (A i)) := forall X : Ob, exists u : Hom X P,
    forall (i : I) (f : Hom X (A i)), f = u .> p i.

Theorem big_proj_ret : forall `(C : Cat) (I : Set) (A : I -> Ob) (P : Ob)
    (p : forall i : I, Hom P (A i)),
        is_big_product I A P p -> forall i : I, Ret (p i).
unfold is_big_product, Ret; intros.
destruct (H (A i)) as (u, H').
exists u. rewrite (H' i (id (A i))). trivial.
Qed.

Definition is_coproduct `{C : Cat} {A B : Ob} (P : Ob) (iA : Hom A P)
    (iB : Hom B P) := forall (X : Ob), exists u : Hom P X,
    forall (f : Hom A X) (g : Hom B X), f = iA .> u /\ g = iB .> u.

Theorem coproduct_comm : forall `(C : Cat) (A B : Ob) (P : Ob) (iA : Hom A P)
    (iB : Hom B P), is_coproduct P iA iB -> is_coproduct P iB iA.
intros. unfold is_coproduct in *. intro. destruct (H X) as (u, H').
exists u. intros. destruct (H' g f) as (eq1, eq2). split; assumption.
Qed.

Theorem inj_sec : forall `(C : Cat) (A B P : Ob) (iA : Hom A P) (iB : Hom B P),
    is_coproduct P iA iB -> Sec iA.
intros. unfold Sec, is_coproduct in *. destruct (H A) as (u, H').
exists u. destruct (H' (id A) (iB .> u)) as (eq1, eq2).
rewrite eq1; trivial.
Qed.

Definition big_coproduct `{C : Cat} (J : Set) (A : J -> Ob) (P : Ob)
    (i : forall j : J, Hom (A j) P) := forall (X : Ob), exists u : Hom P X,
    forall (j : J) (f : Hom (A j) X), f = i j .> u.

Theorem big_inj_sec : forall `(C : Cat) (J : Set) (A : J -> Ob) (P : Ob)
    (i : forall j : J, Hom (A j) P),
        big_coproduct J A P i -> forall j : J, Sec (i j).
unfold big_coproduct, Sec in *; intros.
destruct (H (A j)) as (u, H').
exists u. rewrite <- (H' j (id (A j))). trivial.
Qed.

Definition initial_object `{C : Cat} (I : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom I X, True.

Definition terminal_object `{C : Cat} (T : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom X T, True.

(*  Most likely there's no initial object in the category Sets, because there are
    no functions from the empty set to itself. *)

Definition is_singleton (A : Set) : Prop :=
    exists a : A, True /\ forall (x y : A), x = y.

(* Beware: requires function extensionality. *)
Theorem terminal_object_Sets : forall A : Set,
    is_singleton A -> terminal_object A.
unfold is_singleton, terminal_object; intros.
destruct H as [a [_ H]]. exists (fun _ : X => a).
simpl; unfold unique; split; [trivial | intros].
rewrite fn_ext_axiom. intros. apply H.
Qed.

Theorem init_ob_iso_unique : forall `(C : Cat) (I1 I2 : Ob),
    initial_object I1 -> initial_object I2 -> I1 ~ I2.
unfold initial_object, isomorphic; intros.
destruct (H I1) as (id1, [_ eq1]), (H0 I2) as (id2, [_ eq2]);
destruct (H I2) as (f, _), (H0 I1) as (g, _).
exists f; unfold Iso; exists g; split.
rewrite <- (eq1 (f .> g)); [rewrite <- (eq1 (id I1)); trivial | trivial].
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id I2)); trivial | trivial].
Qed.

Theorem final_ob_iso_unique : forall `(C : Cat) (T1 T2 : Ob),
    terminal_object T1 -> terminal_object T2 -> T1 ~ T2.
unfold terminal_object, isomorphic; intros.
destruct (H T1) as (id1, [_ eq1]), (H0 T2) as (id2, [_ eq2]);
destruct (H T2) as (f, _), (H0 T1) as (g, _).
exists g; unfold Iso; exists f; split.
rewrite <- (eq1 (g .> f)); [rewrite <- (eq1 (id T1)); trivial | trivial].
rewrite <- (eq2 (id T2)); [rewrite <- (eq2 (f .> g)); trivial | trivial].
Qed.

Theorem id_is_aut : forall `(C : Cat) (A : Ob), Aut (id A).
unfold Aut, Iso; intros; exists (id A); cat.
Qed.

(*Theorem iso_prod : forall `(_ : Cat) (A B C D P Q : Ob) (pA : Hom P A)
    (pB : Hom P B) (qC : Hom Q C) (qD : Hom Q D),
    A ~ C -> B ~ D -> is_product P pA pB -> is_product Q qC qD -> P ~ Q.
unfold isomorphic, is_product; intros.
destruct H0 as (f, iso_f), H1 as (g, iso_g).
destruct (H3 P) as (u1, eq1), (H2 Q) as (u2, eq2).
exists u1. unfold Iso. exists u2. split.*)

Theorem init_ob_mor_ret : forall `(_ : Cat) (I X : Ob) (f : Hom X I),
    initial_object I -> Ret f.
unfold initial_object, Ret; intros.
destruct (H0 X) as (g, [_ eq1]); destruct (H0 I) as (idI, [_ eq2]).
exists g.
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id I)); trivial | trivial].
Qed.

Theorem terminal_ob_mor_sec : forall `(_ : Cat) (T X : Ob) (f : Hom T X),
    terminal_object T -> Sec f.
unfold terminal_object, Ret; intros.
destruct (H0 X) as (g, [_ eq1]); destruct (H0 T) as (idT, [_ eq2]).
exists g.
rewrite <- (eq2 (f .> g)); [rewrite <- (eq2 (id T)); trivial | trivial].
Qed.

Definition zero_object `{_ : Cat} (Z : Ob) : Prop :=
    initial_object Z /\ terminal_object Z.

Definition balanced `(C : Cat) : Prop := forall (A B : Ob) (f : Hom A B),
    Iso f <-> Bim f.

Definition has_initial_object `(C : Cat) : Prop :=
    exists I : Ob, initial_object I.

Definition has_terminal_object `(C : Cat) : Prop :=
    exists T : Ob, terminal_object T.

Definition has_zero_object `(C : Cat) : Prop :=
    exists Z : Ob, zero_object Z.

Definition has_binary_products `(C : Cat) : Prop := forall (A B : Ob),
    exists (P : Ob) (pA : Hom P A) (pB : Hom P B), is_product P pA pB.

Definition has_binary_coproducts `(C : Cat) : Prop := forall (A B : Ob),
    exists (P : Ob) (iA : Hom A P) (iB : Hom B P), is_coproduct P iA iB.

Definition has_finite_products `(C : Cat) : Prop :=
    has_terminal_object C /\ has_binary_products C.

Definition has_finite_coproducts `(C : Cat) : Prop :=
    has_initial_object C /\ has_binary_coproducts C.

Class ObPart `(C : Cat) `(D : Cat) : Type :=
{
    fob : ob C -> ob D
}.
Definition ObPart_coercion `(_ : ObPart) := fob.
Coercion ObPart_coercion : ObPart >-> Funclass.

Class MorPart `(C : Cat) `(D : Cat) (fob : ObPart C D) : Type :=
{
    fhom : forall {A B : ob C}, Hom A B -> Hom (fob A) (fob B)
}.

Class Functor `(C : Cat) `(D : Cat) (fobInst : ObPart C D)
    (fhomInst : MorPart C D fobInst) : Type :=
{
    pres_comp : forall (A B C : ob C) (f : Hom A B) (g : Hom B C),
        fhom (f .> g) = fhom f .> fhom g;
    pres_id : forall A : ob C, fhom (id A) = id (fob A)
}.
Definition fn_fhom3 `(T : Functor) {A B : ob C} (f : Hom A B) := fhom f.
Coercion fn_fhom3 : Functor >-> Funclass.

Theorem functor_pres_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Sec f -> Sec (fhom f).
unfold Sec; intros.
destruct H as (g, H'). exists (fhom g).
rewrite <- pres_comp. rewrite <- pres_id. f_equal. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Ret f -> Ret (fhom f).
unfold Ret; intros. destruct H as (g, H'). exists (fhom g).
rewrite <- pres_comp, <- pres_id. apply f_equal; assumption.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Iso f -> Iso (fhom f).
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
destruct H as (H_sec, H_ret).
split. apply functor_pres_sec; assumption.
apply functor_pres_ret; assumption.
Qed.

Definition full `(T : Functor) : Prop := forall (A B : ob C)
    (g : Hom (fob A) (fob B)), exists f : Hom A B, fhom f = g.

Definition faithful `(T : Functor) : Prop := forall (A B : ob C)
    (f g : Hom A B), fhom f = fhom g -> f = g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : ob D),
    exists X : ob C, fob X ~ Y.

Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Sec (fhom f) -> Sec f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H).
destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Ret (fhom f) -> Ret f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Iso (fhom f) -> Iso f.
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H1.
destruct H1 as (H_sec, H_ret). split.
apply full_faithful_refl_sec with T; assumption.
apply full_faithful_refl_ret with T; assumption.
Qed.

Instance CAT : forall `(h : CatHom) `(cmp : @CatComp Ob h) `(id : @CatId Ob h),
    @CatHom (@Cat Ob h cmp id).
intros. split. exact Functor.

Generalizable Variables C D E fob1a fob2a fhom1a fhom2a.
Theorem comp_full : forall `(T1 : Functor C D )
    `(T2 : @Functor D E fob2a fhom2a)
    (TComp : Functor C E (fun A : ob C => fob2a (fob1a A))
        (forall A B : ob C, Hom A B -> Hom (fob2a (fob1a A)) (fob2a (fob1a B)))),
    full T1 -> full T2 -> full TComp.