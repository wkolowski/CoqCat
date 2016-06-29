Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import ProofIrrelevance.

Require Import CatInstances.
Require Import BinProdCoprod.

(*  BIG, REALLY BIG BEWARE: the dual category instance somehow breaks
    projection definitions in Functor and FunctorAlt. *)
Instance DualHom `(C : Cat) : @CatHom Ob.
split. exact (fun A B : Ob => Hom B A).
Defined.

Print DualHom.

Instance DualComp `(cat : Cat) : @CatComp Ob (DualHom cat).
split; simpl; intros A B C f g. exact (g .> f).
Defined.

Instance DualId `(C : Cat) : @CatId Ob (DualHom C).
split. unfold Hom, DualHom. exact id.
Defined.

Instance Dual `(C : Cat) : @Cat Ob (DualHom C) (DualComp C) (DualId C).
split; destruct C, catHom, catComp, catId; simpl in *; cat.
Defined.
Print Cat'.

Definition Dual' (C : Cat') : Cat' :=
{|
    ob_ := ob_ C;
    hom_ := DualHom C;
    cmp_ := DualComp C;
    id_ := DualId C;
    inst_ := Dual C
|}.

Definition End' `(C : Cat) {A : Ob} (f : Hom A A) := End f.
Definition Mon' `(C : Cat) {A B : Ob} (f : Hom A B) := Mon f.
Definition Epi' `(C : Cat) {A B : Ob} (f : Hom A B) := Epi f.
Definition Sec' `(C : Cat) {A B : Ob} (f : Hom A B) := Sec f.
Definition Ret' `(C : Cat) {A B : Ob} (f : Hom A B) := Ret f.
Definition Iso' `(C : Cat) {A B : Ob} (f : Hom A B) := Iso f.
Definition Aut' `(C : Cat) {A : Ob} (f : Hom A A) := Aut f.

Theorem dual_mon_epi : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Mon' C f <-> Epi' (Dual C) f.
unfold Mon', Mon, Epi', Epi; split; intros.
unfold Hom, DualHom in f, g, h. apply H.
unfold comp, DualComp in H0. assumption.
apply H. unfold comp, DualComp. assumption.
Qed.

Theorem dual_sec_ret : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Sec' C f <-> Ret' (Dual C) f.
unfold Sec', Sec, Ret', Ret; split; intros.
unfold Hom, DualHom, comp, DualComp, id, DualId. assumption.
unfold Hom, DualHom, comp, DualComp, id, DualId in H. assumption.
Qed.

Theorem dual_iso_self : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Iso' C f <-> Iso' (Dual C) f.
unfold Iso', Iso; split; intros.
unfold Hom, DualHom, comp, DualComp, id, DualId.
destruct H as [g [eq1 eq2]]. exists g. split; assumption.
unfold Hom, DualHom, comp, DualComp, id, DualId in H.
destruct H as [g [eq1 eq2]]. exists g. split; assumption.
Qed.

Theorem dual_aut_self : forall `(C : Cat) (A : Ob) (f : Hom A A),
    Aut' C f <-> Aut' (Dual C) f.
unfold Aut', Aut; split; intros; apply dual_iso_self; assumption.
Qed.

Definition initial `(C : Cat) (I : Ob) := initial_object I.
Definition terminal `(C : Cat) (T : Ob) := terminal_object T.

Theorem dual_initial_terminal : forall `(C : Cat) (A : Ob),
    initial C A <-> terminal (Dual C) A.
unfold initial, initial_object, terminal, terminal_object; split; intros;
unfold Hom, DualHom, comp, DualComp; apply H.
Qed.

Definition prod' `(C : Cat) {A B : Ob} (P : Ob) (pA : Hom P A) (pB : Hom P B) :=
    is_product P pA pB.
Definition coprod' `(C : Cat) {A B : Ob} (P : Ob) (iA : Hom A P) (iB : Hom B P) :=
    is_coproduct P iA iB.

Theorem dual_prod_coprod : forall `(C : Cat) (A B P : Ob) (pA : Hom P A)
    (pB : Hom P B), prod' C P pA pB <-> coprod' (Dual C) P pA pB.
unfold prod', is_product, coprod', is_coproduct; split; intros;
unfold Hom, DualHom, comp, DualComp; apply H.
Qed.

Theorem duality : forall P : Cat' -> Prop,
    (forall C : Cat', P C) -> forall C : Cat', P (Dual' C).
trivial.
Qed.

Theorem dual_involution : forall (C : Cat'), Dual' (Dual' C) = C.
unfold Dual'; intros;
destruct C; destruct inst_;
destruct hom_, cmp_, id_;
simpl; f_equal; apply proof_irrelevance.
Qed.

Theorem coproduct_comm' : forall (C : Cat') (A B P : ob C) (iA : Hom A P)
    (iB : Hom B P), coprod' C P iA iB -> coprod' C P iB iA.
intro C. rewrite <- (dual_involution C). intros.
rewrite <- (dual_prod_coprod (Dual' C)) in *.
unfold prod' in *. apply product_comm. assumption.
Qed.

Definition Hom' (C : Cat') (A B : ob_ C) := @Hom (ob C) (hom_ C) A B.

Theorem iso_coprod : forall (C' : Cat') (A B C D P Q : ob C') (iA : Hom' C' A P)
    (iB : Hom' C' B P) (jC : Hom' C' C Q) (jD : Hom' C' D Q), 5 = 5.
    isomorphic C' C. -> B ~ D. -> coprod' C' P iA iB -> coprod' C' Q jC jD -> P ~ Q.
intros. rewrite <- (dual_involution C') in *.
