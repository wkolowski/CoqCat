Require Export Cat.Base.

Class Cat : Type :=
{
    Ob : Type;
    Hom : Ob -> Ob -> Type;
    HomSetoid :> forall A B : Ob, Setoid (Hom A B);
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper :> forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    comp_assoc : forall {A B C D : Ob} (f : Hom A B) (g : Hom B C)
        (h : Hom C D), comp (comp f g) h == comp f (comp g h);
    id : forall A : Ob, Hom A A;
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Arguments Ob _ : clear implicits.

Notation "f .> g" := (comp f g) (at level 50).

Hint Resolve comp_assoc id_left id_right.

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
    | Id : forall X : Ob C, exp X X
    | Var : forall X Y : Ob C, Hom X Y -> exp X Y
    | Comp : forall X Y Z : Ob C,
        exp X Y -> exp Y Z -> exp X Z.

Arguments Id [C] _.
Arguments Var [C X Y] _.
Arguments Comp [C X Y Z] _ _.

Hint Constructors exp.

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp X Y)
    : Hom X Y :=
match e with
    | Id X => id X
    | Var f => f
    | Comp e1 e2 => expDenote e1 .> expDenote e2
end.

Fixpoint simplify {C : Cat} {X Y : Ob C} (e : exp X Y) {struct e} : exp X Y.
Proof.
  destruct e.
    exact (Id _).
    exact (Var h). destruct (simplify _ _ _ e1) as [| ? ? f1 | ? ? ? e11 e12]; clear e1.
      exact (simplify _ _ _ e2).
      destruct (simplify _ _ _ e2) as [| ? ? f2 | ? ? ? e21 e22]; clear e2.
        exact (Var f1).
        exact (Comp (Var f1) (Var f2)).
        exact (Comp (Var f1) (Comp e21 e22)).
      destruct (simplify _ _ _ e2) as [| ? ? f2 | ? ? ? e21 e22]; clear e2.
        exact (Comp e11 e12).
        exact (Comp (Comp e11 e12) (Var f2)).
        exact (Comp (Comp e11 e12) (Comp e21 e22)).
Defined.

Theorem simplify_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; simpl; try reflexivity.
    destruct (simplify e1); destruct (simplify e2); simpl in *;
    rewrite <- ?IHe1, <- ?IHe2, ?id_left, ?id_right; reflexivity.
Qed.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
    | HomNil : forall X : Ob C, HomList X X
    | HomCons : forall X Y Z : Ob C,
        Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil [C] _.
Arguments HomCons [C X Y Z] _ _.

Fixpoint expDenoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y)
    : Hom X Y :=
match l with
    | HomNil X => id X
    | HomCons h t => h .> expDenoteHL t
end.

Fixpoint Happ {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y)
    : HomList Y Z -> HomList X Z :=
match l1 with
    | HomNil _ => fun l2 => l2
    | HomCons h t => fun l2 => HomCons h (Happ t l2)
end.

Local Infix "+++" := (Happ) (at level 40).

Fixpoint flatten {C : Cat} {X Y : Ob C} (e : exp X Y)
    : HomList X Y :=
match e with
    | Id X => HomNil X
    | Var f => HomCons f (HomNil _)
    | Comp e1 e2 => flatten e1 +++ flatten e2
end.

Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL l1 .> expDenoteHL l2 == expDenoteHL (l1 +++ l2).
Proof.
  induction l1; simpl; intros.
    rewrite id_left. reflexivity.
    rewrite comp_assoc, IHl1. reflexivity.
Qed.

Theorem flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  induction e; cbn; rewrite <- ?expDenoteHL_comp_app, ?id_right.
    1-2: reflexivity.
    rewrite IHe1, IHe2. reflexivity.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten (simplify e1)) ==
    expDenoteHL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_correct in H. assumption.
Qed.

Theorem cat_expand :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenote e1 == expDenote e2 ->
      expDenoteHL (flatten (simplify e1)) ==
      expDenoteHL (flatten (simplify e2)).
Proof.
  intros. rewrite !flatten_correct, !simplify_correct. assumption.
Qed.

Ltac reify mor :=
match mor with
    | id ?X => constr:(Id X)
    | ?f .> ?g =>
        let e1 := reify f in
        let e2 := reify g in constr:(Comp e1 e2)
    | ?f => match type of f with
        | Hom ?X ?Y => constr:(Var f)
        | _ => fail
    end
end.

Ltac reflect_eqv H :=
match type of H with
    | ?f == ?g =>
        let e1 := reify f in
        let e2 := reify g in
          change (expDenote e1 == expDenote e2) in H;
          apply cat_expand in H; cbn in H;
          rewrite ?id_left, ?id_right in H
end.

Ltac reflect_cat :=
match goal with
    | |- ?f == ?g =>
        let e1 := reify f in
        let e2 := reify g in
          change (expDenote e1 == expDenote e2);
          apply cat_reflect; cbn; rewrite ?id_left, ?id_right
end.

Ltac assocr := rewrite comp_assoc.
Ltac assocl := rewrite <- comp_assoc.

Ltac assocr' := rewrite !comp_assoc.
Ltac assocl' := rewrite <- !comp_assoc.

Ltac cat := repeat (intros; my_simpl; cbn in *; eauto;
match goal with
    | |- _ == _ => progress (reflect_cat; try reflexivity)
    | |- ?x == ?x => reflexivity
    | H : _ == _ |- _ => progress (reflect_eqv H)
    | |- Equivalence _ => solve_equiv
    | |- Proper _ _ => proper
    | _ => cbn in *
end; eauto).

#[refine]
Instance Dual (C : Cat) : Cat :=
{|
    Ob := Ob C;
    Hom := fun A B : Ob C => Hom B A;
    HomSetoid := fun A B : Ob C => {| equiv := fun f g : Hom B A =>
        @equiv (Hom B A) (@HomSetoid C B A) f g |};
    comp := fun (X Y Z : Ob C) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
    id := @id C
|}.
Proof. Time all: cat. Defined.

Axiom dual_involution_axiom : forall (C : Cat), Dual (Dual C) = C.

(* Warning: the following also uses the JMeq_eq axiom *)
Require Import Logic.ProofIrrelevance.
Require Import FunctionalExtensionality.

Theorem cat_split : forall
  (Ob Ob' : Type)
  (Hom : Ob -> Ob -> Type)
  (Hom': Ob' -> Ob' -> Type)
  (HomSetoid : forall A B : Ob, Setoid (Hom A B))
  (HomSetoid' : forall A B : Ob', Setoid (Hom' A B))
  (comp : forall A B C : Ob, Hom A B -> Hom B C -> Hom A C)
  (comp' : forall A B C : Ob', Hom' A B -> Hom' B C -> Hom' A C)
  comp_Proper
  comp'_Proper
  comp_assoc
  comp_assoc'
  (id : forall A : Ob, Hom A A)
  (id' : forall A : Ob', Hom' A A)
  id_left
  id'_left
  id_right
  id'_right,
    Ob = Ob' -> JMeq Hom Hom' -> JMeq comp comp' -> JMeq id id' ->
    JMeq HomSetoid HomSetoid' ->
    @Build_Cat Ob Hom HomSetoid comp comp_Proper comp_assoc id id_left id_right =
    @Build_Cat Ob' Hom' HomSetoid' comp' comp'_Proper comp_assoc' id' id'_left id'_right.
Proof.
  intros. repeat
  match goal with
      | H : _ = _ |- _ => subst
      | H : JMeq _ _ |- _ => apply JMeq_eq in H
      | |- ?x = ?x => reflexivity
  end;
  f_equal; apply proof_irrelevance.
Qed.

Print Assumptions cat_split.

Theorem setoid_split : forall A A' equiv equiv' setoid_equiv setoid_equiv',
    A = A' -> JMeq equiv equiv' ->
    JMeq (@Build_Setoid A equiv setoid_equiv)
         (@Build_Setoid A' equiv' setoid_equiv').
Proof.
  intros. repeat
  match goal with
      | H : _ = _ |- _ => subst
      | H : JMeq _ _ |- _ => apply JMeq_eq in H
      | |- ?x = ?x => reflexivity
  end.
  f_equal.
  assert (setoid_equiv = setoid_equiv') by apply proof_irrelevance.
  rewrite H. trivial.
Qed.

Theorem dual_involution_theorem : forall (C : Cat), Dual (Dual C) = C.
Proof.
  destruct C. unfold Dual. apply cat_split; simpl; trivial.
  assert (forall (A : Type) (x y : A), x = y -> JMeq x y).
    intros. rewrite H. reflexivity.
    apply H. extensionality A. extensionality B. apply JMeq_eq.
      destruct (HomSetoid0 A B). apply setoid_split; trivial.
Qed.

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
Definition Iso {C : Cat} {A B : Ob C} (f : Hom A B ) : Prop :=
    exists g : Hom B A, f .> g == id A /\ g .> f == id B.
Definition Aut {C : Cat} {A : Ob C} (f : Hom A A) : Prop := Iso f.

Hint Unfold End Mon Epi Bim Sec Ret Iso Aut.

Theorem dual_mon_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Mon C A B f <-> @Epi (Dual C) B A f.
Proof.
  unfold Mon, Epi; split; intros.
    apply H. unfold comp, Dual in H0. assumption.
    apply H. unfold comp, Dual. assumption.
Restart.
  cat.
Qed.

Theorem dual_bim_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Bim C A B f <-> @Bim (Dual C) B A f.
Proof.
  unfold Bim; cat.
Qed.

Theorem dual_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Sec C A B f <-> @Ret (Dual C) B A f.
Proof.
  unfold Sec, Ret; split; intros.
  apply H. unfold Hom, comp, id, Dual in H. assumption.
Restart.
  cat.
Qed.

Theorem dual_iso_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Iso C A B f <-> @Iso (Dual C) B A f.
Proof.
  unfold Iso; split; intros; destruct H as [g [eq1 eq2]];
  exists g; split; assumption.
Restart.
  unfold Iso; cat.
Qed.

Theorem iso_inv_unique : forall {C : Cat} {A B : Ob C} (f : Hom A B),
    Iso f <-> exists!! g : Hom B A, (f .> g == id A /\ g .> f == id B).
Proof.
  unfold Iso; split; intros.
    destruct H as [g [inv1 inv2]]. exists g. cat; auto.
      assert (eq1 : y .> f .> g == g) by (rewrite H0; cat).
      assert (eq2 : y .> f .> g == y) by (rewrite comp_assoc, inv1; cat).
      rewrite <- eq1, eq2. reflexivity.
    cat.
Qed.

Hint Resolve dual_mon_epi dual_sec_ret dual_iso_self iso_inv_unique.

Definition isomorphic {C : Cat} (A B : Ob C) :=
    exists f : Hom A B, Iso f.

Definition uniquely_isomorphic {C : Cat} (A B : Ob C) :=
    exists!! f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Hint Unfold isomorphic uniquely_isomorphic setoid_unique.

Ltac uniso' f :=
match goal with
    | H : Iso f |- _ => rewrite iso_inv_unique in H;
        let f_inv := fresh f "_inv" in
        let f_inv_eq1 := fresh f "_inv_eq1" in
        let f_inv_eq2 := fresh f "_inv_eq2" in
        let f_inv_unique := fresh f "_inv_unique" in
        destruct H as [f_inv [[f_inv_eq1 f_inv_eq2] f_inv_unique]]
end.

Ltac iso := repeat  (intros;
match goal with
    | H : _ ~~ _ |- _ => red in H
    | H : _ ~ _ |- _ => red in H
    | |- context [_ ~~ _] => unfold uniquely_isomorphic
    | |- context [_ ~ _] => unfold isomorphic
    | H : exists _ : Hom _ _, Iso _ |- _ => destruct H
    | _ : Iso ?f |- _ => uniso' f
    | |- Iso _ => unfold Iso
    | |- exists _ : Hom _ _, _ => eexists
    | |- _ /\ _ => split
    | |- _ <-> _ => split
    | _ => cat
end).

Theorem dual_isomorphic_self : forall (C : Cat) (A B : Ob C),
    @isomorphic C A B <-> @isomorphic (Dual C) B A.
Proof.
  unfold isomorphic; simpl; split; intros;
  destruct H as [f [g [eq1 eq2]]]; exists f; red; cat.
Restart.
  iso.
Defined.

Theorem dual_unique_iso_self : forall (C : Cat) (A B : Ob C),
    @uniquely_isomorphic C A B <-> @uniquely_isomorphic (Dual C) A B.
Proof.
  (* It works, but it's slow — I don't know why. *)
  unfold uniquely_isomorphic, Dual. simpl; split; intros.
    destruct H as [f [f_iso H]].
      rewrite iso_inv_unique in f_iso. unfold Iso.
        destruct f_iso as [g [[eq1 eq2] unique]].
        exists g. cat. apply unique; rewrite (H x); cat.
    destruct H as [f [f_iso H]].
      rewrite iso_inv_unique in f_iso. unfold Iso.
        destruct f_iso as [g [[eq1 eq2] unique]].
        exists g. cat. apply unique; rewrite (H x); cat.
Restart.
  iso.
    apply x_inv_unique. cat; rewrite H0; iso.
    apply x_inv_unique. cat; rewrite H0; iso.
Time Qed.

Theorem unique_iso_is_iso : forall (C : Cat) (A B : Ob C), A ~~ B -> A ~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic.
  intros. destruct H as [f [H _]]. exists f; apply H.
Restart.
  unfold uniquely_isomorphic, isomorphic; cat.
Qed.

Hint Resolve dual_isomorphic_self dual_unique_iso_self unique_iso_is_iso.

(* The identity is unique. *)
Theorem id_unique_left : forall (C : Cat) (A : Ob C) (idA : Hom A A),
    (forall (B : Ob C) (f : Hom A B), idA .> f == f) -> idA == id A.
Proof.
  intros. specialize (H A (id A)). cat.
Qed.

Theorem id_unique_right : forall (C : Cat) (B : Ob C) (idB : Hom B B),
    (forall (A : Ob C) (f : Hom A B), f .> idB == f) -> idB == id B.
Proof.
  intros. specialize (H B (id B)). cat.
Qed.

Hint Resolve id_unique_left id_unique_right.

(* Relations between different types of morphisms. *)
Theorem sec_is_mon : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec f -> Mon f.
Proof.
  intros; unfold Sec, Mon in *; intros X h1 h2 eq. destruct H as (g, H).
  assert (eq2 : (h1 .> f) .> g == (h2 .> f) .> g).
    rewrite eq; reflexivity.
    rewrite !comp_assoc, H in eq2. cat.
Qed.

Theorem ret_is_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Ret f -> Epi f.
Proof.
  intros. unfold Ret, Epi in *. intros X h1 h2 eq. destruct H as (g, H).
  assert (eq2 : g .> (f .> h1) == g .> (f .> h2)).
    rewrite eq; reflexivity.
    rewrite <- 2 comp_assoc, H in eq2. cat.
Qed.

Theorem iso_is_sec : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Sec f.
Proof.
  unfold Iso, Sec; intros. destruct H as [g [eq1 eq2]]. exists g; assumption.
Restart.
  unfold Iso, Sec; cat.
Qed.

Theorem iso_is_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Ret f.
Proof.
  unfold Iso, Ret; intros. destruct H as [g [eq1 eq2]]. exists g; assumption.
Restart.
  unfold Iso, Ret; cat.
Qed.

Hint Resolve sec_is_mon ret_is_epi iso_is_sec iso_is_ret.

Theorem iso_iff_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
Proof.
  split; intros. cat.
  destruct H as [[g f_sec] [h f_ret]].
    assert (eq1 : h .> f .> g == h). rewrite comp_assoc. rewrite f_sec. cat.
    assert (eq2 : h .> f .> g == g). rewrite f_ret; cat.
    assert (eq : g == h). rewrite <- eq1, eq2. reflexivity.
    exists g. split. assumption. rewrite eq. assumption.
Defined.

Theorem iso_iff_sec_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Epi f.
Proof.
  split; intros.
    apply iso_iff_sec_ret in H. cat.
    unfold Iso, Sec, Epi in *. destruct H as [[g eq] H].
      exists g. split; try assumption.
      apply H. rewrite <- comp_assoc. rewrite eq. cat.
Defined.

Theorem iso_iff_mon_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Mon f /\ Ret f.
Proof.
  split; intros.
    apply iso_iff_sec_ret in H. cat.
    unfold Iso, Sec, Epi in *. destruct H as [H [g eq]].
    exists g. split; try assumption.
    apply H. rewrite comp_assoc. rewrite eq. cat.
Defined.

Hint Resolve iso_iff_sec_ret iso_iff_mon_ret iso_iff_sec_epi.

(* Characterizations. *)
Theorem mon_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon f <-> forall X : Ob C, injectiveS (fun g : Hom X A => g .> f).
Proof.
  unfold Mon, injectiveS; split; intros.
    apply H. assumption.
    apply H. assumption.
Restart.
  cat.
Qed.

Theorem epi_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Epi f <-> forall X : Ob C, injectiveS (fun g : Hom B X => f .> g).
Proof. cat. Qed.

Hint Resolve mon_char epi_char.

(* Composition theorems. *)
Theorem mon_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Mon f -> Mon g -> Mon (f .> g).
Proof.
  unfold Mon. cat. apply H, H0. reflect_cat. cat.
Defined.

Theorem epi_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Epi f -> Epi g -> Epi (f .> g).
Proof.
  unfold Epi. cat.
Defined.

Hint Resolve mon_comp epi_comp.

Theorem bim_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Bim f -> Bim g -> Bim (f .> g).
Proof.
  unfold Bim; cat.
Defined.

Theorem sec_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Sec f -> Sec g -> Sec (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. red. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc g h2). rewrite eq2. cat.
Defined.

Theorem ret_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Ret f -> Ret g -> Ret (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc h1 f). rewrite eq1. cat.
Defined.

Hint Resolve bim_comp sec_comp ret_comp.

Theorem iso_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Iso f -> Iso g -> Iso (f .> g).
Proof.
  intros. apply iso_iff_sec_ret; cat.
Defined.

Hint Resolve iso_comp.

Theorem aut_comp : forall (C : Cat) (X : Ob C)
    (f : Hom X X) (g : Hom X X), Aut f -> Aut g -> Aut (f .> g).
Proof. cat. Defined.

Hint Resolve aut_comp.

(* Composition properties. *)
Theorem mon_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Mon (f .> g) -> Mon f.
Proof.
  unfold Mon; intros. apply H. rewrite <- !comp_assoc.
  rewrite H0. reflexivity.
Defined.

Theorem epi_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Epi (f .> g) -> Epi g.
Proof.
  unfold Epi; intros. apply H.
  rewrite !comp_assoc. rewrite H0. reflexivity.
Defined.

Theorem sec_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Sec (f .> g) -> Sec f.
Proof.
  unfold Sec. destruct 1 as [h eq]. exists (g .> h). rewrite <- eq; cat.
Defined.

Theorem ret_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Ret (f .> g) -> Ret g.
Proof.
  unfold Ret. destruct 1 as [h eq]. exists (h .> f). cat.
Defined.

Theorem id_is_aut : forall (C : Cat) (X : Ob C), Aut (id X).
Proof. unfold Aut, Iso; intros; exists (id X); cat. Defined.

Hint Resolve mon_prop epi_prop sec_prop ret_prop id_is_aut.

Instance isomorphic_equiv (C : Cat) : Equivalence isomorphic.
Proof.
  split; do 2 red; intros.
  (* Reflexivity *) exists (id x). apply id_is_aut.
  (* Symmetry *) destruct H as [f [g [eq1 eq2]]]. exists g, f; auto.
  (* Transitivity *) destruct H as [f f_iso], H0 as [g g_iso].
    exists (f .> g). apply iso_comp; assumption.
Defined.