From Cat Require Export Base.

Set Implicit Arguments.

(** * Categories *)

(** ** Definitions *)

Class Cat : Type :=
{
  Ob : Type;
  Hom : Ob -> Ob -> Type;
  HomSetoid :> forall A B : Ob, Setoid (Hom A B);
  comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
  Proper_comp :> forall A B C : Ob, Proper (equiv ==> equiv ==> equiv) (@comp A B C);
  comp_assoc :
    forall {A B C D : Ob} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp (comp f g) h == comp f (comp g h);
  id : forall A : Ob, Hom A A;
  id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
  id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Arguments Ob _ : clear implicits.

Notation "f .> g" := (comp f g) (at level 50).

#[global] Hint Resolve comp_assoc id_left id_right : core.

(** ** Reflective tactic for categories *)

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
| Id   : forall X     : Ob C, exp X X
| Var  : forall X Y   : Ob C, Hom X Y -> exp X Y
| Comp : forall X Y Z : Ob C, exp X Y -> exp Y Z -> exp X Z.

Arguments Id [C] _.
Arguments Var [C X Y] _.
Arguments Comp [C X Y Z] _ _.

#[global] Hint Constructors exp : core.

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp X Y) : Hom X Y :=
match e with
| Id X       => id X
| Var f      => f
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

Lemma simplify_correct :
  forall {C : Cat} {X Y : Ob C} (e : exp X Y),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; cbn; try reflexivity.
    destruct (simplify e1); destruct (simplify e2); cbn in *;
    rewrite <- ?IHe1, <- ?IHe2, ?id_left, ?id_right; reflexivity.
Qed.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
| HomNil  : forall X : Ob C, HomList X X
| HomCons : forall X Y Z : Ob C, Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil [C] _.
Arguments HomCons [C X Y Z] _ _.

Fixpoint expDenoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y) : Hom X Y :=
match l with
| HomNil X    => id X
| HomCons h t => h .> expDenoteHL t
end.

Fixpoint Happ {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y) : HomList Y Z -> HomList X Z :=
match l1 with
| HomNil _    => fun l2 => l2
| HomCons h t => fun l2 => HomCons h (Happ t l2)
end.

Local Infix "+++" := (Happ) (at level 40).

Fixpoint flatten {C : Cat} {X Y : Ob C} (e : exp X Y) : HomList X Y :=
match e with
| Id X       => HomNil X
| Var f      => HomCons f (HomNil _)
| Comp e1 e2 => flatten e1 +++ flatten e2
end.

Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL l1 .> expDenoteHL l2 == expDenoteHL (l1 +++ l2).
Proof.
  induction l1; cbn; intros.
    rewrite id_left. reflexivity.
    rewrite comp_assoc, IHl1. reflexivity.
Qed.

Lemma expDenoteHL_flatten :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  induction e; cbn; rewrite <- ?expDenoteHL_comp_app, ?id_right.
    1-2: reflexivity.
    rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten (simplify e1)) ==
    expDenoteHL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !expDenoteHL_flatten, !simplify_correct in H. assumption.
Qed.

Lemma cat_expand :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenote e1 == expDenote e2 ->
      expDenoteHL (flatten (simplify e1)) ==
      expDenoteHL (flatten (simplify e2)).
Proof.
  intros. rewrite !expDenoteHL_flatten, !simplify_correct. assumption.
Qed.

Ltac reify mor :=
match mor with
| id ?X => constr:(Id X)
| ?f .> ?g =>
  let e1 := reify f in
  let e2 := reify g in constr:(Comp e1 e2)
| ?f =>
  match type of f with
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

(** ** Duality and equality *)

#[refine]
#[export]
Instance Dual (C : Cat) : Cat :=
{|
  Ob := Ob C;
  Hom := fun A B : Ob C => Hom B A;
  HomSetoid := fun A B : Ob C =>
  {|
    equiv := fun f g : Hom B A => @equiv (Hom B A) (@HomSetoid C B A) f g
  |};
  comp := fun (X Y Z : Ob C) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
  id := @id C
|}.
Proof. all: cat. Defined.

(* The following uses the [JMeq_eq] axiom. *)
Lemma cat_split : forall
  (Ob Ob' : Type)
  (Hom : Ob -> Ob -> Type)
  (Hom': Ob' -> Ob' -> Type)
  (HomSetoid : forall A B : Ob, Setoid (Hom A B))
  (HomSetoid' : forall A B : Ob', Setoid (Hom' A B))
  (comp : forall A B C : Ob, Hom A B -> Hom B C -> Hom A C)
  (comp' : forall A B C : Ob', Hom' A B -> Hom' B C -> Hom' A C)
  Proper_comp
  Proper_comp'
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
    @Build_Cat Ob Hom HomSetoid comp Proper_comp comp_assoc id id_left id_right =
    @Build_Cat Ob' Hom' HomSetoid' comp' Proper_comp' comp_assoc' id' id'_left id'_right.
Proof.
  intros. repeat
  match goal with
  | H : _ = _ |- _ => subst
  | H : JMeq _ _ |- _ => apply JMeq_eq in H
  | |- ?x = ?x => reflexivity
  end;
  f_equal; apply proof_irrelevance.
Qed.

Lemma setoid_split :
  forall A A' equiv equiv' setoid_equiv setoid_equiv',
    A = A' -> JMeq equiv equiv' ->
      JMeq (@Build_Setoid A equiv setoid_equiv) (@Build_Setoid A' equiv' setoid_equiv').
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

(*
Lemma Dual_Dual :
  forall C : Cat,
    Dual (Dual C) = C.
Proof.
  destruct C. unfold Dual. apply cat_split; cbn; trivial.
  assert (forall (A : Type) (x y : A), x = y -> JMeq x y).
    intros. rewrite H. reflexivity.
    apply H. extensionality A. extensionality B. apply JMeq_eq.
      destruct (HomSetoid0 A B). apply setoid_split; trivial.
Qed.
*)

Axiom Dual_Dual : forall (C : Cat), Dual (Dual C) = C.

Lemma duality_principle :
  forall P : Cat -> Prop,
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
Proof. trivial. Qed.

(** ** Kinds of morphisms and their properties *)

Definition End {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  A = B.
Definition Mon {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  forall (X : Ob C) (g h : Hom X A), g .> f == h .> f -> g == h.
Definition Epi {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  forall (X : Ob C) (g h : Hom B X), f .> g == f .> h -> g == h.
Definition Bim {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  Mon f /\ Epi f.
Definition Sec {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  exists g : Hom B A, f .> g == id A.
Definition Ret {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  exists g : Hom B A, g .> f == id B.
Definition Iso {C : Cat} {A B : Ob C} (f : Hom A B ) : Prop :=
  exists g : Hom B A, f .> g == id A /\ g .> f == id B.
Definition Aut {C : Cat} {A : Ob C} (f : Hom A A) : Prop :=
  Iso f.

#[global] Hint Unfold End Mon Epi Bim Sec Ret Iso Aut : core.

Lemma dual_mon_epi :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Mon C A B f <-> @Epi (Dual C) B A f.
Proof. cat. Qed.

Lemma dual_bim_self :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Bim C A B f <-> @Bim (Dual C) B A f.
Proof. unfold Bim; cat. Qed.

Lemma dual_sec_ret :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Sec C A B f <-> @Ret (Dual C) B A f.
Proof. cat. Qed.

Lemma dual_iso_self :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    @Iso C A B f <-> @Iso (Dual C) B A f.
Proof. unfold Iso; cat. Qed.

Lemma iso_inv_unique :
  forall {C : Cat} {A B : Ob C} (f : Hom A B),
    Iso f <-> exists!! g : Hom B A, (f .> g == id A /\ g .> f == id B).
Proof.
  unfold Iso; split; intros.
    destruct H as [g [inv1 inv2]]. exists g. cat; auto.
      assert (eq1 : y .> f .> g == g) by (rewrite H0; cat).
      assert (eq2 : y .> f .> g == y) by (rewrite comp_assoc, inv1; cat).
      rewrite <- eq1, eq2. reflexivity.
    cat.
Qed.

#[global] Hint Resolve dual_mon_epi dual_sec_ret dual_iso_self iso_inv_unique : core.

Definition isomorphic {C : Cat} (A B : Ob C) :=
  exists f : Hom A B, Iso f.

Definition uniquely_isomorphic {C : Cat} (A B : Ob C) :=
  exists!! f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

#[global] Hint Unfold isomorphic uniquely_isomorphic setoid_unique : core.

Ltac uniso' f :=
match goal with
| H : Iso f |- _ =>
  rewrite iso_inv_unique in H;
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

Lemma dual_isomorphic_self :
  forall (C : Cat) (A B : Ob C),
    @isomorphic C A B <-> @isomorphic (Dual C) B A.
Proof. iso. Defined.

Lemma dual_unique_iso_self :
  forall (C : Cat) (A B : Ob C),
    @uniquely_isomorphic C A B <-> @uniquely_isomorphic (Dual C) A B.
Proof.
  iso.
    apply x_inv_unique. cat; rewrite H0; iso.
    apply x_inv_unique. cat; rewrite H0; iso.
Qed.

Lemma unique_iso_is_iso :
  forall (C : Cat) (A B : Ob C), A ~~ B -> A ~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic; cat.
Qed.

#[global] Hint Resolve dual_isomorphic_self dual_unique_iso_self unique_iso_is_iso : core.

(* The identity is unique. *)
Lemma id_unique_left :
  forall (C : Cat) (A : Ob C) (idA : Hom A A),
    (forall (B : Ob C) (f : Hom A B), idA .> f == f) -> idA == id A.
Proof.
  intros. specialize (H A (id A)). cat.
Qed.

Lemma id_unique_right :
  forall (C : Cat) (B : Ob C) (idB : Hom B B),
    (forall (A : Ob C) (f : Hom A B), f .> idB == f) -> idB == id B.
Proof.
  intros. specialize (H B (id B)). cat.
Qed.

#[global] Hint Resolve id_unique_left id_unique_right : core.

(* Relations between different types of morphisms. *)
Lemma sec_is_mon :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec f -> Mon f.
Proof.
  intros; unfold Sec, Mon in *; intros X h1 h2 eq. destruct H as (g, H).
  assert (eq2 : (h1 .> f) .> g == (h2 .> f) .> g).
    rewrite eq; reflexivity.
    rewrite !comp_assoc, H in eq2. cat.
Qed.

Lemma ret_is_epi :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Ret f -> Epi f.
Proof.
  intros. unfold Ret, Epi in *. intros X h1 h2 eq. destruct H as (g, H).
  assert (eq2 : g .> (f .> h1) == g .> (f .> h2)).
    rewrite eq; reflexivity.
    rewrite <- 2 comp_assoc, H in eq2. cat.
Qed.

Lemma iso_is_sec :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Sec f.
Proof.
  unfold Iso, Sec; cat.
Qed.

Lemma iso_is_ret :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f -> Ret f.
Proof.
  unfold Iso, Ret; cat.
Qed.

#[global] Hint Resolve sec_is_mon ret_is_epi iso_is_sec iso_is_ret : core.

Lemma iso_iff_sec_ret :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Ret f.
Proof.
  split; intros. cat.
  destruct H as [[g f_sec] [h f_ret]].
    assert (eq1 : h .> f .> g == h). rewrite comp_assoc. rewrite f_sec. cat.
    assert (eq2 : h .> f .> g == g). rewrite f_ret; cat.
    assert (eq : g == h). rewrite <- eq1, eq2. reflexivity.
    exists g. split. assumption. rewrite eq. assumption.
Defined.

Lemma iso_iff_sec_epi :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Sec f /\ Epi f.
Proof.
  split; intros.
    apply iso_iff_sec_ret in H. cat.
    unfold Iso, Sec, Epi in *. destruct H as [[g eq] H].
      exists g. split; try assumption.
      apply H. rewrite <- comp_assoc. rewrite eq. cat.
Defined.

Lemma iso_iff_mon_ret :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso f <-> Mon f /\ Ret f.
Proof.
  split; intros.
    apply iso_iff_sec_ret in H. cat.
    unfold Iso, Sec, Epi in *. destruct H as [H [g eq]].
    exists g. split; try assumption.
    apply H. rewrite comp_assoc. rewrite eq. cat.
Defined.

#[global] Hint Resolve iso_iff_sec_ret iso_iff_mon_ret iso_iff_sec_epi : core.

(* Characterizations. *)
Lemma mon_char :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon f <-> forall X : Ob C, injectiveS (fun g : Hom X A => g .> f).
Proof.
  cat.
Qed.

Lemma epi_char :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Epi f <-> forall X : Ob C, injectiveS (fun g : Hom B X => f .> g).
Proof. cat. Qed.

#[global] Hint Resolve mon_char epi_char : core.

(* Composition theorems. *)
Lemma mon_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Mon f -> Mon g -> Mon (f .> g).
Proof.
  unfold Mon. cat. apply H, H0. reflect_cat. cat.
Defined.

Lemma epi_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Epi f -> Epi g -> Epi (f .> g).
Proof.
  unfold Epi. cat.
Defined.

#[global] Hint Resolve mon_comp epi_comp : core.

Lemma bim_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Bim f -> Bim g -> Bim (f .> g).
Proof.
  unfold Bim; cat.
Defined.

Lemma sec_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Sec f -> Sec g -> Sec (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. red. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc g h2). rewrite eq2. cat.
Defined.

Lemma ret_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Ret f -> Ret g -> Ret (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc h1 f). rewrite eq1. cat.
Defined.

#[global] Hint Resolve bim_comp sec_comp ret_comp : core.

Lemma iso_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Iso f -> Iso g -> Iso (f .> g).
Proof.
  intros. apply iso_iff_sec_ret; cat.
Defined.

#[global] Hint Resolve iso_comp : core.

Lemma aut_comp :
  forall (C : Cat) (X : Ob C) (f : Hom X X) (g : Hom X X),
    Aut f -> Aut g -> Aut (f .> g).
Proof. cat. Defined.

#[global] Hint Resolve aut_comp : core.

(* Composition properties. *)
Lemma mon_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Mon (f .> g) -> Mon f.
Proof.
  unfold Mon; intros. apply H. rewrite <- !comp_assoc.
  rewrite H0. reflexivity.
Defined.

Lemma epi_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Epi (f .> g) -> Epi g.
Proof.
  unfold Epi; intros. apply H.
  rewrite !comp_assoc. rewrite H0. reflexivity.
Defined.

Lemma sec_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Sec (f .> g) -> Sec f.
Proof.
  unfold Sec. destruct 1 as [h eq]. exists (g .> h). rewrite <- eq; cat.
Defined.

Lemma ret_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    Ret (f .> g) -> Ret g.
Proof.
  unfold Ret. destruct 1 as [h eq]. exists (h .> f). cat.
Defined.

Lemma id_is_aut :
  forall (C : Cat) (X : Ob C),
    Aut (id X).
Proof. unfold Aut, Iso; intros; exists (id X); cat. Defined.

#[global] Hint Resolve mon_prop epi_prop sec_prop ret_prop id_is_aut : core.

#[export]
Instance isomorphic_equiv (C : Cat) : Equivalence isomorphic.
Proof.
  split; do 2 red; intros.
  (* Reflexivity *) exists (id x). apply id_is_aut.
  (* Symmetry *) destruct H as [f [g [eq1 eq2]]]. exists g, f; auto.
  (* Transitivity *) destruct H as [f f_iso], H0 as [g g_iso].
    exists (f .> g). apply iso_comp; assumption.
Defined.

(** ** The category of setoids *)

(** [CoqSetoid] corresponds to what most category theory textbooks call Set,
    the category of sets and functions.

    We need to use setoids instead of sets, because our categories have a
    setoid of morphisms instead of a set/type. *)

Class Setoid' : Type :=
{
  carrier : Type;
  setoid :> Setoid carrier
}.

Coercion carrier : Setoid' >-> Sortclass.
Coercion setoid : Setoid' >-> Setoid.

Ltac setoidob S := try intros until S;
match type of S with
| Setoid =>
  let a := fresh S "_equiv" in
  let b := fresh S "_equiv_refl" in
  let c := fresh S "_equiv_sym" in
  let d := fresh S "_equiv_trans" in destruct S as [a [b c d]];
    red in a; red in b; red in c; red in d
| Setoid' =>
  let a := fresh S "_equiv" in
  let b := fresh S "_equiv_refl" in
  let c := fresh S "_equiv_sym" in
  let d := fresh S "_equiv_trans" in destruct S as [S [a [b c d]]];
    red in a; red in b; red in c; red in d
| Ob _ => progress cbn in S; setoidob S
end.

Ltac setoidobs := intros; repeat
match goal with
| S : Setoid |- _ => setoidob S
| S : Setoid' |- _ => setoidob S
| S : Ob _ |- _ => setoidob S
end.

Class SetoidHom (X Y : Setoid') : Type :=
{
  func : X -> Y;
  Proper_func :> Proper (@equiv _ X ==> @equiv _ Y) func
}.

Arguments func [X Y] _.
Arguments Proper_func [X Y] _.

Coercion func : SetoidHom >-> Funclass.

Ltac setoidhom f := try intros until f;
match type of f with
| SetoidHom _ _ =>
  let a := fresh f "_pres_equiv" in destruct f as [f a]; repeat red in a
| Hom _ _ => progress cbn in f; setoidhom f
end.

Ltac setoidhoms := intros; repeat
match goal with
| f : SetoidHom _ _ |- _ => setoidhom f
| f : Hom _ _ |- _ => setoidhom f
end.

Ltac setoid_simpl := repeat (red || split || cbn in * || intros).
Ltac setoid_simpl' := repeat (setoid_simpl || setoidhoms || setoidobs).

Ltac setoid' := repeat
match goal with
| |- Proper _ _ => proper
| |- Equivalence _ _ => solve_equiv
| _ => setoid_simpl || cat || setoidhoms || setoidobs
end.

Ltac setoid := try (setoid'; fail).

#[refine]
#[export]
Instance SetoidComp (X Y Z : Setoid') (f : SetoidHom X Y) (g : SetoidHom Y Z) : SetoidHom X Z :=
{
  func := fun x : X => g (f x)
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance SetoidId (X : Setoid') : SetoidHom X X :=
{
  func := fun x : X => x
}.
Proof. setoid. Defined.

#[refine]
#[global]
Instance CoqSetoid : Cat :=
{|
  Ob := Setoid';
  Hom := SetoidHom;
  HomSetoid := fun X Y : Setoid' =>
  {|
    equiv := fun f g : SetoidHom X Y => forall x : X, @equiv _ (@setoid Y) (f x) (g x)
  |};
  comp := SetoidComp;
  id := SetoidId
|}.
Proof. all: setoid. Defined.

(** * Functors *)

(** ** Covariant functor definitions *)

Class Functor (C : Cat) (D : Cat) : Type :=
{
  fob : Ob C -> Ob D;
  fmap : forall {A B : Ob C}, Hom A B -> Hom (fob A) (fob B);
  Proper_fmap :> forall A B : Ob C, Proper (equiv ==> equiv) (@fmap A B);
  pres_comp : forall {A B C : Ob C} (f : Hom A B) (g : Hom B C), fmap (f .> g) == fmap f .> fmap g;
  pres_id : forall A : Ob C, fmap (id A) == id (fob A)
}.

Arguments fob  [C D] _ _.
Arguments fmap [C D] _ [A B] _.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

(** ** Kinds of functors and their properties *)

Definition full {C D : Cat} (T : Functor C D) : Prop :=
  forall (A B : Ob C) (g : Hom (fob T A) (fob T B)),
    exists f : Hom A B, fmap T f == g.

Definition faithful {C D : Cat} (T : Functor C D) : Prop :=
  forall (A B : Ob C) (f g : Hom A B),
    fmap T f == fmap T g -> f == g.

Definition iso_dense {C D : Cat} (T : Functor C D) : Prop :=
  forall Y : Ob D, exists X : Ob C, fob T X ~ Y.

Definition embedding {C D : Cat} (T : Functor C D) : Prop :=
  faithful T /\ injective (fob T).

#[global] Hint Unfold full faithful iso_dense embedding : core.

Lemma functor_pres_sec :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    Sec f -> Sec (fmap T f).
Proof.
  unfold Sec; intros. destruct H as (g, H). exists (fmap T g).
  functor_simpl'. f_equiv. assumption.
Defined.

Lemma functor_pres_ret :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    Ret f -> Ret (fmap T f).
Proof.
  unfold Ret; cat. exists (fmap T x). rewrite <- pres_comp, e. functor.
Defined.

#[global] Hint Resolve functor_pres_sec functor_pres_ret : core.

Lemma functor_pres_iso :
  forall {C D : Cat} (T : Functor C D) {X Y : Ob C} (f : Hom X Y),
    Iso f -> Iso (fmap T f).
Proof. intros. rewrite iso_iff_sec_ret in *. cat. Defined.

Lemma full_faithful_refl_sec :
  forall {C D : Cat} (T : Functor C D) {X Y : Ob C} (f : Hom X Y),
    full T -> faithful T -> Sec (fmap T f) -> Sec f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_sec], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

Lemma full_faithful_refl_ret :
  forall {C D : Cat} (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Ret (fmap T f) -> Ret f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_ret], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

#[global] Hint Resolve full_faithful_refl_sec full_faithful_refl_ret : core.

Lemma full_faithful_refl_iso :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Iso (fmap T f) -> Iso f.
Proof.
  intros. rewrite iso_iff_sec_ret in *. destruct H1. split.
    eapply full_faithful_refl_sec; auto.
    eapply full_faithful_refl_ret; auto.
    (* TODO : cat should work here *)
Defined.

(** ** Identity, composition, constant and Hom functors *)

#[refine]
#[export]
Instance FunctorComp {C D E : Cat} (T : Functor C D) (S : Functor D E) : Functor C E :=
{
  fob := fun A : Ob C => fob S (fob T A);
  fmap := fun (X Y : Ob C) (f : Hom X Y) => fmap S (fmap T f)
}.
Proof.
  (* Proper *) proper.
  (* Functor laws *) all: functor.
Defined.

#[refine]
#[export]
Instance FunctorId (C : Cat) : Functor C C :=
{
  fob := fun A : Ob C => A;
  fmap := fun (X Y : Ob C) (f : Hom X Y) => f
}.
Proof.
  (* Proper *) proper.
  (* Functors laws *) all: functor.
Defined.

#[refine]
#[export]
Instance ConstFunctor {D : Cat} (X : Ob D) (C : Cat) : Functor C D :=
{
  fob := fun _ => X;
  fmap := fun _ _ _ => id X
}.
Proof. proper. all: functor. Defined.

#[refine]
#[export]
Instance HomFunctor (C : Cat) (X : Ob C) : Functor C CoqSetoid :=
{
  fob := fun Y : Ob C => {| carrier := Hom X Y; setoid := HomSetoid X Y |}
}.
Proof.
  intros A B f. exists (fun g => g .> f). proper.
  proper. all: cat.
Defined.

(** ** Contravariant functors *)

Class Contravariant (C : Cat) (D : Cat) : Type :=
{
  coob : Ob C -> Ob D;
  comap : forall {X Y : Ob C}, Hom X Y -> Hom (coob Y) (coob X);
  Proper_comap :> forall X Y : Ob C, Proper (equiv ==> equiv) (@comap X Y);
  comap_comp : forall (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z), comap (f .> g) == comap g .> comap f;
  comap_id : forall A : Ob C, comap (id A) == id (coob A)
}.

Arguments coob  [C D] _ _.
Arguments comap [C D] _ [X Y] _.

#[refine]
#[export]
Instance ConstContravariant {D : Cat} (X : Ob D) (C : Cat) : Contravariant C D :=
{
  coob := fun _ => X;
  comap := fun _ _ _ => id X
}.
Proof. proper. all: cat. Defined.

#[refine]
#[export]
Instance HomContravariant (C : Cat) (X : Ob C) : Contravariant C CoqSetoid :=
{
  coob := fun Y : Ob C => {| carrier := Hom Y X; setoid := HomSetoid Y X |}
}.
Proof.
  intros Y Z f. exists (fun g => f .> g). proper.
  proper. all: cat.
Defined.

(** ** Bifunctors *)

Class Bifunctor (C D E : Cat) : Type :=
{
  biob : Ob C -> Ob D -> Ob E;
  bimap :
    forall {X Y : Ob C} {X' Y' : Ob D},
      Hom X Y -> Hom X' Y' -> Hom (biob X X') (biob Y Y');
  Proper_bimap :>
    forall (X Y : Ob C) (X' Y' : Ob D),
      Proper (equiv ==> equiv ==> equiv) (@bimap X Y X' Y');
  bimap_pres_comp :
    forall
      (X Y Z : Ob C) (X' Y' Z' : Ob D)
      (f : Hom X Y) (g : Hom Y Z) (f' : Hom X' Y') (g' : Hom Y' Z'),
        bimap (f .> g) (f' .> g') == bimap f f' .> bimap g g';
  bimap_pres_id :
    forall (X : Ob C) (Y : Ob D),
      bimap (id X) (id Y) == id (biob X Y);
}.

Arguments biob  [C D E Bifunctor] _ _.
Arguments bimap [C D E Bifunctor X Y X' Y'] _ _.

Definition first
  {C D E : Cat} {F : Bifunctor C D E} {X Y : Ob C} {A : Ob D} (f : Hom X Y)
  : Hom (biob X A) (biob Y A) := bimap f (id A).

Definition second
  {C D E : Cat} {F : Bifunctor C D E} {A : Ob C} {X Y : Ob D} (f : Hom X Y)
  : Hom (biob A X) (biob A Y) := bimap (id A) f.

#[refine]
#[export]
Instance BiComp
  {C C' D D' E : Cat} (B : Bifunctor C' D' E) (F : Functor C C') (G : Functor D D')
  : Bifunctor C D E :=
{
  biob := fun (X : Ob C) (Y : Ob D) => biob (fob F X) (fob G Y);
  bimap := fun (X Y : Ob C) (X' Y' : Ob D) (f : Hom X Y) (g : Hom X' Y') =>
    bimap (fmap F f) (fmap G g)
}.
Proof.
  proper.
  intros. rewrite !pres_comp, !bimap_pres_comp. reflexivity.
  intros. rewrite 2 pres_id, bimap_pres_id. reflexivity.
Defined.

#[refine]
#[export]
Instance ConstBifunctor {E : Cat} (X : Ob E) (C D : Cat) : Bifunctor C D E :=
{
  biob := fun _ _ => X;
  bimap := fun _ _ _ _ _ _ => id X
}.
Proof. proper. all: cat. Defined.

(** ** Profunctors *)

Class Profunctor (C D E: Cat) : Type :=
{
  diob : Ob C -> Ob D -> Ob E;
  dimap :
    forall {X Y : Ob C} {X' Y' : Ob D},
      Hom X Y -> Hom X' Y' -> Hom (diob Y X') (diob X Y');
  Proper_dimap :>
    forall (X Y : Ob C) (X' Y' : Ob D),
      Proper (equiv ==> equiv ==> equiv) (@dimap X Y X' Y');
  dimap_comp :
    forall
      (X Y Z : Ob C) (X' Y' Z' : Ob D)
      (f : Hom X Y) (g : Hom Y Z) (f' : Hom X' Y') (g' : Hom Y' Z'),
        dimap (f .> g) (f' .> g') == dimap g f' .> dimap f g';
  dimap_id :
    forall (X : Ob C) (Y : Ob D),
      dimap (id X) (id Y) == id (diob X Y);
}.

Arguments diob  [C D E Profunctor] _ _.
Arguments dimap [C D E Profunctor X Y X' Y'] _ _.

Ltac profunctor_simpl := repeat (rewrite dimap_comp || rewrite dimap_id).

Ltac profunctor := repeat
match goal with
| |- context [Proper] => proper
| _ => cat; try functor_simpl; profunctor_simpl; cat
end.

#[refine]
#[export]
Instance ConstProfunctor {E : Cat} (X : Ob E) (C D : Cat) : Profunctor C D E :=
{
  diob := fun _ _ => X;
  dimap := fun _ _ _ _ _ _ => id X
}.
Proof. all: profunctor. Defined.

#[refine]
#[export]
Instance ProComp
  {C C' D D' E : Cat} (P : Profunctor C' D' E) (F : Functor C C') (G : Functor D D')
  : Profunctor C D E :=
{
  diob := fun (X : Ob C) (Y : Ob D) => diob (fob F X) (fob G Y)
}.
Proof.
  intros ? ? ? ? f g. exact (dimap (fmap F f) (fmap G g)).
  all: profunctor.
Defined.

#[refine]
#[export]
Instance HomProfunctor (C : Cat) : Profunctor C C CoqSetoid :=
{
  diob := fun X Y : Ob C => {| carrier := Hom X Y; setoid := HomSetoid X Y |};
}.
Proof.
  intros ? ? ? ? f g. exists (fun h : Hom Y X' => f .> h .> g). proper.
  all: profunctor.
Defined.

(** * The category of categories and functors *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

Lemma transport_transport :
  forall {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x),
    transport P q (transport P p u) = transport P (eq_trans p q) u.
Proof.
  intros A P x y z [] [] u; cbn; reflexivity.
Defined.

#[refine]
#[export]
Instance CATHomSetoid {C D : Cat} : Setoid (Functor C D) :=
{|
  equiv T S :=
    exists p : forall A : Ob C, fob T A = fob S A,
     forall (A B : Ob C) (f : Hom A B),
      transport (fun cod : Ob D => Hom (fob S A) cod) (p B)
        (transport (fun dom : Ob D => Hom dom (fob T B)) (p A) (fmap T f))
        =
      fmap S f
|}.
Proof.
  split; red.
  - intros F. exists (fun _ => eq_refl); cbn. reflexivity.
  - intros F G [p q]. exists (fun A => eq_sym (p A)).
    intros A B f. rewrite <- q; clear q. destruct (p A), (p B); cbn. reflexivity.
  - intros F G H [p1 q1] [p2 q2]. exists (fun X => eq_trans (p1 X) (p2 X)).
    intros A B f. rewrite <- q2, <- q1; clear q1 q2.
    destruct (p2 B), (p1 B), (p2 A), (p1 A); cbn. reflexivity.
Defined.

#[refine]
#[export]
Instance CAT : Cat :=
{
  Ob := Cat;
  Hom := Functor;
  HomSetoid := @CATHomSetoid;
  comp := @FunctorComp;
  id := FunctorId
}.
Proof.
  - cbn; intros A B C F G [p q] H I [r s].
    unfold FunctorComp; cbn.
    esplit. Unshelve. all: cycle 1.
    + intros X. clear q s. destruct (p X), (r (fob F X)). reflexivity.
    + intros X Y f. cbn.
      rewrite <- q, <- s; clear q s.
      destruct (p X), (p Y), (r (fob F X)), (r (fob F Y)); cbn.
      reflexivity.
  - cbn; intros A B C D F G H.
    exists (fun X => eq_refl).
    cbn; reflexivity.
  - intros A B F. exists (fun _ => eq_refl). cbn. reflexivity.
  - intros A B F. exists (fun _ => eq_refl). cbn. reflexivity.
Defined.

(** We also need to define the product of two categories, as this is needed
    in many places to define two-argument functors. *)

Definition ProdCatHom {C D : Cat} (X Y : Ob C * Ob D) : Type :=
  prod (Hom (fst X) (fst Y)) (Hom (snd X) (snd Y)).

#[refine]
#[export]
Instance ProdCatSetoid {C D : Cat} (X Y : Ob C * Ob D) : Setoid (ProdCatHom X Y) :=
{
  equiv := fun f g : ProdCatHom X Y => fst f == fst g /\ snd f == snd g
}.
Proof.
  split; red; intros; split; try destruct H; try destruct H0;
  try rewrite H; try rewrite H1; try rewrite H0; auto; reflexivity.
Defined.

#[refine]
#[export]
Instance CAT_prodOb (C : Cat) (D : Cat) : Cat :=
{
  Ob := Ob C * Ob D;
  Hom := ProdCatHom;
  HomSetoid := ProdCatSetoid;
  comp := fun
    (X Y Z : Ob C * Ob D)
    (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y))
    (g : Hom (fst Y) (fst Z) * Hom (snd Y) (snd Z)) =>
      (fst f .> fst g, snd f .> snd g);
  id := fun A : Ob C * Ob D => (id (fst A), id (snd A))
}.
Proof.
  (* Proper *) proper; my_simpl.
    rewrite H, H0. reflexivity.
    rewrite H1, H2. reflexivity.
  (* Category laws *) all: cat.
Defined.

(** * Natural transformations *)

Class NatTrans {C D : Cat} (T S : Functor C D) : Type :=
{
  component : forall X : Ob C, Hom (fob T X) (fob S X);
  coherence :
    forall [X Y : Ob C] (f : Hom X Y),
      component X .> fmap S f == fmap T f .> component Y
}.

Arguments component [C D T S] _ _.
Arguments coherence [C D T S] _ [X Y] _.

#[refine]
#[export]
Instance NatTransSetoid {C D : Cat} (F G : Functor C D) : Setoid (NatTrans F G) :=
{
  equiv := fun alfa beta : NatTrans F G =>
    forall X : Ob C, component alfa X == component beta X
}.
Proof.
  split; red; intros; try rewrite H; try rewrite H0; reflexivity.
Defined.

#[refine]
#[export]
Instance NatTransComp
  {C D : Cat} {F : Functor C D} {G : Functor C D} {H : Functor C D}
  (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H :=
{
  component := fun X : Ob C => component α X .> component β X
}.
Proof.
  intros. destruct α, β; cbn in *.
  rewrite !comp_assoc, coherence1, <- comp_assoc, coherence0. cat.
Defined.

#[refine]
#[export]
Instance NatTransId {C D : Cat} (F : Functor C D) : NatTrans F F :=
{
  component := fun X : Ob C => id (fob F X)
}.
Proof. cat. Defined.

(** ** Natural isomorphisms and representable functors *)

Definition natural_isomorphism
  {C D : Cat} {F G : Functor C D} (α : NatTrans F G) : Prop :=
    exists β : NatTrans G F,
      NatTransComp α β == NatTransId F /\
      NatTransComp β α == NatTransId G.

Lemma natural_isomorphism_char :
  forall (C D : Cat) (F G : Functor C D) (α : NatTrans F G),
    natural_isomorphism α <-> forall X : Ob C, Iso (component α X).
Proof.
  unfold natural_isomorphism; split; cbn; intros.
    destruct H as [β [Η1 Η2]]. red. exists (component β X). auto.
    red in H. destruct α as [component_α coherence_α]; cbn in *.
    assert (component_β : {f : forall X : Ob C, Hom (fob G X) (fob F X) |
    (forall X : Ob C, component_α X .> f X == id (fob F X) /\
      f X .> component_α X == id (fob G X)) /\
    (forall (X Y : Ob C) (g : Hom X Y), f X .> fmap F g == fmap G g .> f Y)}).
      pose (H' := fun X : Ob C => constructive_indefinite_description _ (H X)).
      exists (fun X : Ob C => proj1_sig (H' X)). split.
        intros. split; destruct (H' X); cat.
        intros. destruct (H' X), (H' Y). cbn in *. cat. clear H'.
        assert (
        x .> component_α X .> x .> fmap F g .> component_α Y .> x0 ==
        x .> component_α X .> fmap G g .> x0 .> component_α Y .> x0). cat.
          rewrite <- (comp_assoc (component_α X) x).
          rewrite <- (comp_assoc x0 (component_α Y)).
          rewrite <- (comp_assoc (fmap F g) _).
          rewrite <- (comp_assoc _ (fmap G g)).
          rewrite H2, H1, coherence_α. cat.
        rewrite H3 in H4. rewrite !comp_assoc in H4.
        rewrite H0 in H4. cat.
    destruct component_β as [component_β [inverse_α_β coherence_β]].
    eexists {| component := component_β; coherence := coherence_β |}.
    cat; apply inverse_α_β.
Defined.

Definition representable {C : Cat} (F : Functor C CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor C X)), natural_isomorphism α.

Definition corepresentable {C : Cat} (F : Functor (Dual C) CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor (Dual C) X)), natural_isomorphism α.