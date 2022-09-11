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
  comp_id_l : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
  comp_id_r : forall (A B : Ob) (f : Hom A B), comp f (id B) == f;
}.

Arguments Ob _ : clear implicits.

Notation "f .> g" := (comp f g) (at level 50).

#[global] Hint Resolve comp_assoc comp_id_l comp_id_r : core.

#[global] Hint Rewrite @comp_id_l @comp_id_r @comp_assoc : cat.

Ltac cat_simpl := autorewrite with cat in *.

(** *** The identity is unique *)

Lemma id_unique_left :
  forall (C : Cat) (A : Ob C) (idA : Hom A A),
    (forall (B : Ob C) (f : Hom A B), idA .> f == f) -> idA == id A.
Proof.
  now intros; rewrite <- (H _ (id A)), comp_id_r.
Qed.

Lemma id_unique_right :
  forall (C : Cat) (B : Ob C) (idB : Hom B B),
    (forall (A : Ob C) (f : Hom A B), f .> idB == f) -> idB == id B.
Proof.
  now intros; rewrite <- (H _ (id B)), comp_id_l.
Qed.

#[global] Hint Resolve id_unique_left id_unique_right : core.

(** ** Reflective tactic for categories *)

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
| Id   : forall X     : Ob C, exp X X
| Var  : forall X Y   : Ob C, Hom X Y -> exp X Y
| Comp : forall X Y Z : Ob C, exp X Y -> exp Y Z -> exp X Z.

Arguments Id   {C} _.
Arguments Var  {C X Y} _.
Arguments Comp {C X Y Z} _ _.

#[global] Hint Constructors exp : core.

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp X Y) : Hom X Y :=
match e with
| Id X       => id X
| Var f      => f
| Comp e1 e2 => expDenote e1 .> expDenote e2
end.

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
    now rewrite comp_id_l.
    now rewrite comp_assoc, IHl1.
Qed.

Lemma expDenoteHL_flatten :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  now induction e; cbn; rewrite <- ?expDenoteHL_comp_app, ?comp_id_r, ?IHe1, ?IHe2.
Qed.

Lemma cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten e1) ==
    expDenoteHL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite !expDenoteHL_flatten in H.
Qed.

Lemma cat_expand :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenote e1 == expDenote e2 ->
      expDenoteHL (flatten e1) ==
      expDenoteHL (flatten e2).
Proof.
  now intros; rewrite !expDenoteHL_flatten.
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
    rewrite ?comp_id_l, ?comp_id_r in H
end.

Ltac reflect_cat :=
match goal with
| |- ?f == ?g =>
  let e1 := reify f in
  let e2 := reify g in
    change (expDenote e1 == expDenote e2);
    apply cat_reflect; cbn; rewrite ?comp_id_l, ?comp_id_r
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
Proof.
  - apply HomSetoid.
  - proper.
  - now intros; rewrite comp_assoc.
  - now intros; rewrite comp_id_r.
  - now intros; rewrite comp_id_l.
Defined.

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
  comp_id_l
  id'_left
  comp_id_r
  id'_right,
    Ob = Ob' -> JMeq Hom Hom' -> JMeq comp comp' -> JMeq id id' ->
    JMeq HomSetoid HomSetoid' ->
    @Build_Cat Ob Hom HomSetoid comp Proper_comp comp_assoc id comp_id_l comp_id_r =
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

Lemma Dual_Dual :
  forall C : Cat,
    Dual (Dual C) = C.
Proof.
  intros []; apply cat_split; cbn; [easy | easy | easy | easy |].
  apply eq_JMeq; extensionality A; extensionality B; apply JMeq_eq.
  destruct (HomSetoid0 A B).
  now apply setoid_split.
Qed.

Lemma duality_principle :
  forall P : Cat -> Prop,
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
Proof. easy. Qed.

(** ** Kinds of morphisms and their properties *)

Definition isEndo {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  A = B.
Definition isMono {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  forall (X : Ob C) (g h : Hom X A), g .> f == h .> f -> g == h.
Definition isEpi {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  forall (X : Ob C) (g h : Hom B X), f .> g == f .> h -> g == h.
Definition isBi {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  isMono f /\ isEpi f.
Definition isSec {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  exists g : Hom B A, f .> g == id A.
Definition isRet {C : Cat} {A B : Ob C} (f : Hom A B) : Prop :=
  exists g : Hom B A, g .> f == id B.
Definition isIso {C : Cat} {A B : Ob C} (f : Hom A B ) : Prop :=
  exists g : Hom B A, f .> g == id A /\ g .> f == id B.
Definition isAut {C : Cat} {A : Ob C} (f : Hom A A) : Prop :=
  isIso f.

#[global] Hint Unfold isEndo isMono isEpi isBi isSec isRet isIso isAut : core.

(** *** Duality and subsumption *)

Lemma isMono_Dual :
  forall [C : Cat] [A B : Ob C] (f : @Hom (Dual C) A B),
    @isMono (Dual C) A B f = @isEpi C B A f.
Proof. easy. Defined.

Lemma isEpi_Dual :
  forall [C : Cat] [A B : Ob C] (f : @Hom (Dual C) A B),
    @isEpi (Dual C) A B f = @isMono C B A f.
Proof. easy. Defined.

Lemma isBi_Dual :
  forall (C : Cat) (A B : Ob C) (f : @Hom (Dual C) A B),
    @isBi (Dual C) A B f <-> @isBi C B A f.
Proof.
  intros.
  unfold isBi.
  rewrite isMono_Dual, isEpi_Dual.
  firstorder.
Qed.

Lemma isSec_Dual :
  forall [C : Cat] [A B : Ob C] (f : @Hom (Dual C) A B),
    @isSec (Dual C) A B f <-> @isRet C B A f.
Proof. easy. Defined.

Lemma isRet_Dual :
  forall [C : Cat] [A B : Ob C] (f : @Hom (Dual C) A B),
    @isRet (Dual C) A B f <-> @isSec C B A f.
Proof. easy. Defined.

Lemma isIso_Dual :
  forall [C : Cat] [A B : Ob C] (f : @Hom (Dual C) A B),
    @isIso (Dual C) A B f <-> @isIso C B A f.
Proof. firstorder. Qed.

Lemma isAut_Dual :
  forall [C : Cat] [A : Ob C] (f : @Hom (Dual C) A A),
    @isAut (Dual C) A f <-> @isAut C A f.
Proof. firstorder. Qed.

Lemma isIso_inv_unique :
  forall {C : Cat} {A B : Ob C} (f : Hom A B),
    isIso f <-> exists!! g : Hom B A, f .> g == id A /\ g .> f == id B.
Proof.
  unfold isIso; split; [| cat].
  intros (g & inv1 & inv2).
  exists g. split; [easy |]. intros y [_ H2].
  now rewrite <- comp_id_l, <- H2, comp_assoc, inv1, comp_id_r.
Qed.

#[global] Hint Resolve
  isMono_Dual isEpi_Dual isBi_Dual isSec_Dual isRet_Dual isIso_Dual isAut_Dual
  isIso_inv_unique
  : core.

Lemma isMono_isSec :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isSec f -> isMono f.
Proof.
  unfold isSec, isMono.
  intros C A B f [g Hfg] X h1 h2 Heq.
  now rewrite <- comp_id_r, <- Hfg, <- comp_assoc, Heq, comp_assoc, Hfg, comp_id_r.
Qed.

Lemma isEpi_isRet :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isRet f -> isEpi f.
Proof.
  unfold isRet, isEpi.
  intros C A B f [g Hgf] X h1 h2 Heq.
  now rewrite <- comp_id_l, <- Hgf, comp_assoc, Heq, <- comp_assoc, Hgf, comp_id_l.
Qed.

Lemma isSec_isIso :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isIso f -> isSec f.
Proof.
  unfold isIso, isSec; firstorder.
Qed.

Lemma isRet_isIso :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isIso f -> isRet f.
Proof.
  unfold isIso, isRet; firstorder.
Qed.

#[global] Hint Resolve isMono_isSec isEpi_isRet isSec_isIso isRet_isIso : core.

Lemma isIso_iff_isSec_isRet :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isIso f <-> isSec f /\ isRet f.
Proof.
  split; [firstorder |].
  intros [[g1 H1] [g2 H2]].
  exists (g2 .> f .> g1).
  split.
  - now rewrite H2, comp_id_l, H1.
  - now rewrite 2!comp_assoc, <- (comp_assoc f g1), H1, comp_id_l, H2.
Defined.

Lemma isIso_iff_isSec_isEpi :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isIso f <-> isSec f /\ isEpi f.
Proof.
  split; intros.
    apply isIso_iff_isSec_isRet in H. intuition.
    unfold isIso, isSec, isEpi in *. destruct H as [[g eq] H].
      exists g. split; [easy |]. apply H.
      now rewrite <- comp_assoc, eq, comp_id_l, comp_id_r.
Defined.

Lemma isIso_iff_isMono_isRet :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isIso f <-> isMono f /\ isRet f.
Proof.
  split; intros.
    apply isIso_iff_isSec_isRet in H. intuition.
    unfold isIso, isSec, isEpi in *. destruct H as [H [g eq]].
    exists g. split; [| easy].
    apply H. now rewrite comp_assoc, eq, comp_id_l, comp_id_r.
Defined.

#[global] Hint Resolve isIso_iff_isSec_isRet isIso_iff_isMono_isRet isIso_iff_isSec_isEpi : core.

(** *** Characterizations in terms of hom-sets *)

Lemma isMono_char :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isMono f <-> forall X : Ob C, injectiveS (fun g : Hom X A => g .> f).
Proof. easy. Defined.

Lemma isEpi_char :
  forall (C : Cat) (A B : Ob C) (f : Hom A B),
    isEpi f <-> forall X : Ob C, injectiveS (fun g : Hom B X => f .> g).
Proof. easy. Defined.

#[global] Hint Resolve isMono_char isEpi_char : core.

(** *** Identity properties *)

Lemma isMono_id :
  forall (C : Cat) (X : Ob C),
    isMono (id X).
Proof. now red; intros; cat_simpl. Defined.

Lemma isEpi_id :
  forall (C : Cat) (X : Ob C),
    isEpi (id X).
Proof. now red; intros; cat_simpl. Defined.

Lemma isBi_id :
  forall (C : Cat) (X : Ob C),
    isBi (id X).
Proof. red; cat. Defined.

Lemma isSec_id :
  forall (C : Cat) (X : Ob C),
    isSec (id X).
Proof. cat. Defined.

Lemma isRet_id :
  forall (C : Cat) (X : Ob C),
    isRet (id X).
Proof. cat. Defined.

Lemma isIso_id :
  forall (C : Cat) (X : Ob C),
    isIso (id X).
Proof. cat. Defined.

Lemma isAut_id :
  forall (C : Cat) (X : Ob C),
    isAut (id X).
Proof. cat. Defined.

#[global] Hint Resolve isMono_id isEpi_id isBi_id isSec_id isRet_id isIso_id isAut_id : core.

(** *** Composition properties *)

Lemma isMono_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isMono f -> isMono g -> isMono (f .> g).
Proof.
  unfold isMono; intros * Hf Hg W h1 h2 Heq.
  now apply Hf, Hg; cat_simpl.
Defined.

Lemma isEpi_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isEpi f -> isEpi g -> isEpi (f .> g).
Proof.
  unfold isEpi; intros * Hf Hg W h1 h2 Heq.
  now apply Hg, Hf; cat_simpl.
Defined.

#[global] Hint Resolve isMono_comp isEpi_comp : core.

Lemma isBi_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isBi f -> isBi g -> isBi (f .> g).
Proof.
  unfold isBi; cat.
Defined.

Lemma isSec_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isSec f -> isSec g -> isSec (f .> g).
Proof.
  unfold isSec; intros C X Y Z f g [h1 eq1] [h2 eq2].
  exists (h2 .> h1).
  now rewrite comp_assoc, <- (comp_assoc g h2), eq2, comp_id_l, eq1.
Defined.

Lemma isRet_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isRet f -> isRet g -> isRet (f .> g).
Proof.
  unfold isRet; intros C X Y Z f g [h1 eq1] [h2 eq2].
  exists (h2 .> h1).
  now rewrite comp_assoc, <- (comp_assoc h1 f), eq1, comp_id_l, eq2.
Defined.

#[global] Hint Resolve isBi_comp isSec_comp isRet_comp : core.

Lemma isIso_comp :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isIso f -> isIso g -> isIso (f .> g).
Proof.
  intros. apply isIso_iff_isSec_isRet. auto.
Defined.

#[global] Hint Resolve isIso_comp : core.

Lemma isAut_comp :
  forall (C : Cat) (X : Ob C) (f : Hom X X) (g : Hom X X),
    isAut f -> isAut g -> isAut (f .> g).
Proof. auto. Defined.

#[global] Hint Resolve isAut_comp : core.

(** *** Composition properties, reverse *)

Lemma isMono_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isMono (f .> g) -> isMono f.
Proof.
  unfold isMono; intros * HM W h1 h2 Heq.
  now apply HM; rewrite <- !comp_assoc, Heq.
Defined.

Lemma isEpi_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isEpi (f .> g) -> isEpi g.
Proof.
  unfold isEpi; intros * HE W h1 h2 Heq.
  now apply HE; rewrite !comp_assoc, Heq.
Defined.

Lemma isSec_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isSec (f .> g) -> isSec f.
Proof.
  unfold isSec; intros * [h Heq].
  exists (g .> h).
  now rewrite <- Heq, comp_assoc.
Defined.

Lemma isRet_prop :
  forall (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
    isRet (f .> g) -> isRet g.
Proof.
  unfold isRet; intros * [h Heq].
  exists (h .> f).
  now rewrite <- Heq, comp_assoc.
Defined.

#[global] Hint Resolve isMono_prop isEpi_prop isSec_prop isRet_prop : core.

(** *** Isomorphism machinery *)

Definition isomorphic {C : Cat} (A B : Ob C) : Prop :=
  exists f : Hom A B, isIso f.

Definition uniquely_isomorphic {C : Cat} (A B : Ob C) : Prop :=
  exists!! f : Hom A B, isIso f.

Definition Iso {C : Cat} (A B : Ob C) : Type :=
  {f : Hom A B | isIso f}.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

#[global] Hint Unfold isomorphic uniquely_isomorphic : core.

Ltac uniso' f :=
match goal with
| H : isIso f |- _ =>
  rewrite isIso_inv_unique in H;
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
| H : exists _ : Hom _ _, isIso _ |- _ => destruct H
| _ : isIso ?f |- _ => uniso' f
| |- isIso _ => unfold isIso
| |- exists _ : Hom _ _, _ => eexists
| |- _ /\ _ => split
| |- _ <-> _ => split
| _ => cat
end).

Lemma Dual_isomorphic :
  forall (C : Cat) (A B : Ob C),
    @isomorphic C A B <-> @isomorphic (Dual C) B A.
Proof. iso. Defined.

Lemma Dual_uniquely_isomorphic :
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
  unfold uniquely_isomorphic, isomorphic.
  now intros * (f & HIso & _); exists f.
Qed.

#[global] Hint Resolve Dual_isomorphic Dual_uniquely_isomorphic unique_iso_is_iso : core.

#[export]
Instance isomorphic_equiv (C : Cat) : Equivalence isomorphic.
Proof.
  split; do 2 red.
  - intros X. exists (id X). apply isIso_id.
  - intros X Y (f & g & eq1 & eq2). now exists g, f.
  - intros X Y Z [f f_iso] [g g_iso]. exists (f .> g). now apply isIso_comp.
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
  fmap_comp : forall {A B C : Ob C} (f : Hom A B) (g : Hom B C), fmap (f .> g) == fmap f .> fmap g;
  fmap_id : forall A : Ob C, fmap (id A) == id (fob A)
}.

Arguments fob  [C D] _ _.
Arguments fmap [C D] _ [A B] _.

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

Lemma isSec_fmap :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    isSec f -> isSec (fmap T f).
Proof.
  unfold isSec; intros * [g H].
  exists (fmap T g).
  now rewrite <- fmap_comp, H, fmap_id.
Defined.

Lemma isRet_fmap :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    isRet f -> isRet (fmap T f).
Proof.
  unfold isRet; intros * [g H].
  exists (fmap T g).
  now rewrite <- fmap_comp, H, fmap_id.
Defined.

#[global] Hint Resolve isSec_fmap isRet_fmap : core.

Lemma isIso_fmap :
  forall {C D : Cat} (T : Functor C D) {X Y : Ob C} (f : Hom X Y),
    isIso f -> isIso (fmap T f).
Proof. intros. rewrite isIso_iff_isSec_isRet in *. intuition. Defined.

Lemma full_faithful_refl_isSec :
  forall {C D : Cat} (T : Functor C D) {X Y : Ob C} (f : Hom X Y),
    full T -> faithful T -> isSec (fmap T f) -> isSec f.
Proof.
  unfold full, faithful, isSec; intros * T_full T_faithful [Tg Tg_sec].
  destruct (T_full Y X Tg) as [g Heq].
  exists g.
  now apply T_faithful; rewrite fmap_comp, fmap_id, Heq.
Defined.

Lemma full_faithful_refl_isRet :
  forall {C D : Cat} (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> isRet (fmap T f) -> isRet f.
Proof.
  unfold isRet, full, faithful; intros * T_full T_faithful [Tg Tg_ret].
  destruct (T_full Y X Tg) as [g Heq].
  exists g.
  now apply T_faithful; rewrite fmap_comp, fmap_id, Heq.
Defined.

#[global] Hint Resolve full_faithful_refl_isSec full_faithful_refl_isRet : core.

Lemma isSec_fmap_conv :
  forall {C D : Cat} (T : Functor C D) {X Y : Ob C} (f : Hom X Y),
    full T -> faithful T -> isSec (fmap T f) <-> isSec f.
Proof.
  split; intros.
  - now eapply full_faithful_refl_isSec.
  - now eapply isSec_fmap.
Qed.

Lemma isRet_fmap_conv :
  forall {C D : Cat} (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> isRet (fmap T f) <-> isRet f.
Proof.
  split; intros.
  - now eapply full_faithful_refl_isRet.
  - now eapply isRet_fmap.
Qed.

Lemma full_faithful_refl_isIso :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> isIso (fmap T f) -> isIso f.
Proof.
  intros * Hfu Hfa.
  now rewrite !isIso_iff_isSec_isRet, isSec_fmap_conv, isRet_fmap_conv.
Defined.

Lemma isIso_fmap_conv :
  forall (C D : Cat) (T : Functor C D) (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> isIso (fmap T f) <-> isIso f.
Proof.
  intros * Hfu Hfa.
  now rewrite !isIso_iff_isSec_isRet, isSec_fmap_conv, isRet_fmap_conv.
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
  - proper.
  - now intros; rewrite !fmap_comp.
  - now intros; rewrite !fmap_id.
Defined.

#[refine]
#[export]
Instance FunctorId (C : Cat) : Functor C C :=
{
  fob := fun A : Ob C => A;
  fmap := fun (X Y : Ob C) (f : Hom X Y) => f
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance ConstFunctor {D : Cat} (X : Ob D) (C : Cat) : Functor C D :=
{
  fob := fun _ => X;
  fmap := fun _ _ _ => id X
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance HomFunctor (C : Cat) (X : Ob C) : Functor C CoqSetoid :=
{
  fob := fun Y : Ob C => {| carrier := Hom X Y; setoid := HomSetoid X Y |}
}.
Proof.
  - intros A B f. exists (fun g => g .> f). proper.
  - proper.
  - now cbn; intros; rewrite comp_assoc.
  - now cbn; intros; rewrite comp_id_r.
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
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance HomContravariant (C : Cat) (X : Ob C) : Contravariant C CoqSetoid :=
{
  coob := fun Y : Ob C => {| carrier := Hom Y X; setoid := HomSetoid Y X |}
}.
Proof.
  - intros Y Z f. exists (fun g => f .> g). proper.
  - proper.
  - now cbn.
  - now cbn.
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
  bimap_comp :
    forall
      (X Y Z : Ob C) (X' Y' Z' : Ob D)
      (f : Hom X Y) (g : Hom Y Z) (f' : Hom X' Y') (g' : Hom Y' Z'),
        bimap (f .> g) (f' .> g') == bimap f f' .> bimap g g';
  bimap_id :
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
  - proper.
  - now intros; rewrite !fmap_comp, !bimap_comp.
  - now intros; rewrite 2 fmap_id, bimap_id.
Defined.

#[refine]
#[export]
Instance ConstBifunctor {E : Cat} (X : Ob E) (C D : Cat) : Bifunctor C D E :=
{
  biob := fun _ _ => X;
  bimap := fun _ _ _ _ _ _ => id X
}.
Proof.
  all: easy.
Defined.

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
| _ => cat; profunctor_simpl; cat
end.

#[refine]
#[export]
Instance ConstProfunctor {E : Cat} (X : Ob E) (C D : Cat) : Profunctor C D E :=
{
  diob := fun _ _ => X;
  dimap := fun _ _ _ _ _ _ => id X
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance ProComp
  {C C' D D' E : Cat} (P : Profunctor C' D' E) (F : Functor C C') (G : Functor D D')
  : Profunctor C D E :=
{
  diob := fun (X : Ob C) (Y : Ob D) => diob (fob F X) (fob G Y)
}.
Proof.
  - intros * f g. exact (dimap (fmap F f) (fmap G g)).
  - proper.
  - now cbn; intros; rewrite !fmap_comp, dimap_comp.
  - now cbn; intros; rewrite !fmap_id, dimap_id.
Defined.

#[refine]
#[export]
Instance HomProfunctor (C : Cat) : Profunctor C C CoqSetoid :=
{
  diob := fun X Y : Ob C => {| carrier := Hom X Y; setoid := HomSetoid X Y |};
}.
Proof.
  - intros * f g. exists (fun h : Hom Y X' => f .> h .> g). proper.
  - proper.
  - now cbn; intros; rewrite !comp_assoc.
  - now cbn; intros; rewrite comp_id_l, comp_id_r.
Defined.

(** * The category of categories and functors *)

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
  - now intros F; exists (fun _ => eq_refl); cbn.
  - intros F G [p q]. exists (fun A => eq_sym (p A)).
    intros A B f; rewrite <- q; clear q. now destruct (p A), (p B); cbn.
  - intros F G H [p1 q1] [p2 q2]. exists (fun X => eq_trans (p1 X) (p2 X)).
    intros A B f. rewrite <- q2, <- q1; clear q1 q2.
    now destruct (p2 B), (p1 B), (p2 A), (p1 A); cbn.
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
    + intros X. clear q s. now destruct (p X), (r (fob F X)).
    + intros X Y f. cbn.
      rewrite <- q, <- s; clear q s.
      now destruct (p X), (p Y), (r (fob F X)), (r (fob F Y)); cbn.
  - cbn; intros A B C D F G H.
    now exists (fun X => eq_refl).
  - now intros A B F; exists (fun _ => eq_refl).
  - now intros A B F; exists (fun _ => eq_refl).
Defined.

(** We also need to define the product of two categories, as this is needed
    in many places to define two-argument functors. *)

Definition ProdCatHom {C D : Cat} (X Y : Ob C * Ob D) : Type :=
  Hom (fst X) (fst Y) * Hom (snd X) (snd Y).

#[refine]
#[export]
Instance ProdCatSetoid {C D : Cat} (X Y : Ob C * Ob D) : Setoid (ProdCatHom X Y) :=
{
  equiv := fun f g : ProdCatHom X Y => fst f == fst g /\ snd f == snd g
}.
Proof.
  now split; red; intros; split; try destruct H; try destruct H0; rewrite ?H, ?H0, ?H1.
Defined.

#[refine]
#[export]
Instance CAT_product (C : Cat) (D : Cat) : Cat :=
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
  - proper. now destruct H as [-> ->], H0 as [-> ->].
  - now cbn; intros; rewrite !comp_assoc.
  - now cbn; intros; rewrite comp_id_l.
  - now cbn; intros; rewrite comp_id_r.
Defined.

(** * Natural transformations *)

Class NatTrans {C D : Cat} (T S : Functor C D) : Type :=
{
  component : forall X : Ob C, Hom (fob T X) (fob S X);
  natural :
    forall [X Y : Ob C] (f : Hom X Y),
      component X .> fmap S f == fmap T f .> component Y
}.

Arguments component [C D T S] _ _.
Arguments natural   [C D T S] _ [X Y] _.

#[refine]
#[export]
Instance NatTransSetoid {C D : Cat} (F G : Functor C D) : Setoid (NatTrans F G) :=
{
  equiv := fun alfa beta : NatTrans F G =>
    forall X : Ob C, component alfa X == component beta X
}.
Proof.
  now split; red; intros; rewrite ?H, ?H0.
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
  now intros X Y f; rewrite !comp_assoc, natural, <- comp_assoc, natural, comp_assoc.
Defined.

#[refine]
#[export]
Instance NatTransId {C D : Cat} (F : Functor C D) : NatTrans F F :=
{
  component := fun X : Ob C => id (fob F X)
}.
Proof.
  now intros; rewrite comp_id_l, comp_id_r.
Defined.

(** ** Natural isomorphisms and representable functors *)

Definition natural_isomorphism
  {C D : Cat} {F G : Functor C D} (α : NatTrans F G) : Prop :=
    exists β : NatTrans G F,
      NatTransComp α β == NatTransId F /\
      NatTransComp β α == NatTransId G.

Lemma natural_isomorphism_char :
  forall (C D : Cat) (F G : Functor C D) (α : NatTrans F G),
    natural_isomorphism α <-> forall X : Ob C, isIso (component α X).
Proof.
  unfold natural_isomorphism; split; cbn; intros.
  - destruct H as (β & Η1 & Η2). red. now exists (component β X).
  - red in H. destruct α as [component_α natural_α]; cbn in *.
    assert (component_β : {f : forall X : Ob C, Hom (fob G X) (fob F X) |
      (forall X : Ob C,
        component_α X .> f X == id (fob F X)
          /\
        f X .> component_α X == id (fob G X))
      /\
    (forall (X Y : Ob C) (g : Hom X Y), f X .> fmap F g == fmap G g .> f Y)}).
    {
      pose (H' := fun X : Ob C => constructive_indefinite_description _ (H X)).
      exists (fun X : Ob C => proj1_sig (H' X)). split.
      - intros. now split; destruct (H' X); cbn.
      - intros; destruct (H' X), (H' Y); cbn in *; clear H H'.
        destruct a as [a1 a2], a0 as [b1 b2].
        rewrite <- comp_id_l, <- comp_id_r, <- a2, <- b1.
        rewrite !comp_assoc, <- (comp_assoc (fmap F g) _).
        rewrite <- natural_α.
        rewrite <- (comp_assoc (component_α X)).
        rewrite a1, comp_id_l, <- !comp_assoc, a2, comp_id_l.
        easy.
    }
    destruct component_β as (component_β & inverse_α_β & natural_β).
    eexists {| component := component_β; natural := natural_β |}.
    cat; apply inverse_α_β.
Defined.

Definition representable {C : Cat} (F : Functor C CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor C X)), natural_isomorphism α.

Definition corepresentable {C : Cat} (F : Functor (Dual C) CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor (Dual C) X)), natural_isomorphism α.