Require Import Cat.

Set Implicit Arguments.

Definition equalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall {E' : Ob C} {e' : Hom E' X},
    e' .> f == e' .> g -> Hom E' E) : Prop :=
      e .> f == e .> g /\
      forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
        setoid_unique (fun u : Hom E' E => u .> e == e') (factorize H).

Definition coequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall {Q' : Ob C} {q' : Hom Y Q'},
    f .> q' == g .> q' -> Hom Q Q') : Prop :=
      f .> q == g .> q /\
      forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
        setoid_unique (fun u : Hom Q Q' => q .> u == q') (cofactorize H).

Definition biequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X) (q : Hom Y E)
  (factorize : forall (E' : Ob C) (e' : Hom E' X),
    e' .> f == e' .> g -> Hom E' E)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom E Q') : Prop :=
      equalizer C f g E e factorize /\
      coequalizer C f g E q cofactorize.

(* TODO : write JMequiv_dep *)

#[refine]
Instance SetoidFunExt_setoid (A B : Type) (A' : Setoid A) (B' : Setoid B)
    : Setoid (A -> B) :=
{
    equiv := fun f g : A -> B => forall x : A, f x == g x
}.
Proof. solve_equiv. Defined.

(* TODO : Instance SetoidFunExt (A B : Setoid') : Setoid' :=
{
    carrier := A -> B;
    setoid := @SetoidFunExt_setoid A B _ _
}.

Inductive JMequiv_ext : forall (A B : Setoid'), A -> B -> Prop :=
    | JMequiv_step : forall (A B : Setoid') (x y : A),
        x == y -> JMequiv_ext A A x y
    | JMequiv_ext' : forall (A B : Setoid') (f g : A -> B),
        (forall x : A, f x == g x) ->
        JMequiv_ext (SetoidFunExt A B) (SetoidFunExt A B) f g.

Arguments JMequiv_ext [A B] _ _.
Arguments JMequiv_step [A B] _ _ _.
Arguments JMequiv_ext' [A B] _ _ _.

Theorem JMequiv_ext_Setoid' :
  forall (A B : Setoid') (x : A) (y : B),
    JMequiv_ext x y -> A = B.
Proof.
  destruct 1; trivial.
Qed.*)

(* TODO *) Definition eq_ob_Proper_T (C : Cat) (X Y : Ob C) (f f' g g' : Hom X Y)
  : f == f' -> g == g' -> Prop.
Proof.
Abort.

Class has_equalizers (C : Cat) : Type :=
{
    eq_ob : forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
    eq_ob_Proper :
      forall (X Y : Ob C) (f f' g g' : Hom X Y),
        f == f' -> g == g' -> JMequiv (id (eq_ob f g)) (id (eq_ob f' g'));
    eq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
    eq_mor_Proper :
      forall (X Y : Ob C) (f f' g g' : Hom X Y),
        f == f' -> g == g' -> (*eq_ob f g = eq_ob f' g' ->*)
          JMequiv (eq_mor f g) (eq_mor f' g');
    factorize :
      forall {X Y : Ob C} (f g : Hom X Y) (E' : Ob C) (e' : Hom E' X),
        e' .> f == e' .> g -> Hom E' (eq_ob f g);
    (* TODO : factorize_Proper : forall (X Y E' : Ob C) (f f' g g' : Hom X Y)
      (e' : Hom E' X) (H : e' .> f == e' .> g) (H' : e' .> f' == e' .> g'),
      f == f' -> g == g' ->
      JMequiv (factorize f g E' e' H) (factorize f' g' E' e' H'); *)
    is_equalizer : forall (X Y : Ob C) (f g : Hom X Y),
      equalizer C f g (eq_ob f g) (eq_mor f g) (factorize f g)
}.

Class has_coequalizers (C : Cat) : Type :=
{
    coeq_ob : forall {X Y : Ob C} (f g : Hom X Y), Ob C;
    coeq_ob_Proper : forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (coeq_ob f g)) (id (coeq_ob f' g'));
    coeq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coeq_ob f g);
    coeq_mor_Proper : forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (coeq_mor f g) (coeq_mor f' g');
    cofactorize : forall {X Y : Ob C} (f g : Hom X Y)
      (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom (coeq_ob f g) Q';
    (* TODO : cofactorize_Proper : forall (X Y Q' : Ob C) (f f' g g' : Hom X Y)
      (q' : Hom Y Q') (H : f .> q' == g .> q') (H' : f' .> q' == g' .> q'),
      f == f' -> g == g' ->
      JMequiv (cofactorize f g Q' q' H) (cofactorize f' g' Q' q' H'); *)
    is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
      coequalizer C f g (coeq_ob f g) (coeq_mor f g) (cofactorize f g)
}.

Class has_biequalizers (C : Cat) : Type :=
{
    bi_has_equalizers :> has_equalizers C;
    bi_has_coequalizers :> has_coequalizers C;
    equalizer_is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
      eq_ob f g = coeq_ob f g
}.

Coercion bi_has_equalizers : has_biequalizers >-> has_equalizers.
Coercion bi_has_coequalizers : has_biequalizers >-> has_coequalizers.

Theorem dual_equalizer_coequalizer :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X),
      e' .> f == e' .> g -> Hom E' E),
      @equalizer C X Y f g E e factorize <->
      @coequalizer (Dual C) Y X f g E e factorize.
Proof. cat. Qed.

Theorem dual_biqualizer_self :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e : Hom E X) (q : Hom Y E)
    (factorize : forall (E' : Ob C) (e' : Hom E' X),
      e' .> f == e' .> g -> Hom E' E)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom E Q'),
    @biequalizer C X Y f g E e q factorize cofactorize <->
    @biequalizer (Dual C) Y X f g E q e cofactorize factorize.
Proof.
  unfold biequalizer. do 2 split; destruct H; assumption.
Qed.

Theorem equalizer_uiso :
  forall {C : Cat} {X Y : Ob C} {f g : Hom X Y}
    {E E' : Ob C} {e : Hom E X} {e' : Hom E' X}
    {factorize : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .> g -> Hom E'' E}
    {factorize' : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .> g -> Hom E'' E'},
      equalizer C f g E e factorize ->
      equalizer C f g E' e' factorize' ->
      exists !! f : Hom E E', Iso f /\
        e == f .> e'.
Proof.
  unfold equalizer; intros. destruct H, H0.
  destruct
    (H1 E e H) as [eq1 unique1],
    (H1 E' e' H0) as [eq1' unique1'],
    (H2 E' e' H0) as [eq2 unique2],
    (H2 E e H) as [eq2' unique2'].
  exists (factorize' E e H).
  repeat split.
    red. exists (factorize0 E' e' H0). split.
      assert (Heq : (factorize' E e H .> e') .> f ==
        (factorize' E e H .> e') .> g).
        rewrite eq2'. trivial.
        destruct (H1 E (factorize' E e H .> e') Heq).
          rewrite <- (unique1 (factorize' E e H .> factorize0 E' e' H0)).
            auto.
            assocr. rewrite eq1'. auto.
          rewrite <- (unique2 (factorize0 E' e' H0 .> factorize' E e H)).
            auto.
            assocr. rewrite eq2'. auto.
    rewrite eq2'. reflexivity.
    intros. destruct H3. apply unique2'. rewrite H4. reflexivity.
Qed.

Theorem equalizer_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E E' : Ob C) (e : Hom E X) (e' : Hom E' X)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .> g -> Hom E'' E)
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .>g -> Hom E'' E'),
      equalizer C f g E e factorize ->
      equalizer C f g E' e' factorize' ->
      E ~ E'.
Proof.
  intros. destruct (equalizer_uiso H H0).
  do 2 destruct H1. eauto.
Qed.

Theorem equalizer_equiv :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e1 : Hom E X) (e2 : Hom E X)
  (factorize : forall (E' : Ob C) (e : Hom E' X),
    e .> f == e .> g -> Hom E' E),
      equalizer C f g E e1 factorize ->
      equalizer C f g E e2 factorize ->
        e1 == e2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (factorize0 E e2 H3 == id E).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Theorem equalizer_equiv_factorize :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall (E' : Ob C) (e' : Hom E' X),
    e' .> f == e' .> g -> Hom E' E)
  (factorize' : forall (E' : Ob C) (e' : Hom E' X),
    e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize ->
      equalizer C f g E e factorize' ->
        forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
         factorize E' e' H == factorize' E' e' H.
Proof.
  intros.
  edestruct H, H3. apply H5.
  edestruct H0, H7. apply H8.
Qed.

Theorem coequalizer_uiso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
  (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''),
    f .> q'' == g .> q'' -> Hom Q Q'')
  (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''),
    f .> q'' == g .> q'' -> Hom Q' Q''),
      coequalizer C f g Q q cofactorize ->
      coequalizer C f g Q' q' cofactorize' ->
        exists !! f : Hom Q' Q, Iso f /\
          q' .> f == q.
Proof.
  intro. rewrite <- (dual_involution_axiom C). intros. simpl in *.
  rewrite <- dual_equalizer_coequalizer in H.
  rewrite <- dual_equalizer_coequalizer in H0.
  destruct (equalizer_uiso H H0).
  exists x. repeat split.
    rewrite <- dual_iso_self. cat.
    cat. rewrite H3. reflexivity.
    intros. cat. apply H4. cat.
      rewrite dual_iso_self. assumption.
      rewrite H3. reflexivity.
Time Qed.

Theorem coequalizer_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
  (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''),
    f .> q'' == g .> q'' -> Hom Q Q'')
  (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''),
    f .> q'' == g .> q'' -> Hom Q' Q''),
      coequalizer C f g Q q cofactorize ->
      coequalizer C f g Q' q' cofactorize' ->
        Q ~ Q'.
Proof.
  intros. destruct (coequalizer_uiso H H0).
  do 2 destruct H1. iso.
Qed.

Theorem coequalizer_equiv :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q1 : Hom Y Q) (q2 : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q1 cofactorize ->
      coequalizer C f g Q q2 cofactorize ->
        q1 == q2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (cofactorize0 Q q2 H3 == id Q).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Theorem coequalizer_equiv_factorize :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom Q Q')
  (cofactorize' : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize ->
      coequalizer C f g Q q cofactorize' ->
        forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
          cofactorize Q' q' H == cofactorize' Q' q' H.
Proof.
  intros.
  edestruct H, H3; apply H5.
  edestruct H0, H7; apply H8.
Qed.

(* TODO : finish *) Theorem biequalizer_uiso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) (q : Hom Y E)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .> g -> Hom E'' E)
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''),
      f .> q'' == g .> q'' -> Hom E Q'')
    (E' : Ob C) (e' : Hom E' X) (q' : Hom Y E')
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X),
      e'' .> f == e'' .> g -> Hom E'' E')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''),
      f .> q'' == g .> q'' -> Hom E' Q''),
      biequalizer C f g E e q factorize cofactorize ->
      biequalizer C f g E' e' q' factorize' cofactorize' ->
      exists !! f : Hom E E', Iso f /\
        e == f .> e' /\ q .> f == q'.
Proof.
  unfold biequalizer; intros.
  destruct H as [[HE_eq HE_uq] [HC_eq HC_uq]],
    H0 as [[HE'_eq HE'_uq] [HC'_eq HC'_uq]].
  destruct (HE_uq E' e' HE'_eq) as [eq unique].
  destruct (HE'_uq E e HE_eq) as [eq' unique'].
  exists (factorize' E e HE_eq).
  repeat split.
    red. exists (factorize0 E' e' HE'_eq). split. (*
      destruct (HE_uq E (factorize' E e HE_eq .> e')). rewrite eq'. auto.
        rewrite <- (H0 (factorize' E e .> factorize0 E' e')).
        apply H0. rewrite eq'. cat.
        rewrite comp_assoc, eq. reflexivity.
      destruct (HE'_uq E' (factorize0 E' e' .> e)). rewrite eq. auto.
        rewrite <- (H0 (factorize0 E' e' .> factorize' E e)).
        apply H0. rewrite eq. cat.
        rewrite comp_assoc, eq'. reflexivity.
    rewrite eq'. reflexivity.
    Focus 2.
    intros. destruct H as [_ [H1 _]]. apply unique'. symmetry. auto.
    destruct (HC_uq E' q' HC'_eq).
    destruct (HC'_uq E q HC_eq).
    assert (factorize' E e .> e' .> g .> q'
      == e .> f .> q .> cofactorize0 E' q').
      rewrite eq'. rewrite HE_eq.
      assocr'. rewrite H. reflexivity. rewrite unique'. eauto.
        rewrite H0. eauto.
    assert (factorize' E e == cofactorize0 E' q').
      apply unique'. *)
Abort.

Theorem equalizer_is_mono :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall (E' : Ob C) (e' : Hom E' X),
    e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize -> Mon e.
Proof.
  unfold equalizer, setoid_unique, Mon. intros.
  rename X0 into Z. rename g0 into h'.
  destruct H as [eq H].
  assert ((h .> e) .> f == (h .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  assert ((h' .> e) .> f == (h' .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  destruct (H Z (h .> e) H1) as [u Hh].
  edestruct (H Z (h' .> e) H2) as [u' Hh'].
  assert (factorize0 Z (h .> e) H1 == factorize0 Z (h' .> e) H2).
    rewrite Hh, Hh'. reflexivity. reflexivity. assumption.
  specialize (Hh h); specialize (Hh' h').
  rewrite <- Hh, <- Hh'; try rewrite H3; reflexivity.
Defined.

Theorem equalizer_epi_is_iso
  : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X),
      e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize -> Epi e -> Iso e.
Proof.
  intros. assert (HMon : Mon e).
    eapply equalizer_is_mono; eauto.
    unfold Epi, Mon in *. destruct H.
    red. pose (Heq := H0 _ _ _ H). assert (id X .> f == id X .> g).
      cat.
      exists (factorize0 _ (id X) H2). split.
        edestruct H1. assert (e .> factorize0 X (id X) H2 .> e == id E .> e).
          assocr. rewrite H3. cat.
          rewrite (HMon _ _ _ H5). reflexivity.
        edestruct H1. apply H3.
Qed.

Theorem coequalizer_is_epi :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize -> Epi q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_mon_epi.
  rewrite <- dual_equalizer_coequalizer in *.
  eapply equalizer_is_mono. eauto.
Qed.

Theorem coequalizer_mono_is_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'),
    f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize -> Mon q -> Iso q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite dual_mon_epi in H0.
  rewrite <- dual_iso_self.
  apply (@equalizer_epi_is_iso (Dual C) Y X f g _ _ cofactorize0).
    rewrite dual_equalizer_coequalizer. exact H.
    exact H0.
Qed.

(*
Print factorize.
Print is_equalizer.
Print has_equalizers.
*)

Theorem factorize_eq_mor :
  forall
    (C : Cat) (he : has_equalizers C)
    (X Y : Ob C) (f g : Hom X Y),
      factorize f g _ (eq_mor f g) (proj1 (is_equalizer X Y f g)) ==
      id (eq_ob f g).
Proof.
  intros. destruct he; simpl in *.
  edestruct is_equalizer0, s. cat.
Defined.

Check @factorize.

(*
TODO Theorem factorize_comp :
  forall
    (C : Cat) (he : has_equalizers C)
    (X Y A : Ob C) (f g : Hom X Y)
    (h1 : Hom (eq_ob f g) A) (h2 : Hom A X)
    (H : h1 .> h2 .> f == h1 .> h2 .> g),
      factorize f g _ (h1 .> h2) H ==
(*      id (eq_ob f g).*)
Proof.
  intros. destruct he; simpl in *.
  destruct (is_equalizer0 _ _ f g).
  edestruct is_equalizer0, H1. rewrite H3. reflexivity. reflexivity. cat. apply H3. s. cat.
Defined.
*)

Theorem cofactorize_eq_mor :
  forall (C : Cat) (he : has_coequalizers C) (X Y : Ob C) (f g : Hom X Y),
    cofactorize f g _ (coeq_mor f g) (proj1 (is_coequalizer X Y f g)) ==
    id (coeq_ob f g).
Proof.
  intros. destruct he; simpl in *.
  edestruct is_coequalizer0, s. cat.
Defined.

#[refine]
Instance Dual_has_coequalizers (C : Cat) (he : has_equalizers C)
    : has_coequalizers (Dual C) :=
{
    coeq_ob := fun X Y : Ob (Dual C) => @eq_ob C he Y X;
    coeq_mor := fun X Y : Ob (Dual C) => @eq_mor C he Y X;
    cofactorize := fun X Y : Ob (Dual C) => @factorize C he Y X;
    (*cofactorize_Proper := fun X Y : Ob (Dual C) =>
      @factorize_Proper C he Y X;*)
    is_coequalizer := fun X Y : Ob (Dual C) => @is_equalizer C he Y X
}.
Proof.
  all: simpl; intros.
    destruct (eq_ob_Proper Y X f f' g g' H H0). auto.
    destruct (eq_mor_Proper Y X f f' g g' H H0). auto.
Defined.

#[refine]
Instance Dual_has_equalizers (C : Cat) (he : has_coequalizers C)
    : has_equalizers (Dual C) :=
{
    eq_ob := fun X Y : Ob (Dual C) => @coeq_ob C he Y X;
    eq_mor := fun X Y : Ob (Dual C) => @coeq_mor C he Y X;
    factorize := fun X Y : Ob (Dual C) => @cofactorize C he Y X;
    (*factorize_Proper := fun X Y : Ob (Dual C) =>
      @cofactorize_Proper C he Y X;*)
    is_equalizer := fun X Y : Ob (Dual C) => @is_coequalizer C he Y X
}.
Proof.
  all: simpl; intros.
    destruct (coeq_ob_Proper Y X f f' g g' H H0). auto.
    destruct (coeq_mor_Proper Y X f f' g g' H H0). auto.
Defined.

#[refine]
Instance Dual_has_biequalizers (C : Cat) (he : has_biequalizers C)
    : has_biequalizers (Dual C) :=
{
    bi_has_equalizers := Dual_has_equalizers he;
    bi_has_coequalizers := Dual_has_coequalizers he;
}.
Proof.
  simpl. intros. rewrite equalizer_is_coequalizer. trivial.
Defined.