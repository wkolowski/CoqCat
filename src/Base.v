From Stdlib Require Export Setoid Classes.SetoidClass.
From Stdlib Require Export Bool Arith Lia.

From Stdlib Require Export List.
Export ListNotations.

#[global] Set Universe Polymorphism.

(** * Useful custom types *)

(** Sum-product hybrid. Useful for a few categories that behave like [Rel]. *)

Inductive sumprod (A B : Type) : Type :=
| inl'  : A -> sumprod A B
| inr'  : B -> sumprod A B
| pair' : A -> B -> sumprod A B.

Arguments inl'  {A B} _.
Arguments inr'  {A B} _.
Arguments pair' {A B} _ _.

#[global] Hint Constructors sumprod : core.

(** Non-empty lists *)

Inductive Nel (A : Type) : Type := Cons
{
  hd : A;
  tl : option (Nel A);
}.

Arguments hd {A} _.
Arguments tl {A} _.
Arguments Cons {A} _ _.

Fixpoint Nel_ind'
  (A : Type) (P : Nel A -> Prop)
  (hd' : forall h : A, P (Cons h None))
  (tl' : forall (h : A) (t : Nel A), P t -> P (Cons h (Some t)))
  (l : Nel A) {struct l} : P l :=
match l with
| {| hd := h; tl := None |}   => hd' h
| {| hd := h; tl := Some t |} => tl' h t (Nel_ind' A P hd' tl' t)
end.

Definition nsingl {A : Type} (x : A) : Nel A :=
{|
  hd := x;
  tl := None;
|}.

Fixpoint nmap {A B : Type} (f : A -> B) (l : Nel A) : Nel B :=
{|
  hd := f (hd l);
  tl := option_map (nmap f) (tl l);
|}.

Fixpoint napp {A : Type} (l1 l2 : Nel A) : Nel A :=
{|
  hd := hd l1;
  tl :=
    match tl l1 with
    | None => Some l2
    | Some t1 => Some (napp t1 l2)
    end;
|}.

Lemma napp_assoc :
  forall {A : Type} (l1 l2 l3 : Nel A),
    napp (napp l1 l2) l3 = napp l1 (napp l2 l3).
Proof.
  now induction l1 as [h | h t] using Nel_ind'; cbn; intros; rewrite ?IHt.
Qed.

Lemma nmap_napp :
  forall {A B : Type} (f : A -> B) (l1 l2 : Nel A),
    nmap f (napp l1 l2) = napp (nmap f l1) (nmap f l2).
Proof.
  now induction l1 as [h | h t] using Nel_ind'; cbn; intros; rewrite ?IHt.
Qed.

(** * Parametric translations *)

Definition relate_unit (u1 u2 : unit) : Prop := True.

Definition relate_Empty (e1 e2 : Empty_set) : Prop := True.

Definition relate_bool (b1 b2 : bool) : Prop :=
match b1, b2 with
| true , true  => True
| false, false => True
| _    , _     => False
end.

Inductive Relate_bool : bool -> bool -> Prop :=
| relate_false : Relate_bool false false
| relate_true  : Relate_bool true true.

Definition relate_option
  {A : Type} (R : A -> A -> Prop) (o1 o2 : option A) : Prop :=
match o1, o2 with
| None   , None    => True
| Some a1, Some a2 => R a1 a2
| _      , _       => False
end.

Inductive Relate_option
  {A : Type} (R : A -> A -> Prop) : option A -> option A -> Prop :=
| relate_None : Relate_option R None None
| relate_Some : forall {a1 a2 : A}, R a1 a2 -> Relate_option R (Some a1) (Some a2).

Arguments relate_None {A R}.
Arguments relate_Some {A R a1 a2} _.

Definition relate_prod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
    RA (fst p1) (fst p2) /\ RB (snd p1) (snd p2).

Definition relate_prod'
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
match p1, p2 with
| (a1, b1), (a2, b2) => RA a1 a2 /\ RB b1 b2
end.

Record Relate_prod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
{
  relate_fst : RA (fst p1) (fst p2);
  relate_snd : RB (snd p1) (snd p2);
}.

Arguments relate_fst {A B RA RB p1 p2} _.
Arguments relate_snd {A B RA RB p1 p2} _.

Definition relate_sum
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (s1 s2 : A + B) : Prop :=
match s1, s2 with
| inl a1, inl a2 => RA a1 a2
| inr b1, inr b2 => RB b1 b2
| _     , _      => False
end.

Inductive Relate_sum
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
| relate_inl : forall {a1 a2 : A}, RA a1 a2 -> Relate_sum RA RB (inl a1) (inl a2)
| relate_inr : forall {b1 b2 : B}, RB b1 b2 -> Relate_sum RA RB (inr b1) (inr b2).

Arguments relate_inl {A B RA RB a1 a2} _.
Arguments relate_inr {A B RA RB b1 b2} _.

Definition relate_fun
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f1 f2 : A -> B) : Prop :=
    forall a1 a2 : A, RA a1 a2 -> RB (f1 a1) (f2 a2).

Record Relate_sig
  {A : Type} {B : A -> Prop}
  (RA : A -> A -> Prop) (RB : forall {a1 a2 : A}, B a1 -> B a2 -> Prop)
  (p1 p2 : {a : A | B a}) : Prop :=
{
  relate_proj1_sig : RA (proj1_sig p1) (proj1_sig p2);
  relate_proj2_sig : RB (proj2_sig p1) (proj2_sig p2);
}.

Arguments relate_proj1_sig {A B RA RB p1 p2} _.
Arguments relate_proj2_sig {A B RA RB p1 p2} _.

Record Relate_sigT
  {A : Type} {B : A -> Type}
  (RA : A -> A -> Prop) (RB : forall {a1 a2 : A}, B a1 -> B a2 -> Prop)
  (p1 p2 : {a : A & B a}) : Prop :=
{
  relate_projT1 : RA (projT1 p1) (projT1 p2);
  relate_projT2 : RB (projT2 p1) (projT2 p2);
}.

Arguments relate_projT1 {A B RA RB p1 p2} _.
Arguments relate_projT2 {A B RA RB p1 p2} _.

Definition relate_forall
  {A : Type} {B : A -> Type}
  (RA : A -> A -> Prop) (RB : forall {a1 a2 : A}, B a1 -> B a2 -> Prop)
  (f1 f2 : forall a : A, B a) : Prop :=
    forall a1 a2 : A, RA a1 a2 -> RB (f1 a1) (f2 a2).

Definition relate_Prop (P1 P2 : Prop) : Prop := P1 <-> P2.

Definition relate_sumprod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (s1 s2 : sumprod A B) : Prop :=
match s1, s2 with
| inl' a1    , inl' a2     => RA a1 a2
| inr' a1    , inr' a2     => RB a1 a2
| pair' a1 b1, pair' a2 b2 => RA a1 a2 /\ RB b1 b2
| _          , _           => False
end.

Inductive Relate_sumprod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : sumprod A B -> sumprod A B -> Prop :=
| relate_inl'  :
  forall {a1 a2 : A}, RA a1 a2 -> Relate_sumprod RA RB (inl' a1) (inl' a2)
| relate_inr'  :
  forall {b1 b2 : B}, RB b1 b2 -> Relate_sumprod RA RB (inr' b1) (inr' b2)
| relate_pair' :
  forall {a1 a2 : A} {b1 b2 : B},
    RA a1 a2 -> RB b1 b2 -> Relate_sumprod RA RB (pair' a1 b1) (pair' a2 b2).

Arguments relate_inl'  {A B RA RB a1 a2} _.
Arguments relate_inr'  {A B RA RB b1 b2} _.
Arguments relate_pair' {A B RA RB a1 a2 b1 b2} _ _.

Fixpoint relate_list {A : Type} (R : A -> A -> Prop) (l1 l2 : list A) : Prop :=
match l1, l2 with
| []      , []       => True
| h1 :: t1, h2 :: t2 => R h1 h2 /\ relate_list R t1 t2
| _       , _        => False
end.

Fixpoint relate_Nel {A : Type} (RA : A -> A -> Prop) (l1 l2 : Nel A) : Prop :=
  RA (hd l1) (hd l2) /\
match tl l1, tl l2 with
| None, None => True
| Some t1, Some t2 => relate_Nel RA t1 t2
| _      , _       => False
end.

Inductive Relate_Nel {A : Type} (R : A -> A -> Prop) (l1 l2 : Nel A) : Prop :=
{
  relate_hd : R (hd l1) (hd l2);
  relate_tl : Relate_option (Relate_Nel R) (tl l1) (tl l2);
}.

Arguments relate_hd {A R l1 l2} _.
Arguments relate_tl {A R l1 l2} _.

(** * Equality *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

Lemma transport_transport :
  forall {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x),
    transport P q (transport P p u) = transport P (eq_trans p q) u.
Proof.
  now intros A P x y z [] [] u; cbn.
Defined.

Definition eq_unit_intro (x y : unit) : x = y :=
match x, y with
| tt, tt => eq_refl
end.

Definition eq_Empty_intro (x y : Empty_set) : x = y :=
  match x with end.

Definition eq_bool_intro {x y : bool} (E : Relate_bool x y) : x = y :=
match E with
| relate_false => eq_refl
| relate_true  => eq_refl
end.

Definition eq_option_intro
  {A : Type} {x y : option A} (E : Relate_option eq x y) : x = y :=
match E with
| relate_None => eq_refl
| relate_Some p => f_equal Some p
end.

Lemma eq_prod_intro :
  forall {A B : Type} (x y : A * B),
    fst x = fst y -> snd x = snd y -> x = y.
Proof.
  now intros A B [] []; cbn; intros [] [].
Defined.

Definition eq_sum_intro
  {A B : Type} {x y : A + B} (E : Relate_sum eq eq x y) : x = y :=
match E with
| relate_inl p => f_equal inl p
| relate_inr q => f_equal inr q
end.

Definition eq_sumprod_intro
  {A B : Type} {x y : sumprod A B} (p : Relate_sumprod eq eq x y) : x = y :=
match p with
| relate_inl'  p   => f_equal inl' p
| relate_inr'    q => f_equal inr' q
| relate_pair' p q => f_equal2 pair' p q
end.

Lemma eq_Nel_intro :
  forall {A : Type} {l1 l2 : Nel A},
    Relate_Nel eq l1 l2 -> l1 = l2.
Proof.
  fix IH 4.
  destruct 1, l1 as [h1 t1], l2 as [h2 t2]; cbn in *.
  apply f_equal2.
  - easy.
  - inversion relate_tl0.
    + easy.
    + now apply f_equal, IH.
Defined.

Lemma eq_Nel_intro' :
  forall {A : Type} {l1 l2 : Nel A},
    relate_Nel eq l1 l2 -> l1 = l2.
Proof.
  fix IH 2.
  destruct l1 as [h1 [t1 |]], l2 as [h2 [t2 |]];  intros [p E]; cbn in *.
  - apply f_equal2; [easy |].
    now apply f_equal, IH.
  - easy.
  - easy.
  - now apply f_equal2.
Defined.

(** * Setoids *)

(** Some useful setoid instances. *)

#[refine]
#[export]
Instance Setoid_unit : Setoid unit :=
{
  equiv := relate_unit;
}.
Proof. now split. Defined.

#[refine]
#[export]
Instance Setoid_Empty : Setoid Empty_set :=
{
  equiv := relate_Empty;
}.
Proof. now split. Defined.

#[export]
Instance Setoid_bool : Setoid bool :=
{
  equiv := fun b1 b2 => b1 = b2;
}.

#[export]
Instance Setoid_nat : Setoid nat :=
{
  equiv := fun n1 n2 => n1 = n2;
}.

#[refine]
#[export]
Instance Setoid_option {A : Type} (SA : Setoid A) : Setoid (option A) :=
{
  equiv := relate_option equiv;
}.
Proof.
  split; red.
  - now intros [a |]; cbn.
  - now intros [a1 |] [a2 |]; cbn.
  - intros [a1 |] [a2 |] [a3 |]; cbn; try easy.
    now intros -> ->.
Defined.

#[refine]
#[export]
Instance Setoid_prod {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (A * B) :=
{
  equiv := fun x y => fst x == fst y /\ snd x == snd y;
}.
Proof.
  split; red.
  - now intros [a b].
  - now intros [a1 b1] [a2 b2]; cbn; intros [-> ->].
  - now intros [a1 b1] [a2 b2] [a3 b3]; cbn; intros [-> ->] [-> ->].
Defined.

#[refine]
#[export]
Instance Setoid_sum {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (A + B) :=
{
  equiv := relate_sum equiv equiv;
}.
Proof.
  split; red.
  - now intros [a | b]; cbn.
  - now intros [a1 | b1] [a2 | b2]; cbn.
  - intros [a1 | b1] [a2 | b2] [a3 | b3]; cbn; try easy.
    + now intros -> ->.
    + now intros -> ->.
Defined.

#[refine]
#[export]
Instance Setoid_fun {A B : Type} (SB : Setoid B) : Setoid (A -> B) :=
{
  equiv := fun f g => forall a : A, f a == g a;
}.
Proof.
  split; red.
  - easy.
  - easy.
  - intros f g h H1 H2 a.
    now rewrite H1, H2.
Defined.

#[refine]
#[export]
Instance Setoid_sig
  {A : Type} (SA : Setoid A) {B : A -> Prop}
  : Setoid {a : A | B a} :=
{
  equiv := fun x y => proj1_sig x == proj1_sig y;
}.
Proof.
  split; red.
  - now intros [x x']; cbn.
  - now intros [x x'] [y y']; cbn.
  - now intros [x x'] [y y'] [z z']; cbn; intros -> ->.
Defined.

#[refine]
#[export]
Instance Setoid_sigT
  {A : Type} {B : A -> Type} (SB : forall x : A, Setoid (B x))
  : Setoid {a : A & B a} :=
{
  equiv := fun x y => {p : projT1 x = projT1 y & transport B p (projT2 x) == projT2 y};
}.
Proof.
  split; red.
  - now intros [x x']; exists eq_refl; cbn.
  - now intros [x x'] [y y']; cbn; intros [-> p]; exists eq_refl; cbn in *.
  - intros [x x'] [y y'] [z z']; cbn; intros [-> p] [-> q]; exists eq_refl; cbn in *.
    now rewrite p, q.
Defined.

#[refine]
#[export]
Instance Setoid_forall
  {A : Type} {B : A -> Type} (SB : forall x : A, Setoid (B x))
  : Setoid (forall x : A, B x) :=
{
  equiv := fun f g => forall x : A, f x == g x;
}.
Proof.
  split; red.
  - easy.
  - easy.
  - intros f g h H1 H2 a.
    now rewrite H1, H2.
Defined.

#[export]
Instance Setoid_Prop : Setoid Prop :=
{
  equiv := iff;
}.

#[refine]
#[export]
Instance Setoid_sumprod {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (sumprod A B) :=
{
  equiv := relate_sumprod equiv equiv;
}.
Proof.
  split; red.
  - now intros [a | b | a b]; cbn.
  - now intros [a1 | b1 | a1 b1] [a2 | b2 | a2 b2]; cbn.
  - intros [a1 | b1 | a1 b1] [a2 | b2 | a2 b2] [a3 | b3 | a3 b3]; cbn; try easy.
    + now intros -> ->.
    + now intros -> ->.
    + now intros [-> ->] [-> ->].
Defined.

#[refine]
#[export]
Instance Setoid_list {A : Type} (SA : Setoid A) : Setoid (list A) :=
{
  equiv := relate_list equiv;
}.
Proof.
  split; red.
  - now induction x; cbn.
  - induction x as [| h1 t1]; destruct y as [| h2 t2]; cbn; try easy.
    now intros [-> E]; split; [| apply IHt1].
  - induction x as [| h1 t1];
      destruct y as [| h2 t2], z as [| h3 t3]; cbn; try easy.
    intros [-> E1] [-> E2].
    now split; [| apply (IHt1 t2)].
Defined.

#[refine]
#[export]
Instance Setoid_Nel {A : Type} (SA : Setoid A) : Setoid (Nel A) :=
{
  equiv := relate_Nel equiv;
}.
Proof.
  split; red.
  - now induction x using Nel_ind'; cbn.
  - induction x as [h1 | h1 t1] using Nel_ind'; destruct y as [h2 [t2 |]]; cbn; try easy.
    now intros [-> E]; split; [| apply IHt1].
  - induction x as [h1 | h1 t1] using Nel_ind';
      destruct y as [h2 [t2 |]], z as [h3 [t3 |]]; cbn; try easy.
    + now intros [-> _] [-> _].
    + intros [-> E1] [-> E2].
      now split; [| apply (IHt1 t2)].
Defined.

(** Generic instances. *)

Definition Setoid_kernel {A B : Type} (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => f a1 = f a2).
  now split; red; [| | intros * -> ->].
Defined.

Definition Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => @equiv _ S (f a1) (f a2)).
  now split; red; [| | intros * -> ->].
Defined.

(** Uniqueness up to a custom equivalence relation, using setoids. *)

Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A) : Prop :=
  P x /\ (forall y : A, P y -> x == y).

Notation "'exists' !! x : A , P" :=
  (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).

#[global] Hint Unfold setoid_unique : core.

(** Kinds of ordinary functions. The suffix "S" at the end of some
    of these stands for "Setoid". *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Definition injectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
  forall a a' : A, f a == f a' -> a == a'.

Definition surjectiveS {A B : Type} {S : Setoid B} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a == b.

Definition bijectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
  injectiveS f /\ surjectiveS f.

#[global] Hint Unfold injective surjective bijective injectiveS surjectiveS bijectiveS : core.

(** Useful automation tactics. *)

Ltac proper :=
match goal with
| |- context [Proper] => unfold Proper, respectful; cbn; intros; proper
| H : ?a == ?b |- _ => rewrite H; clear H; proper
| |- ?a == ?a => reflexivity
| _ => auto
end.

Ltac my_simpl := cbn in *; repeat
match goal with
| H : False |- _ => inversion H
| e : Empty_set |- _ => inversion e
| x : True |- _ => clear x
| x : unit |- _ => destruct x
| |- context [@eq unit ?a ?b] => destruct a, b
| H : forall _ : unit, _ |- _ => specialize (H tt)
| H : forall _ : True, _ |- _ => specialize (H I)
| H : _ /\ _ |- _ => destruct H
| |- _ /\ _ => split
| |- _ <-> _ => split
| H : exists x, _ |- _ => destruct H
| H : exists! x, _ |- _ => destruct H
| H : exists!! x : _, _ |- _ => destruct H; unfold setoid_unique in *
| H : {_ | _} |- _ => destruct H
| H : {_ : _ | _} |- _ => destruct H
| H : {_ : _ & _} |- _ => destruct H
| H : context [setoid_unique] |- _ => red in H
| |- context [setoid_unique] => split
| H : _ = _ |- _ => subst
end.

Ltac solve_equiv := intros; repeat
match goal with
| |- context [Equivalence] => split; red; intros
| |- Reflexive _ => red; intros
| |- Symmetric _ => red; intros
| |- Transitive _ => red; intros
    (* Dealing with equality *)
| |-  ?a = ?a => reflexivity
| H : ?a = ?b |- ?b = ?a => symmetry; assumption
| H : ?a = ?b, H' : ?b = ?c |- ?a = ?c => rewrite H, H'; reflexivity
    (* Quantified equality *)
| H : forall _, ?a _ = ?b _ |- ?b _ = ?a _ => rewrite H; reflexivity
| H : forall _, ?a _ = ?b _, H' : forall _, ?b _ = ?c _
  |- ?a _ = ?c _ => rewrite H, H'; reflexivity
    (* Dealing with setoid equivalence *)
| |-  ?a == ?a => reflexivity
| H : ?a == ?b |- ?b == ?a => symmetry; assumption
| H : ?a == ?b, H' : ?b == ?c |- ?a == ?c => rewrite H, H'; reflexivity
    (* Quantified setoid equivalence *)
| H : forall _, ?a _ == ?b _ |- ?b _ == ?a _ => rewrite H; reflexivity
| H : forall _, ?a _ == ?b _, H' : forall _, ?b _ == ?c _
  |- ?a _ == ?c _ => rewrite H, H'; reflexivity
| _ => my_simpl; eauto
end.
