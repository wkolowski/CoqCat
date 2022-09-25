Require Export Setoid Classes.SetoidClass.
Require Export Bool Arith Lia.

Require Export List.
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

(** Better non-empty lists *)

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

Definition unit_eq_intro (x y : unit) : x = y :=
match x, y with
| tt, tt => eq_refl
end.

Definition Empty_eq_intro (x y : Empty_set) : x = y :=
  match x with end.

Inductive eq_bool : bool -> bool -> Prop :=
| eq_bool_false : eq_bool false false
| eq_bool_true  : eq_bool true true.

Definition eq_bool_intro {x y : bool} (E : eq_bool x y) : x = y :=
match E with
| eq_bool_false => eq_refl
| eq_bool_true  => eq_refl
end.

Lemma prod_eq_intro :
  forall {A B : Type} (x y : A * B),
    fst x = fst y -> snd x = snd y -> x = y.
Proof.
  now intros A B [] []; cbn; intros [] [].
Defined.

Inductive eq_sum {A B : Type} : A + B -> A + B -> Prop :=
| eq_sum_inl : forall {a1 a2 : A}, a1 = a2 -> eq_sum (inl a1) (inl a2)
| eq_sum_inr : forall {b1 b2 : B}, b1 = b2 -> eq_sum (inr b1) (inr b2).

Definition eq_sum_intro
  {A B : Type} {x y : A + B} (E : eq_sum x y) : x = y :=
match E with
| eq_sum_inl p => f_equal inl p
| eq_sum_inr q => f_equal inr q
end.

Inductive eq_option {A : Type} : option A -> option A -> Prop :=
| eq_option_None : eq_option None None
| eq_option_Some : forall a1 a2 : A, a1 = a2 -> eq_option (Some a1) (Some a2).

Definition eq_option_intro
  {A : Type} {x y : option A} (E : eq_option x y) : x = y :=
match E with
| eq_option_None => eq_refl
| eq_option_Some a1 a2 p => f_equal Some p
end.

Inductive eq_sumprod {A B : Type} : sumprod A B -> sumprod A B -> Prop :=
| eq_sumprod_inl'  :
  forall {a1 a2 : A}, a1 = a2 -> eq_sumprod (inl' a1) (inl' a2)
| eq_sumprod_inr'  :
  forall {b1 b2 : B}, b1 = b2 -> eq_sumprod (inr' b1) (inr' b2)
| eq_sumprod_pair' :
  forall {a1 a2 : A} {b1 b2 : B}, a1 = a2 -> b1 = b2 -> eq_sumprod (pair' a1 b1) (pair' a2 b2).

Definition eq_sumprod_intro
  {A B : Type} {x y : sumprod A B} (p : eq_sumprod x y) : x = y :=
match p with
| eq_sumprod_inl'  p   => f_equal inl' p
| eq_sumprod_inr'    q => f_equal inr' q
| eq_sumprod_pair' p q => f_equal2 pair' p q
end.

(** * Setoids *)

(** Uniqueness up to a custom equivalence relation, using setoids. *)

Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A) : Prop :=
  P x /\ (forall y : A, P y -> x == y).

Set Warnings "-deprecated-ident-entry".
Notation "'exists' !! x : A , P" :=
  (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).
Set Warnings "+deprecated-ident-entry".

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

Definition surjectiveS'
  {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
    exists g : B -> A,
      Proper (equiv ==> equiv) g /\ forall b : B, f (g b) == b.

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

(** Generic instances. *)

Definition Setoid_kernel {A B : Type} (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => f a1 = f a2).
  now solve_equiv.
Defined.

Definition Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => @equiv _ S (f a1) (f a2)).
  now solve_equiv.
Defined.

(** Some useful setoid instances. *)

#[export]
Instance Setoid_Prop : Setoid Prop :=
{
  equiv := iff;
}.

#[refine]
#[export]
Instance Setoid_unit : Setoid unit :=
{
  equiv := fun _ _ => True;
}.
Proof. now solve_equiv. Defined.

#[refine]
#[export]
Instance Setoid_Empty : Setoid Empty_set :=
{
  equiv := fun _ _ => True;
}.
Proof. now solve_equiv. Defined.

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
Instance Setoid_prod {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (A * B) :=
{
  equiv := fun x y => fst x == fst y /\ snd x == snd y;
}.
Proof.
  split; red.
  - now intros [a b].
  - now intros [a1 b1] [a2 b2] [-> ->].
  - now intros [a1 b1] [a2 b2] [a3 b3] [-> ->] [-> ->].
Defined.

#[refine]
#[export]
Instance Setoid_sum {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (A + B) :=
{
  equiv := fun x y =>
    match x, y with
    | inl a1, inl a2 => a1 == a2
    | inr b1, inr b2 => b1 == b2
    | _     , _      => False
    end;
}.
Proof.
  split; red.
  - now intros [a | b].
  - now intros [a1 | b1] [a2 | b2].
  - intros [a1 | b1] [a2 | b2] [a3 | b3]; try easy.
    + now intros -> ->.
    + now intros -> ->.
Defined.

#[refine]
#[export]
Instance Setoid_option {A : Type} (SA : Setoid A) : Setoid (option A) :=
{
  equiv := fun x y =>
    match x, y with
    | None   , None    => True
    | Some a1, Some a2 => a1 == a2
    | _      , _       => False
    end;
}.
Proof.
  split; red.
  - now intros [a |].
  - now intros [a1 |] [a2 |].
  - intros [a1 |] [a2 |] [a3 |]; try easy.
    now intros -> ->.
Defined.

#[refine]
#[export]
Instance Setoid_sumprod {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (sumprod A B) :=
{
  equiv := fun x y =>
    match x, y with
    | inl' a1    , inl' a2     => a1 == a2
    | inr' b1    , inr' b2     => b1 == b2
    | pair' a1 b1, pair' a2 b2 => a1 == a2 /\ b1 == b2
    | _          , _           => False
    end;
}.
Proof.
  split; red.
  - now intros [a | b | a b].
  - now intros [a1 | b1 | a1 b1] [a2 | b2 | a2 b2].
  - intros [a1 | b1 | a1 b1] [a2 | b2 | a2 b2] [a3 | b3 | a3 b3]; try easy.
    + now intros -> ->.
    + now intros -> ->.
    + now intros [-> ->] [-> ->].
Defined.

#[refine]
#[export]
Instance Setoid_fun {A B : Type} (SA : Setoid A) (SB : Setoid B) : Setoid (A -> B) :=
{
  equiv := fun f g => forall a : A, f a == g a;
}.
Proof. now solve_equiv. Defined.

#[refine]
#[export]
Instance Setoid_forall
  {A : Type} {B : A -> Type} (SB : forall x : A, Setoid (B x))
  : Setoid (forall x : A, B x) :=
{
  equiv := fun f g => forall x : A, f x == g x;
}.
Proof. now solve_equiv. Defined.

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

(* TODO: Setoid_Nel *)