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

(** Non-empty lists *)

Inductive nel (A : Type) : Type :=
| singl    : A -> nel A
| cons_nel : A -> nel A -> nel A.

Arguments singl    {A} _.
Arguments cons_nel {A} _ _.

Notation "h ::: t" := (cons_nel h t) (right associativity, at level 30).

Fixpoint nel_app {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
| singl a => cons_nel a l2
| a ::: l1' => cons_nel a (nel_app l1' l2)
end.

Lemma nel_app_assoc :
  forall (A : Type) (x y z : nel A),
    nel_app x (nel_app y z) = nel_app (nel_app x y) z.
Proof.
  now induction x as [h | h t]; cbn; intros; rewrite ?IHt.
Qed.

Fixpoint nel_map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
| singl x => singl (f x)
| h ::: t => f h ::: nel_map f t
end.

Fixpoint nel2list {A : Type} (l : nel A) : list A :=
match l with
| singl h => [h]
| h ::: t => h :: nel2list t
end.

Lemma nel2list_app :
  forall {A : Type} (l1 l2 : nel A),
    nel2list (nel_app l1 l2) = nel2list l1 ++ nel2list l2.
Proof.
  now induction l1 as [h | h t]; cbn; intros; rewrite ?IHt.
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

Inductive eq_nel {A : Type} : nel A -> nel A -> Prop :=
| eq_singl :
  forall {a1 a2 : A}, a1 = a2 -> eq_nel (singl a1) (singl a2)
| eq_cons_nel :
  forall {a1 a2 : A} {t1 t2 : nel A},
    a1 = a2 -> eq_nel t1 t2 -> eq_nel (a1 ::: t1) (a2 ::: t2).

Fixpoint eq_nel_intro {A : Type} {l1 l2 : nel A} (E : eq_nel l1 l2) : l1 = l2 :=
match E with
| eq_singl p => f_equal singl p
| eq_cons_nel p E' => f_equal2 cons_nel p (eq_nel_intro E')
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

Fixpoint equiv_nel {X : Type} `{Setoid X} (l1 l2 : nel X) : Prop :=
match l1, l2 with
| singl h, singl h' => h == h'
| h ::: t, h' ::: t' => h == h' /\ equiv_nel t t'
| _, _ => False
end.

Lemma equiv_nel_refl :
  forall {X : Type} `{Setoid X} (l : nel X),
    equiv_nel l l.
Proof.
  now induction l as [| h t]; cbn; rewrite ?IHt.
Qed.

Lemma equiv_nel_sym :
  forall {X : Type} `{Setoid X} (l1 l2 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l1.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; [easy.. |].
  now intros [-> H']; split; [| apply IHt1].
Qed.

Lemma equiv_nel_trans :
  forall {X : Type} `{Setoid X} (l1 l2 l3 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l3 -> equiv_nel l1 l3.
Proof.
  induction l1 as [| h1 t1]; destruct l2, l3; cbn; try easy.
  - now intros -> ->.
  - now intros [-> H12] [-> H23]; split; [| apply (IHt1 l2)].
Qed.

#[global] Hint Resolve equiv_nel_refl equiv_nel_sym equiv_nel_trans : core.

#[refine]
#[export]
Instance Setoid_nel {A : Type} (SA : Setoid A) : Setoid (nel A) :=
{
  equiv := equiv_nel;
}.
Proof.
  split; red.
  - now apply equiv_nel_refl.
  - now apply equiv_nel_sym.
  - now apply equiv_nel_trans.
Defined.

(** Old trash *)

(*
Fixpoint fp_equiv {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 : nel (X + Y)) : Prop :=
match l1, l2 with
| singl (inl x), singl (inl x') => x == x'
| singl (inr y), singl (inr y') => y == y'
| cons_nel (inl h1) t1, cons_nel (inl h2) t2 => h1 == h2 /\ fp_equiv t1 t2
| cons_nel (inr h1) t1, cons_nel (inr h2) t2 => h1 == h2 /\ fp_equiv t1 t2
| _, _ => False
end.

Ltac fp_equiv := intros; repeat
match goal with
| x : _ + _ |- _ => destruct x; cbn in *
| H : _ /\ _ |- _ => destruct H
| |- _ /\ _ => split
| |- ?x == ?x => reflexivity
| H : ?P |- ?P => assumption
| H : ?x == ?y |- ?y == ?x => symmetry; assumption
| |- _ == _ => solve_equiv
| H : False |- _ => inversion H
| _ => eauto
end.

Lemma fp_equiv_refl :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l : nel (X + Y)),
    fp_equiv l l.
Proof.
  now induction l as [| h t]; fp_equiv.
Qed.

Lemma fp_equiv_sym :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l1.
Proof.
  now induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; fp_equiv.
Qed.

Lemma fp_equiv_trans :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 l3 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l3 -> fp_equiv l1 l3.
Proof.
  now induction l1 as [| h1 t1]; destruct l2, l3; fp_equiv.
Qed.

#[global] Hint Resolve fp_equiv_refl fp_equiv_sym fp_equiv_trans : core.
*)