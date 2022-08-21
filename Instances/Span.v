From Cat Require Import Cat.
From Cat.Limits Require Import Product Coproduct Pullback.

Set Implicit Arguments.

(** Category of spans *)

Class SpanHom (C : Cat) (hp : HasPullbacks C) (A B : Ob C) : Type :=
{
  center : Ob C;
  left : Hom center A;
  right : Hom center B;
}.

#[export]
Instance SpanHomSetoid (C : Cat) (hp : HasPullbacks C) (A B : Ob C) : Setoid (SpanHom hp A B).
Proof.
  esplit. Unshelve. 2:
  {
    red. intros [X f g] [Y f' g'].
    exact (exists p : X = Y,
      @transport _ (fun X => Hom X A) _ _ p f == f' /\
      @transport _ (fun X => Hom X B) _ _ p g == g').
  }
  split; red; destruct x; try destruct y; try destruct z.
    now exists eq_refl.
    intros [-> [H1 H2]]. now exists eq_refl.
    intros [-> [Hl1 Hr1]] [-> [Hl2 Hr2]]. exists eq_refl. cbn in *.
      now rewrite ?Hl1, ?Hr1.
Defined.

#[export]
Instance SpanId (C : Cat) (hp : HasPullbacks C) (A : Ob C) : SpanHom hp A A :=
{
  center := A;
  left := id A;
  right := id A;
}.

#[refine]
#[export]
Instance Span (C' : Cat) (hp : HasPullbacks C') : Cat :=
{
  Ob := Ob C';
  Hom := SpanHom hp;
  HomSetoid := SpanHomSetoid hp;
  id := SpanId hp;
}.
Proof.
Abort.