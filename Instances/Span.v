From Cat Require Import Cat.
From Cat.Universal Require Import Product Coproduct Pullback.

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
  unshelve esplit.
  - intros [X f g] [Y f' g'].
    exact (exists p : X = Y,
      @transport _ (fun X => Hom X A) _ _ p f == f' /\
      @transport _ (fun X => Hom X B) _ _ p g == g').
  - split; red.
    + now intros [x x1 x2]; exists eq_refl.
    + now intros [x x1 x2] [y y1 y2] (-> & p1 & p2); cbn in *; exists eq_refl.
    + intros [x x1 x2] [y y1 y2] [z z1 z2] (-> & p1 & p2) (-> & q1 & q2); cbn in *.
      exists eq_refl; cbn.
      now rewrite p1, p2, q1, q2.
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
  - intros A B C [X l1 r1] [Y l2 r2].
    exists (pullback r1 l2).
    + exact (pullL .> l1).
    + exact (pullR .> r2).
  - intros A B C [X1 l1 r1] [X2 l2 r2] (p & Hp1 & Hp2)
                 [X3 l3 r3] [X4 l4 r4] (q & Hq1 & Hq2); cbn in *.
    destruct p, q. cbn in *.
    admit.
  - intros A B C D [X1 l1 r1] [X2 l2 r2] [X3 l3 r3]; cbn in *.
    admit.
  - intros A B [X l1 r1]; cbn.
Abort.