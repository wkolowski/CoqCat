From Cat Require Import Cat.

#[refine]
#[export]
Instance N (n : nat) : Cat :=
{
  Ob := {k : nat | k <= n};
  Hom := fun X Y => proj1_sig X <= proj1_sig Y;
  HomSetoid := fun _ _ => {| equiv := fun _ _ => True |}
}.
Proof.
  - now solve_equiv.
  - now intros [a Ha] [b Hb] [c Hc] Hab Hbc; cbn in *; transitivity b.
  - now proper.
  - easy.
  - easy.
  - easy.
  - easy.
Defined.