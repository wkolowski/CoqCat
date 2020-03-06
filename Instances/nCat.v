Require Import Arith.
Require Import Omega.

Require Import Cat.

#[refine]
Instance N (n : nat) : Cat :=
{
    Ob := {k : nat | k <= n};
    Hom := fun X Y => proj1_sig X <= proj1_sig Y;
    HomSetoid := fun _ _ => {| equiv := fun _ _ => True |}
        (* proof irrelevance *)
}.
Proof.
  (* Equiv *) solve_equiv.
  (* composition *) destruct A, B, C. simpl. intros.
    eapply le_trans; eauto.
  (* Proper *) proper.
  (* Category laws *) all: cat.
Defined.

