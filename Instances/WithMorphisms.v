From Cat Require Import Cat.

#[refine]
#[export]
Instance WithMono (C : Cat) : Cat :=
{
  Ob := Ob C;
  Hom := fun X Y : Ob C => {f : Hom X Y | isMono f};
  HomSetoid := fun X Y : Ob C => Setoid_kernel_equiv (HomSetoid X Y) (@proj1_sig (Hom X Y) isMono)
}.
Proof.
  - intros X Y Z [f Hf] [g Hg].
    exists (f .> g).
    now apply isMono_comp.
  - intros X Y Z [f1 Hf1] [f2 Hf2] Hf [g1 Hg1] [g2 Hg2] Hg; cbn in *.
    now rewrite Hf, Hg.
  - intros X Y Z W [f Hf] [g Hg] [h Hh]; cbn in *.
    now rewrite comp_assoc.
  - intros X.
    exists (id X).
    now apply isMono_id.
  - intros X Y [f Hf]; cbn.
    now rewrite comp_id_l.
  - intros X Y [f Hf]; cbn.
    now rewrite comp_id_r.
Defined.

#[refine]
#[export]
Instance WithIso (C : Cat) : Cat :=
{
  Ob := Ob C;
  Hom := fun A B : Ob C => {f : Hom A B | isIso f};
  HomSetoid := fun A B : Ob C => Setoid_kernel_equiv (HomSetoid A B) (@proj1_sig (Hom A B) isIso)
}.
Proof.
  - intros X Y Z [f Hf] [g Hg].
    exists (f .> g).
    now apply isIso_comp.
  - intros X Y Z [f1 Hf1] [f2 Hf2] Hf [g1 Hg1] [g2 Hg2] Hg; cbn in *.
    now rewrite Hf, Hg.
  - intros X Y Z W [f Hf] [g Hg] [h Hh]; cbn in *.
    now rewrite comp_assoc.
  - intros X.
    exists (id X).
    now apply isIso_id.
  - intros X Y [f Hf]; cbn.
    now rewrite comp_id_l.
  - intros X Y [f Hf]; cbn.
    now rewrite comp_id_r.
Defined.