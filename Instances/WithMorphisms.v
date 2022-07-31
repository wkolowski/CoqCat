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
  destruct 1 as [f f_mon], 1 as [g g_mon].
    exists (f .> g). apply isMono_comp; auto.
  repeat (red || split).
    destruct C, x as [f1 f1_mon], y as [g1 g1_mon]; cbn in *;
    destruct x as [f2 f2_mon], y as [g2 g2_mon]; cbn in *; intros.
    rewrite H, H0. reflexivity.
  destruct f, g, h; cat.
  intro. exists (id A). red; cat.
  all: destruct f; cat.
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
  intros. destruct X as [f f_iso], X0 as [g g_iso].
    exists (f .> g). apply isIso_comp; assumption.
  unfold Proper, respectful; intros;
    destruct x, y, x0, y0; cbn in *. rewrite H, H0. reflexivity.
  intros; destruct f, g, h; cat.  
  intro. exists (id A). apply isAut_id.
  intros; destruct f; cat.
  intros; destruct f; cat.
Defined.