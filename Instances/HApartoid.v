From Cat Require Export Cat.
From Cat.Universal Require Import
  Initial Terminal Product Coproduct Equalizer IndexedProduct IndexedCoproduct.

Class HApartoid : Type :=
{
  carrier : Type;
  hneq : forall (A B : Type), A -> B -> Prop;
  hneq_irrefl : forall (A : Type) (x : A), ~ hneq A A x x;
  hneq_sym : forall (A B : Type) (x : A) (y : B),
    hneq A B x y -> hneq B A y x;
  hneq_cotrans : forall (A B C : Type) (x : A) (y : B) (z : C),
    hneq A B x y -> hneq C A z x \/ hneq C B z y
}.

Arguments hneq [HApartoid] [A] [B] _ _.

Coercion carrier : HApartoid >-> Sortclass.

Definition HApartoidHom (X Y : HApartoid) : Type :=
  {f : X -> Y | forall x x' : carrier, ~ hneq x x' -> ~ hneq (f x) (f x')}.

Definition HApartoidHom_Fun (X Y : HApartoid) (f : HApartoidHom X Y) : X -> Y := proj1_sig f.
Coercion HApartoidHom_Fun : HApartoidHom >-> Funclass.

Definition HApartoidComp
  (X Y Z : HApartoid) (f : HApartoidHom X Y) (g : HApartoidHom Y Z) : HApartoidHom X Z.
Proof.
  exists (fun x : X => g (f x)).
  intros x y Hn Hng.
  destruct f as [f Hf], g as [g Hg]; cbn in *.
  eapply Hg; [| exact Hng].
Abort.