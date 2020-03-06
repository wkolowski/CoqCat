Require Import Cat.

Class ProdMakerOb (C : Cat) (A B : Ob C) : Type :=
{
    pmob : Ob C;
    pmmorl : Hom pmob A;
    pmmorr : Hom pmob B
}.

Coercion pmob : ProdMakerOb >-> Ob.

Arguments pmob [C A B] _.
Arguments pmmorl [C A B] _.
Arguments pmmorr [C A B] _.

Ltac pmob X := try intros until X;
match type of X with
  | ProdMakerOb _ _ _ => 
    let a := fresh X "_f" in
    let b := fresh X "_g" in destruct X as [X [a b]]
  | Ob _ => progress cbn in X; pmob X
end; cbn in X.

Ltac pmobs := repeat
match goal with
  | X : ProdMakerOb _ _ _ |- _ => pmob X
  | X : Ob _ |- _ => pmob X
end.

Class ProdMakerHom {C : Cat} {A B : Ob C} (X Y : ProdMakerOb C A B) : Type :=
{
    pmhom : Hom X Y;
    pmhom_coherence : pmhom .> pmmorl Y == pmmorl X;
    pmhom_coherence' : pmhom .> pmmorr Y == pmmorr X;
}.

Coercion pmhom : ProdMakerHom >-> Hom.

Arguments pmhom [C A B X Y] _.

Ltac pmhom f := try intros until f;
match type of f with
  | ProdMakerHom _ _ =>
      let a := fresh f "_eq1" in
      let b := fresh f "_eq2" in destruct f as [f a b]
  | Hom _ _ => progress simpl in f; pmhom f
end; cbn in f.

Ltac pmhoms := intros; repeat
match goal with
  | f : ProdMakerHom _ _ |- _ => pmhom f
  | f : Hom _ _ |- _ => pmhom f
  | _ => idtac
end.

Hint Rewrite @id_left @id_right @pmhom_coherence @pmhom_coherence'
  : prodmaker_base.

Ltac pm := intros;
match goal with
    | |- Proper _ _ => proper
    | |- Equivalence _ => solve_equiv
    | |- context [pmmorl] => autorewrite with prodmaker_base
    | |- context [pmmorr] => autorewrite with prodmaker_base
    | |- ?x == ?x => reflexivity
    | _ => repeat (my_simpl || pmobs || pmhoms || cat)
end.

#[refine]
Instance ProdMakerHomSetoid {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    : Setoid (ProdMakerHom P1 P2) :=
{
    equiv := fun h h' : ProdMakerHom P1 P2 =>
        @equiv _ (HomSetoid P1 P2) h h'
}.
Proof. pm. Defined.

#[refine]
Instance ProdMakerComp {C : Cat} {A B : Ob C} (P1 P2 P3 : ProdMakerOb C A B)
  (h : ProdMakerHom P1 P2) (h' : ProdMakerHom P2 P3) : ProdMakerHom P1 P3 :=
{
    pmhom := h .> h'
}.
Proof.
  all: assocr; pm; reflexivity.
Defined.

#[refine]
Instance ProdMakerId {C : Cat} {A B : Ob C} (P : ProdMakerOb C A B)
    : ProdMakerHom P P :=
{
    pmhom := id P
}.
Proof. all: pm; reflexivity. Defined.

#[refine]
Instance ProdMaker (C : Cat) (A B : Ob C) : Cat :=
{
    Ob := ProdMakerOb C A B;
    Hom := ProdMakerHom;
    HomSetoid := ProdMakerHomSetoid;
    comp := ProdMakerComp;
    id := ProdMakerId
}.
Proof. all: pm. Defined.

(* TODO : prove this is equvalent to the usual products *)