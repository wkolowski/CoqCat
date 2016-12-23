Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Coq.Classes.SetoidClass.

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Class Apartoid : Type :=
{
    carrier : Type;
    neq : carrier -> carrier -> Prop;
    neq_irrefl : forall x y : carrier, ~ neq x x;
    neq_sym : forall x y : carrier, neq x y -> neq y x;
    weird : forall x y z : carrier, neq x y -> neq z x \/ neq z y
}.
Print Apartoid.
Coercion carrier : Apartoid >-> Sortclass.

Hint Resolve neq_irrefl neq_sym weird.

(*Instance Apartoid_to_Setoid (A : Apartoid) : Setoid A :=
{
    equiv := fun x y : A => ~ neq x y
}.
Proof.
  split; red; intros; intro; eauto.
    eapply neq_irrefl; eauto.
    destruct (weird x z y H1); auto.
Defined.*)

Definition ApartoidHom (X Y : Apartoid) : Type :=
    {f : X -> Y | forall x x' : X, ~ neq x x' -> ~ neq (f x) (f x')}.

Definition ApartoidHomInj (X Y : Apartoid) : Type :=
    {f : X -> Y | forall x x' : X, neq x x' -> neq (f x) (f x')}.

Definition ApartoidHom_Fun {X Y : Apartoid} (f : ApartoidHom X Y) : X -> Y
    := proj1_sig f.
Coercion ApartoidHom_Fun : ApartoidHom >-> Funclass.

Definition ApartoidComp (X Y Z : Apartoid) (f : ApartoidHom X Y)
    (g : ApartoidHom Y Z) : ApartoidHom X Z.
Proof.
  red; destruct f as [f Hf], g as [g Hg].
  exists (fun x : X => g (f x)). auto.
Defined.

Definition ApartoidId (X : Apartoid) : ApartoidHom X X.
Proof.
  red. exists (fun x : X => x). auto.
Defined.

Instance ApartoidCat : Cat :=
{
    Ob := Apartoid;
    Hom := ApartoidHom;
    HomSetoid := fun X Y : Apartoid =>
        {| equiv := fun f g : ApartoidHom X Y => forall x : X, f x = g x |};
    comp := ApartoidComp;
    id := ApartoidId
}.
Proof.
  (* Equivalence *) cat. red. intros. rewrite H, H0. auto.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; simpl in *.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : ApartoidHom _ _ |- _ => destruct f
  end; simpl; auto.
Defined.

Instance Apartoid_init : Apartoid :=
{
    carrier := Empty_set;
    neq := fun (e : Empty_set) _ => match e with end
}.
Proof. all: destruct x. Defined.

Definition Apartoid_create (X : Apartoid) : ApartoidHom Apartoid_init X.
Proof.
  red; simpl. exists (fun (e : Empty_set) => match e with end). destruct x.
Defined.

Instance Apartoid_has_init : has_init ApartoidCat :=
{
    init := Apartoid_init;
    create := Apartoid_create
}.
Proof. cat. Defined.

(* Things can be done this way too. *)
Instance Apartoid_has_init' : has_init ApartoidCat := {}.
Proof.
  refine {| carrier := Empty_set;
      neq := fun (e : Empty_set) _ => match e with end |}; cat.
  repeat red; simpl in *; intros.
    exists (fun e : Empty_set => match e with end). destruct x.
    cat.
Defined.

Eval cbn in init ApartoidCat.

Instance Apartoid_term : Apartoid :=
{
    carrier := unit;
    neq := fun _ _ => False
}.
Proof. all: auto. Defined.

Definition Apartoid_delete (X : Apartoid) : ApartoidHom X Apartoid_term.
Proof.
  red; simpl. exists (fun _ => tt). auto.
Defined.

Instance Apartoid_has_term : has_term ApartoidCat :=
{
    term := Apartoid_term;
    delete := Apartoid_delete
}.
Proof. cat. Defined.

Instance Apartoid_prod (X Y : Apartoid) : Apartoid :=
{
    carrier := prod X Y;
    neq := fun (p1 : prod X Y) (p2 : prod X Y) =>
      neq (fst p1) (fst p2) \/ neq (snd p1) (snd p2)
}.
Proof.
  all: cat; destruct x, y; try destruct z; simpl in *.
    destruct 1.
      apply (@neq_irrefl X c); auto.
      apply (@neq_irrefl Y c0); auto.
    destruct H; auto.
    destruct H.
      destruct (weird _ _ c3 H); auto.
      destruct (weird _ _ c4 H); auto.
Defined.

Definition Apartoid_proj1 (X Y : Apartoid)
    : ApartoidHom (Apartoid_prod X Y) X.
Proof.
  red. exists fst. intros. destruct x, x'; simpl in *. intro.
  apply H. auto.
Defined.

Definition Apartoid_proj2 (X Y : Apartoid)
    : ApartoidHom (Apartoid_prod X Y) Y.
Proof.
  red. exists snd. intros. destruct x, x'; simpl in *. intro.
  apply H. auto.
Defined.

(*Definition Apartoid_mor_pair (X X' Y Y' : Apartoid)
    (f : ApartoidHom X X') (g : ApartoidHom Y Y')
    : ApartoidHom (Apartoid_prod X Y) (Apartoid_prod X' Y').
Proof.
  red. exists (fun p : X * Y => (f (fst p), g (snd p))).
  intros. destruct x as [x y], x' as [x' y'], f as [f Hf], g as [g Hg];
   simpl in *. specialize (Hf x x'); specialize (Hg y y').
  intro. destruct H0; [eapply Hf | eapply Hg]; auto.
Defined.
*)

Definition Apartoid_diag (A B X : Apartoid)
    (f : ApartoidHom X A) (g : ApartoidHom X B)
    : ApartoidHom X (Apartoid_prod A B).
Proof.
  red. exists (fun x : X => (f x, g x)). intros.
  intro. simpl in *. destruct f as [f Hf], g as [g Hg].
  destruct H0; simpl in *.
    eapply Hf; eauto.
    eapply Hg; eauto.
Defined.

Instance Apartoid_has_products : has_products ApartoidCat :=
{
    prodOb := Apartoid_prod;
    proj1 := Apartoid_proj1;
    proj2 := Apartoid_proj2;
    diag := Apartoid_diag
}.
Proof.
  repeat red; simpl; intros. rewrite H, H0. auto.
  unfold product; simpl; intros. cat. destruct f, g, y; simpl in *.
    rewrite H, H0. destruct (x2 x). auto.
Defined.