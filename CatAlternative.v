Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.ProofIrrelevance.

Class Cat : Type :=
{
    Ob : Type;
    Hom : forall A B : Ob, Type;
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    id : forall A : Ob, Hom A A;
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
        comp (comp f g) h = comp f (comp g h);
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f = f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) = f
}.

Notation "f .> g" := (comp f g) (at level 50).

(*Definition hom_coercion `(C : Cat) := Hom.
Coercion hom_coercion : Cat >-> Funclass.*)

Ltac cat_rw := rewrite id_l || rewrite id_r || rewrite comp_assoc.
Ltac cat_rw' := rewrite id_l || rewrite id_r || rewrite <- comp_assoc.
Ltac cat_simpl := repeat cat_rw.
Ltac cat_simpl' := repeat cat_rw'.
Ltac cat := repeat (intros || cat_rw || auto).

(*Instance Sets : Cat.
split with
    (Ob := Set)
    (Hom := fun A B : Set => A -> B)
    (comp := fun (A B C : Set) (f : A -> B) (g : B -> C) => (fun a : A => g (f a)))
    (id := fun A : Set => (fun a : A => a));
auto.
Defined.*)

Definition ob `(C : Cat) := Ob.

Definition dom `(C : Cat) {A B : ob C} (_ : Hom A B) := A.

Definition cod `(C : Cat) {A B : Ob} (_ : Hom A B) := B.

Theorem id_unique_left : forall (C : Cat) (A : ob C) (idA : Hom A A),
    (forall (B : Ob) (f : Hom A B), idA .> f = f) -> idA = id A.
intros.
assert (eq1 : idA .> (id A) = id A). apply H.
assert (eq2 : idA .> (id A) = idA); cat.
rewrite <- eq1, eq2; trivial.
Qed.

Theorem id_unique_right : forall `(C : Cat) (B : Ob) (idB : Hom B B),
    (forall (A : Ob) (f : Hom A B), f .> idB = f) -> idB = id B.
intros.
assert (eq1 : id B .> idB = id B). apply H.
assert (eq2 : id B .> idB = idB); cat.
rewrite <- eq1, eq2; trivial.
Qed.

Definition End `{C : Cat} {A B : Ob} (f : Hom A B) : Prop := A = B.

Definition Mon `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom X A), g .> f = h .> f -> g = h.

Definition Epi `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    forall (X : Ob) (g h : Hom B X), f .> g = f .> h -> g = h.

Definition Bim `{C : Cat} {A B : Ob} (f : Hom A B) : Prop := Mon f /\ Epi f.

Definition Sec `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, f .> g = id A.

Definition Ret `{C : Cat} {A B : Ob} (f : Hom A B) : Prop :=
    exists g : Hom B A, g .> f = id B.

Definition Iso `{C : Cat} {A B : Ob} (f : Hom A B ) : Prop :=
   exists g : Hom B A, f .> g = id A /\ g .> f = id B.

Definition Aut `{C : Cat} {A : Ob} (f : Hom A A) : Prop := Iso f.

Definition isomorphic `{C : Cat} (A B : Ob) := exists f : Hom A B, Iso f.
Definition uniquely_isomorphic `{C : Cat} (A B : Ob) := exists! f : Hom A B, Iso f.

Notation "A ~ B" := (isomorphic A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic A B) (at level 50).

Definition balanced `(C : Cat) : Prop := forall (A B : Ob) (f : Hom A B),
    Iso f <-> Bim f.

Theorem sec_is_mon : forall `(C : Cat) (A B : Ob) (f : Hom A B),
    Sec f -> Mon f.
intros. unfold Sec, Mon in *. intros X h1 h2 eq. destruct H as (g, H).
assert (eq2 : (h1 .> f) .> g = (h2 .> f) .> g). rewrite eq; trivial.
rewrite comp_assoc, comp_assoc in eq2. rewrite H in eq2.
rewrite id_right, id_right in eq2. assumption.
Qed.

Class Functor `(C : Cat) `(D : Cat) : Type :=
{
    fob : ob C -> ob D;
    fhom : forall {A B : ob C}, Hom A B -> Hom (fob A) (fob B);
    pres_comp : forall {A B C : ob C} (f : Hom A B) (g : Hom B C),
        fhom (f .> g) = fhom f .> fhom g;
    pres_id : forall A : ob C, fhom (id A) = id (fob A)
}.

Definition Tob `(T : Functor) := fob.
Definition Thom `(T : Functor) {A B : ob C} (f : Hom A B) := fhom f.

Instance IdFunctor (C : Cat) : Functor C C.
split with
    (fob := fun A : ob C => A)
    (fhom := fun (A B : ob C) (f : Hom A B) => f);
trivial.
Defined.

Instance FunctorComp {C D E : Cat} (T : Functor C D) (S : Functor D E) : Functor C E.
split with
    (fob := fun A : ob C => fob (fob A))
    (fhom := fun (A B : ob C) (f : Hom A B) => fhom (fhom f)).
intros. repeat rewrite pres_comp; trivial.
intros. repeat rewrite pres_id; trivial.
Defined.

Axiom FunctorExt : forall (C D : Cat) (T S : Functor C D),
    T = S <-> (forall A : ob C, Tob T A = Tob S A) /\ 
        (forall (A B : ob C) (f : Hom A B), Tob T = Tob S -> Thom T f = Thom S f).

Axiom fn_ext_axiom : forall {A B : Set} (f g : A -> B),
forall a : A, f a = g a -> f = g.

Axiom functor_eq : forall `(T S : Functor), T = S <->
    

Instance CAT : Cat.
split with
    (Ob := Cat)
    (Hom := fun C D : Cat => Functor C D)
    (comp := fun (C D E : Cat) (T : Functor C D) (S : Functor D E) =>
        FunctorComp T S)
    (id := fun C : Cat => IdFunctor C);
intros.
unfold FunctorComp. auto. destruct f, g, h. simpl. repeat f_equal. f_equal.
apply fn_ext_axiom.