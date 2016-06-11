Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.

Notation "f .> g" := (compose g f) (at level 50).

Axiom fn_ext : forall (A B : Type) (f g : A -> B),
    f = g <-> forall a : A, f a = g a.

Class Functor (F : Type -> Type) : Type :=
{
    fmap : forall {A B : Type}, (A -> B) -> F A -> F B;
    pres_id : forall A : Type, fmap (@id A) = @id (F A);
    pres_comp : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap (f .> g) = fmap f .> fmap g
}.

Inductive Maybe (A : Type) : Type :=
    | Nothing : Maybe A
    | Just : A -> Maybe A.

Arguments Nothing {A}.
Arguments Just {A} _.

Notation "A ?" := (Maybe A) (at level 50).

Fixpoint fmap_maybe (A B : Type) (f : A -> B) (ma : A?) : B? := match ma with
    | Nothing => Nothing
    | Just a => Just (f a)
end.

Instance FunctorMaybe : Functor Maybe.
split with (fmap := fmap_maybe);
intros; rewrite fn_ext; intros; destruct a; trivial.
Defined.

(*Class Applicative (F : Type -> Type) : Type :=
{
    functor :> Functor F;
    pure : forall A : Type, A -> F A;
    ap : forall A B : Type, F (A -> B) -> F A -> F B;
    pure_id : forall (A : Type) (a : A), ap (pure (id)) a = a
}.*)

Class Monad (M : Type -> Type) : Type :=
{
    functor :> Functor M;
    ret : forall {A : Type}, A -> M A;
    (*bind : forall A B : Type, M A -> (A -> M B) -> M B*)
    mcomp : forall {A B C : Type}, (A -> M B) -> (B -> M C) -> (A -> M C);
    unit_l : forall (A B : Type) (f : A -> M B), mcomp ret f = f;
    unit_r : forall (A B : Type) (f : A -> M B), mcomp f ret = f;
    mcomp_assoc : forall (A B C D : Type) (f : A -> M B) (g : B -> M C)
        (h : C -> M D), mcomp f (mcomp g h) = mcomp (mcomp f g) h
}.

Notation "f >=> g" := (mcomp f g) (at level 50).

(* WRONG AS FK
Definition bind `{_ : Monad} {A B : Type} (a : M A) (f : A -> M B)
    := (fun _ : A => a) >=> f.*)

Eval compute in bind Nothing (fun a => Just 22).

Definition comp_maybe {A B C : Type} (f : A -> B?) (g : B -> C?) (a : A) : C? :=
    match f a with
    | Nothing => Nothing
    | Just b => g b
end.

Instance MonadMaybe : Monad Maybe.
split with
    (ret := fun (A : Type) => @Just A)
    (mcomp := fun A B C : Type => @comp_maybe A B C); intros.
try apply FunctorMaybe.
rewrite fn_ext; trivial.
rewrite fn_ext; intros. unfold comp_maybe. destruct (f a); trivial.
rewrite fn_ext; intros. unfold comp_maybe. destruct (f a); trivial.
Defined.

Eval compute in fmap (fun x => x + 2) (Just 5).
Eval compute in ((fun a => Just (a + 5)) >=> (fun a => Just (a * a))) 2.


