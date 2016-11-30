
Class Pros (A : Type) : Type :=
{
    leq : A -> A -> Prop;
    leq_refl : forall a : A, leq a a;
    leq_trans : forall a b c : A, leq a b -> leq b c -> leq a c
}.


Print Setoid.
Instance SetoidPros (A : Type) : Setoid (@Pros A).
refine {| equiv := fun P Q : @Pros A => @leq A P = @leq A Q |}.
split.
unfold Reflexive. trivial.
unfold Symmetric; intros. rewrite H. reflexivity.
unfold Transitive; intros; rewrite H, H0; reflexivity.
Defined.

Class Pros' : Type :=
{
    carr_ :> Type;
    pros_ :> @Pros carr_;
    setoid_ : 
}.
