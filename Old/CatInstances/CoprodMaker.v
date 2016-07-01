Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Export Cat.

Record ObCoprodMaker `{_ : Cat} (A B : Ob) : Type :=
{
    C_ : Ob;
    f_ : Hom A C_;
    g_ : Hom B C_
}.

Record HomCoprodMaker' `{C : Cat} {A B : Ob} (X Y : ObCoprodMaker A B) :=
{
    h_ : Hom (C_ A B X) (C_ A B Y);
    eq1_ : f_ A B Y = f_ A B X .> h_;
    eq2_ : g_ A B Y = g_ A B X .> h_
}.

Axiom HomCoprodMaker_eq : forall `(C : Cat) (A B : Ob) (X Y : ObCoprodMaker A B)
    (f g : HomCoprodMaker' X Y), f = g <-> h_ X Y f = h_ X Y g.

Instance HomCoprodMaker `(C : Cat) (A B : Ob) : @CatHom (ObCoprodMaker A B).
split; intros. exact (HomCoprodMaker' A0 B0).
Defined.

Instance CompCoprodMaker `(C : Cat) (A B : Ob) :
    @CatComp (ObCoprodMaker A B) (HomCoprodMaker C A B).
split; unfold Hom, HomCoprodMaker; intros; destruct A0, B0, C0.
destruct X as [h1 h1_eq1 h1_eq2], X0 as [h2 h2_eq1 h2_eq2].
exists (h1 .> h2).
rewrite <- comp_assoc, <- h1_eq1, <- h2_eq1; cat.
rewrite <- comp_assoc, <- h1_eq2, <- h2_eq2; cat.
Defined.

Instance IdCoprodMaker `(C : Cat) (A B : Ob) :
    @CatId (ObCoprodMaker A B) (HomCoprodMaker C A B).
split; unfold Hom, HomCoprodMaker; intros; destruct A0.
exists (id C_0); cat.
Defined.

Instance CatCoprodMaker `(C : Cat) (A B : Ob) : @Cat (ObCoprodMaker A B)
    (HomCoprodMaker C A B) (CompCoprodMaker C A B) (IdCoprodMaker C A B).
split; unfold Hom, HomCoprodMaker, comp, CompCoprodMaker; intros.
destruct A0, B0, C0, D, f, g, h; apply HomCoprodMaker_eq; simpl; cat.
destruct A0, B0, f; apply HomCoprodMaker_eq; simpl; cat.
destruct A0, B0, f; apply HomCoprodMaker_eq; simpl; cat.
Defined.

Instance HomCoprodMaker2 `(C : Cat) (A B : Ob) : @CatHom (ObCoprodMaker A B).
split; intros. destruct A0, B0.
exact ({h : Hom C_0 C_1 | f_1 = f_0 .> h /\ g_1 = g_0 .> h}).
Defined.

Instance CompCoprodMaker2 `(C : Cat) (A B : Ob) :
    @CatComp (ObCoprodMaker A B) (HomCoprodMaker2 C A B).
split; unfold Hom, HomCoprodMaker; intros; destruct A0, B0, C0.
destruct X as [h1 [h1_eq1 h1_eq2]], X0 as [h2 [h2_eq1 h2_eq2]].
exists (h1 .> h2). split.
rewrite <- comp_assoc, <- h1_eq1, <- h2_eq1; cat.
rewrite <- comp_assoc, <- h1_eq2, <- h2_eq2; cat.
Defined.

Instance IdCoprodMaker2 `(C : Cat) (A B : Ob) :
    @CatId (ObCoprodMaker A B) (HomCoprodMaker2 C A B).
split; unfold Hom, HomCoprodMaker; intros; destruct A0.
exists (id C_0). split; cat.
Defined.

(* Add custom equality on HomCoprodMaker2 to make it work. 
Instance CatCoprodMaker2 `(C : Cat) (A B : Ob) : @Cat (ObCoprodMaker C A B)
    (HomCoprodMaker2 C A B) (CompCoprodMaker2 C A B) (IdCoprodMaker2 C A B).
split; unfold Hom, HomCoprodMaker2, comp, CompCoprodMaker2; intros.
destruct A0, B0, C0, D, f, g, h; simpl.
unfold comp, CompCoprodMaker.
Focus 2. destruct A0, B0; unfold comp, CompCoprodMaker; trivial.
f_equal. destruct f as [f [eq1 eq2]].
repeat rewrite eq1, eq2.*)