Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Export Cat.

Record ObProdMaker `(_ : Cat) (A B : Ob) : Type :=
{
    C_ : Ob;
    f_ : Hom C_ A;
    g_ : Hom C_ B
}.

Record HomProdMaker' `(C : Cat) (A B : Ob) (X Y : ObProdMaker C A B) : Type :=
{
    h_ : Hom (C_ C A B X) (C_ C A B Y);
    eq1_ : f_ C A B X = h_ .> f_ C A B Y;
    eq2_ : g_ C A B X = h_ .> g_ C A B Y
}.

Instance HomProdMaker `(C : Cat) (A B : Ob) : @CatHom (ObProdMaker C A B).
split; intros.
exact (HomProdMaker' C A B A0 B0).
Defined.

Instance CompProdMaker `(C : Cat) (A B : Ob) :
    @CatComp (ObProdMaker C A B) (HomProdMaker C A B).
split; unfold Hom, HomProdMaker; intros; destruct A0, B0, C0.
destruct X as [h1 h1_eq1 h1_eq2], X0 as [h2 h2_eq1 h2_eq2].
exists (h1 .> h2).
rewrite h1_eq1, h2_eq1; cat.
rewrite h1_eq2, h2_eq2; cat.
Defined.

Instance IdProdMaker `(C : Cat) (A B : Ob) :
    @CatId (ObProdMaker C A B) (HomProdMaker C A B).
split; unfold Hom, HomProdMaker; intros; destruct A0.
exists (id C_0); cat.
Defined.

(*Instance CatProdMaker `(C : Cat) (A B : Ob) : @Cat (ObProdMaker C A B)
    (HomProdMaker C A B) (CompProdMaker C A B) (IdProdMaker C A B).
split.
Focus 2.
intros. simpl. destruct A0, B0, f.
assert (id C_0 .> h_0 = h_0). cat. 
intros.

rewrite H.
pattern (id C_0 .> h_0) at 0. rewrite H.

 unfold Hom, HomProdMaker, comp, CompProdMaker; intros;
try destruct A0, B0, C0, D. destruct f, g, h.
assert ((h_0 .> h_1) .> h_2 = h_0 .> (h_1 .> h_2)). cat.
Focus 2.
destruct A0, B0, f. f_equal. cat.


f_equal.
Print proof_irrelevance.
decompose record.
rewrite proof_irrelevance with eq1_.

ance.
unfold comp, CompProdMaker.
Focus 2. destruct A0, B0; unfold comp, CompProdMaker; trivial.
f_equal. destruct f as [f [eq1 eq2]].
repeat rewrite eq1, eq2.




 destruct A0, B0.
exact ({h : Hom C_0 C_1 | f_0 = h .> f_1 /\ g_0 = h .> g_1}).
Defined.*)


(* OLD ONES
Instance CompProdMaker `(C : Cat) (A B : Ob) :
    @CatComp (ObProdMaker C A B) (HomProdMaker C A B).
split; unfold Hom, HomProdMaker; intros; destruct A0, B0, C0.
destruct X as [h1 [h1_eq1 h1_eq2]], X0 as [h2 [h2_eq1 h2_eq2]].
exists (h1 .> h2). split.
rewrite h1_eq1, h2_eq1; cat.
rewrite h1_eq2, h2_eq2; cat.
Defined.

Instance IdProdMaker `(C : Cat) (A B : Ob) :
    @CatId (ObProdMaker C A B) (HomProdMaker C A B).
split; unfold Hom, HomProdMaker; intros; destruct A0.
exists (id C_0). split; cat. *)
Defined.

Instance CatProdMaker `(C : Cat) (A B : Ob) : @Cat (ObProdMaker C A B)
    (HomProdMaker C A B) (CompProdMaker C A B) (IdProdMaker C A B).
split; unfold Hom, HomProdMaker (*comp, CompProdMaker*); intros;
try destruct A0, B0, C0, D. 
unfold comp, CompProdMaker.
Focus 2. destruct A0, B0; unfold comp, CompProdMaker; trivial.
f_equal. destruct f as [f [eq1 eq2]].
repeat rewrite eq1, eq2.*)