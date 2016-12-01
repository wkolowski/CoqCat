
Instance HomProsCat `(A : Pros) : @CatHom A.
split; intros a b. exact (a ≤ b).
Defined.

Instance CompProsCat `(A : Pros) : @CatComp A (HomProsCat A).
split; unfold Hom, HomProsCat; intros.
apply leq_trans with B; assumption.
Defined.

Instance IdProsCat `(A : Pros) : @CatId A (HomProsCat A).
split; unfold Hom, HomProsCat; intros.
apply leq_refl.
Defined.

Instance CatProsCat `(A : Pros) :
    @Cat A (HomProsCat A) (CompProsCat A) (IdProsCat A).
split; unfold Hom, HomProsCat, comp, CompProsCat;
intros; apply proof_irrelevance.
Defined.
