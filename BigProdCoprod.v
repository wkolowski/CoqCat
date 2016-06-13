Require Export Cat.

Definition is_big_product `{C : Cat} {I : Set} {A : I -> Ob} (P : Ob)
    (p : forall i : I, Hom P (A i)) := forall (X : Ob) (i : I) (f : Hom X (A i)),
    exists! u : Hom X P, f = u .> p i.

Definition big_coproduct `{C : Cat} {J : Set} {A : J -> Ob} (P : Ob)
    (i : forall j : J, Hom (A j) P) := forall (X : Ob) (j : J) (f : Hom (A j) X),
    exists! u : Hom P X, f = i j .> u.

Theorem big_proj_ret : forall `(C : Cat) (I : Set) (A : I -> Ob) (P : Ob)
    (p : forall i : I, Hom P (A i)),
        is_big_product P p -> forall i : I, Ret (p i).
unfold is_big_product, Ret; intros.
destruct (H (A i) i (id (A i))) as (u, [eq uniq]).
exists u. rewrite eq. trivial.
Qed.

Theorem big_inj_sec : forall `(C : Cat) (J : Set) (A : J -> Ob) (P : Ob)
    (i : forall j : J, Hom (A j) P),
        big_coproduct P i -> forall j : J, Sec (i j).
unfold big_coproduct, Sec in *; intros.
destruct (H (A j) j (id (A j))) as (u, [eq uniq]); clear H.
exists u. rewrite <- eq. trivial.
Qed.