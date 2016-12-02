Require Export Cat.
Require Export BinProdCoprod.
Require Export BigProdCoprod.

(* These theorems are actually FALSE. This is obvious (well, at least now),
   because if P and Q are both products of A and B, then they're isomorphic
   to A × B, so the number of isomorphisms between P and Q is |A × B|!
   in the case of finite sets.

   Something else is true: there is an unique isomorphism that is compatible
   (dunno in what precise sense for now) with the projections. *)
Theorem product_uniquely_isomorphic : forall (C : Cat) (A B : Ob C) (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob C) (qA : Hom Q A) (qB : Hom Q B),
    product C P pA pB -> product C Q qA qB -> P ~~ Q.
Proof.
  unfold product; intros.
  destruct (H Q qA qB) as [f [[f_eq1 f_eq2] f_unique]].
  destruct (H0 P pA pB) as [g [[g_eq1 g_eq2] g_unique]].
  red. exists g. red. split.
    red. exists f. split.
      destruct (H P pA pB) as [idP [[idP_eq1 idP_eq2] idP_unique]].
        assert (idP == id P). apply idP_unique. cat.
        rewrite <- H1. symmetry. apply idP_unique. split.
          rewrite comp_assoc, <- f_eq1. assumption.
          rewrite comp_assoc, <- f_eq2. assumption.
      destruct (H0 Q qA qB) as [idQ [[idQ_eq1 idQ_eq2] idQ_unique]].
        assert (idQ == id Q). apply idQ_unique. cat.
        rewrite <- H1. symmetry. apply idQ_unique. split.
          rewrite comp_assoc, <- g_eq1. assumption.
          rewrite comp_assoc, <- g_eq2. assumption.
    intros. apply g_unique. split.
Abort.

(* This one is false, too. *)
Theorem big_product_uniquely_isomorphic : forall (C : Cat) (J : Set)
    (A : J -> Ob C) (P Q : Ob C) (p : forall j : J, Hom P (A j))
    (q : forall j : J, Hom Q (A j)) (j : J),
    big_product P p -> big_product Q q -> P ~~ Q.
unfold big_product; intros. unfold uniquely_isomorphic, isomorphic.
destruct (H0 P j (p j)) as [u1 [eq1 uniq1]],
(H Q j (q j)) as [u2 [eq2 uniq2]].
exists u1. unfold Iso. split. exists u2. split.
destruct (H P j (p j)) as [i [eq_id uniq_id]].
assert (i_is_id : i == id P). apply uniq_id. cat.
rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
rewrite <- eq2. assumption.
destruct (H0 Q j (q j)) as [i [eq_id uniq_id]].
assert (i_is_id : i == id Q). apply uniq_id. cat.
rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
rewrite <- eq1. assumption.
intros. apply uniq1.
destruct H1 as [g eq]. (*
specialize (H0 P j (x' .> g .> p j)).
specialize (H Q j (g .> x' .> q j)).

******************

unfold big_product, uniquely_isomorphic, isomorphic; intros.
assert (P ~ Q). apply big_product_iso_unique with J A p q; assumption.
destruct H1 as [f f_iso].
exists f; split. assumption.
intros f' f'_iso. destruct (H0 P j (p j)).
destruct H1 as [eq unique].
assert (x = f). apply unique. *)
Restart.
  intros. red; unfold setoid_unique.
    assert (H_iso : P ~ Q). eapply big_product_iso_unique.
      exact j. exact H. exact H0.
    destruct H_iso as [f [g [iso_eq1 iso_eq2]]]. exists f. split.
      unfold Iso. exists g. auto.
      intros. unfold big_product in *.
        destruct H1 as [y_inv [y_iso_eq1 y_iso_eq2]].
        destruct (H P j (f .> y_inv .> p j)) as [xu1 [xeq1 xunique1]].
        specialize (xunique1 (f .> y_inv)).




        destruct (H P j (f .> (q j))) as [u1 [eq1 unique1]].
        destruct (H Q j (g .> (p j))) as [u2 [eq2 unique2]].
        destruct (H0 Q j (g .> (p j))) as [u4 [eq4 unique4]].
        destruct (H0 P j (f .> (q j))) as [u3 [eq3 unique3]].
        assert (u3 == f). apply unique3. reflexivity.
        destruct (H P j (y .> (q j))) as [y_u1 [y_eq1 y_unique1]].
        destruct (H Q j (y_inv .> (p j))) as [y_u2 [y_eq2 y_unique2]].
        destruct (H0 Q j (y_inv .> (p j))) as [y_u4 [y_eq4 y_unique4]].
        destruct (H0 P j (y .> (q j))) as [y_u3 [y_eq3 y_unique3]].
        rewrite <- H1. apply unique3. rewrite eq1, y_eq1.
assert (u1 == id P). apply unique1. cat.