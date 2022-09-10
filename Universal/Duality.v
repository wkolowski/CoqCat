From Cat Require Export Cat.
From Cat.Universal Require Import
  Initial Terminal Zero Product Coproduct Biproduct Equalizer Coequalizer Pushout Pullback
  IndexedProduct IndexedCoproduct IndexedBiproduct Limit Colimit.

Set Implicit Arguments.

Lemma isInitial_Dual :
  forall (C : Cat) (X : Ob C) (delete : forall X' : Ob C, Hom X' X),
    isInitial (Dual C) X delete = isTerminal C X delete.
Proof. easy. Defined.

Lemma isTerminal_Dual :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    isTerminal (Dual C) X create = isInitial C X create.
Proof. easy. Defined.

Lemma isZero_Dual :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      isZero (Dual C) X delete create
        <->
      isZero C X create delete.
Proof. firstorder. Defined.

(*
#[refine]
#[export]
Instance HasInit'_Dual {C : Cat} {term : Ob C} (ht : HasTerm' C term) : HasInit' (Dual C) term :=
{
  create := @delete C _ ht;
}.
Proof.
  now rewrite isInitial_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasTerm'_Dual {C : Cat} {init : Ob C} (hi : HasInit' C init) : HasTerm' (Dual C) init :=
{
  delete := @create C _ hi;
}.
Proof.
  now rewrite isTerminal_Dual; typeclasses eauto.
Defined.
*)

#[refine]
#[export]
Instance HasInit_Dual (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
  create := @delete C ht;
}.
Proof.
  now rewrite isInitial_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
  delete := @create C hi;
}.
Proof.
  now rewrite isTerminal_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasZero_Dual (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  HasInit_HasZero := HasInit_Dual hz;
  HasTerm_HasZero := HasTerm_Dual hz;
}.
Proof.
  now cbn; symmetry; apply HasZero_spec.
Defined.

Lemma isProduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isProduct (Dual C) P finl finr copair
        <->
      isCoproduct C P finl finr copair.
Proof. firstorder. Defined.

Lemma isCoproduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair : forall (P' : Ob C) (outl' : Hom P' X) (outr' : Hom P' Y), Hom P' P),
      isCoproduct (Dual C) P outl outr fpair
        <->
      isProduct C P outl outr fpair.
Proof. firstorder. Defined.

Lemma isBiproduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr : Hom P Y) (finl : Hom X P) (finr : Hom Y P)
    (fpair : forall (P' : Ob C) (outl' : Hom P' X) (outr' : Hom P' Y), Hom P' P)
    (copair : forall (P' : Ob C) (finl' : Hom X P') (finr' : Hom Y P'), Hom P P'),
      isBiproduct (Dual C) P finl finr outl outr copair fpair
        <->
      isBiproduct C P outl outr finl finr fpair copair.
Proof. firstorder. Defined.

(*
#[refine]
#[export]
Instance HasProducts'_Dual
  {C : Cat} {coproduct : Ob C -> Ob C -> Ob C} (hp : HasCoproducts' C coproduct)
  : HasProducts' (Dual C) coproduct :=
{
  outl := @finl C _ hp;
  outr := @finr C _ hp;
  fpair := @copair C _ hp;
}.
Proof.
  now intros; apply isProduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasCoproducts'_Dual
  {C : Cat} {product : Ob C -> Ob C -> Ob C} (hp : HasProducts' C product)
  : HasCoproducts' (Dual C) product :=
{
  finl := @outl C _ hp;
  finr := @outr C _ hp;
  copair := @fpair C _ hp;
}.
Proof.
  now intros; apply isCoproduct_Dual; typeclasses eauto.
Defined.
*)

#[refine]
#[export]
Instance HasProducts_Dual (C : Cat) (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  product := @coproduct C hp;
  outl := @finl C hp;
  outr := @finr C hp;
  fpair := @copair C hp;
}.
Proof.
  now intros; apply isProduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coproduct := @product C hp;
  finl := @outl C hp;
  finr := @outr C hp;
  copair := @fpair C hp;
}.
Proof.
  now intros; apply isCoproduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasBiproducts_Dual (C : Cat) (hp : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  HasProducts_HasBiproducts := HasProducts_Dual hp;
  HasCoproducts_HasBiproducts := HasCoproducts_Dual hp;
}.
Proof.
  now cbn; symmetry; apply HasBiproducts_spec.
Defined.

Lemma isEqualizer_Dual :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (Q : Ob C) (q : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isEqualizer (Dual C) f g Q q cofactorize
        <->
      isCoequalizer C f g Q q cofactorize.
Proof. firstorder. Defined.

Lemma isCoequalizer_Dual :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (E : Ob C) (e : Hom E A)
    (factorize : forall (E' : Ob C) (e' : Hom E' A), e' .> f == e' .> g -> Hom E' E),
      isCoequalizer (Dual C) f g E e factorize
        <->
      isEqualizer C f g E e factorize.
Proof. firstorder. Defined.

#[refine]
#[export]
Instance HasEqualizers_Dual (C : Cat) (he : HasCoequalizers C) : HasEqualizers (Dual C) :=
{
  equalizer := fun A B : Ob (Dual C) => @coequalizer C he B A;
  equalize  := fun A B : Ob (Dual C) => @coequalize C he B A;
  factorize := fun A B : Ob (Dual C) => @cofactorize C he B A;
}.
Proof.
  now intros; apply isEqualizer_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_Dual (C : Cat) (he : HasEqualizers C) : HasCoequalizers (Dual C) :=
{
  coequalizer := fun A B : Ob (Dual C) => @equalizer C he B A;
  coequalize  := fun A B : Ob (Dual C) => @equalize C he B A;
  cofactorize := fun A B : Ob (Dual C) => @factorize C he B A;
}.
Proof.
  now intros; apply isCoequalizer_Dual; typeclasses eauto.
Defined.

Lemma isPullback_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (cofactor : forall (P' : Ob C) (pushl' : Hom X P') (pushr' : Hom Y P'),
                  f .> pushl' == g .> pushr' -> Hom P P'),
      isPullback (Dual C) f g P pushl pushr cofactor
        <->
      isPushout C f g P pushl pushr cofactor.
Proof. firstorder. Defined.

Lemma isPushout_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
    (P : Ob C) (pullL : Hom P X) (pullR : Hom P Y)
    (factor : forall (P' : Ob C) (pullL' : Hom P' X) (pullR' : Hom P' Y),
                pullL' .> f == pullR' .> g -> Hom P' P),
      isPushout (Dual C) f g P pullL pullR factor
        <->
      isPullback C f g P pullL pullR factor.
Proof. firstorder. Defined.

#[refine]
#[export]
Instance HasPullbacks_Dual (C : Cat) (hp : HasPushouts C) : HasPullbacks (Dual C) :=
{
  pullback := @pushout C hp;
  pullL := @pushl C hp;
  pullR := @pushr C hp;
  factor := @cofactor C hp;
}.
Proof.
  now intros; apply isPullback_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasPushouts_Dual (C : Cat) (hp : HasPullbacks C) : HasPushouts (Dual C) :=
{
  pushout := @pullback C hp;
  pushl := @pullL C hp;
  pushr := @pullR C hp;
  cofactor := @factor C hp;
}.
Proof.
  now intros; apply isPushout_Dual; typeclasses eauto.
Defined.

Lemma isIndexedProduct_Dual :
  forall
    (C : Cat) {J : Set} {A : J -> Ob C}
    (P : Ob C) (coproj : forall j : J, Hom (A j) P)
    (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X),
      isIndexedProduct (Dual C) P coproj (@cotuple)
        <->
      isIndexedCoproduct C P coproj (@cotuple).
Proof. firstorder. Defined.

Lemma isIndexedCoproduct_Dual :
  forall
    (C : Cat) {J : Set} {A : J -> Ob C}
    (P : Ob C) (proj : forall j : J, Hom P (A j))
    (tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P),
      isIndexedCoproduct (Dual C) P proj (@tuple)
        <->
      isIndexedProduct C P proj (@tuple).
Proof. firstorder. Defined.

Lemma isIndexedBiproduct_Dual :
  forall
    (C : Cat) {J : Set} {A : J -> Ob C}
    (P : Ob C) (proj : forall j : J, Hom P (A j)) (coproj : forall j : J, Hom (A j) P)
    (tuple : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
    (cotuple : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X),
      isIndexedBiproduct (Dual C) P coproj proj (@cotuple) (@tuple)
        <->
      isIndexedBiproduct C P proj coproj (@tuple) (@cotuple).
Proof. firstorder. Defined.

(*
#[refine]
#[export]
Instance HasIndexedProducts'_Dual
  {C : Cat} {indexedCoproduct : forall J : Set, (J -> Ob C) -> Ob C}
  (hp : HasIndexedCoproducts' C indexedCoproduct)
  : HasIndexedProducts' (Dual C) indexedCoproduct :=
{
  proj := @coproj C _ hp;
  tuple := @cotuple C _ hp;
}.
Proof.
  now intros; apply isIndexedProduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts'_Dual
  {C : Cat} {indexedProduct : forall J : Set, (J -> Ob C) -> Ob C}
  (hp : HasIndexedProducts' C indexedProduct)
  : HasIndexedCoproducts' (Dual C) indexedProduct :=
{
  coproj := @proj C _ hp;
  cotuple := @tuple C _ hp;
}.
Proof.
  now intros; apply isIndexedCoproduct_Dual; typeclasses eauto.
Defined.
*)

#[refine]
#[export]
Instance HasIndexedProducts_Dual
  {C : Cat} (hp : HasIndexedCoproducts C) : HasIndexedProducts (Dual C) :=
{
  indexedProduct := @indexedCoproduct C hp;
  proj := @coproj C hp;
  tuple := @cotuple C hp;
}.
Proof.
  now intros; apply isIndexedProduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_Dual
  {C : Cat} (hp : HasIndexedProducts C) : HasIndexedCoproducts (Dual C) :=
{
  indexedCoproduct := @indexedProduct C hp;
  coproj := @proj C hp;
  cotuple := @tuple C hp;
}.
Proof.
  now intros; apply isIndexedCoproduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasIndexedBiproducts_Dual
  (C : Cat) (hp : HasIndexedBiproducts C) : HasIndexedBiproducts (Dual C) :=
{
  HasIndexedProducts_HasIndexedBiproducts := HasIndexedProducts_Dual hp;
  HasIndexedCoproducts_HasIndexedBiproducts := HasIndexedCoproducts_Dual hp;
}.
Proof.
  cbn; symmetry; apply HasIndexedBiproducts_spec.
Defined.