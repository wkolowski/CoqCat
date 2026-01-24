From Cat Require Import Cat.
From Cat.Universal Require Import
  Duality Initial Terminal Product Coproduct IndexedProduct IndexedCoproduct.

Class HasInit' (C : Cat) (I : Ob C) : Type :=
{
  create : forall X : Ob C, Hom I X;
  isInitial_HasInit' :: isInitial C I create;
}.

Arguments create {C _ _} _.

Coercion isInitial_HasInit' : HasInit' >-> isInitial.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  HasInit'_HasInit :: HasInit' C init;
}.

Arguments init _ {_}.

Coercion HasInit'_HasInit : HasInit >-> HasInit'.

Class HasTerm' (C : Cat) (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  isTerminal_HasTerm' :: isTerminal C T delete;
}.

Arguments delete {C _ _} _.

Coercion isTerminal_HasTerm' : HasTerm' >-> isTerminal.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm'_HasTerm :: HasTerm' C term;
}.

Arguments term _ {_}.

Coercion HasTerm'_HasTerm : HasTerm >-> HasTerm'.

Class HasZero (C : Cat) : Type :=
{
  zero : Ob C;
  HasInit'_HasZero :: HasInit' C zero;
  HasTerm'_HasZero :: HasTerm' C zero;
}.

Arguments zero _ {_}.

Coercion HasInit'_HasZero : HasZero >-> HasInit'.
Coercion HasTerm'_HasZero : HasZero >-> HasTerm'.

#[export]
Instance HasInit_HasZero {C : Cat} (hz : HasZero C) : HasInit C :=
{
  init := zero C;
}.

#[export]
Instance HasTerm_HasZero {C : Cat} (hz : HasZero C) : HasTerm C :=
{
  term := zero C;
}.

Coercion HasInit_HasZero : HasZero >-> HasInit.
Coercion HasTerm_HasZero : HasZero >-> HasTerm.

Class HasProducts' (C : Cat) (product : Ob C -> Ob C -> Ob C) : Type :=
{
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
  isProduct_HasProducts' ::
    forall {A B : Ob C}, isProduct C (product A B) outl outr (@fpair A B)
}.

Arguments outl   {C product HasProducts' A B}.
Arguments outr   {C product HasProducts' A B}.
Arguments fpair  {C product HasProducts' A B X} _ _.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  HasProducts'_HasProducts :: HasProducts' C product;
}.

Arguments product {C HasProducts} _ _.

Coercion HasProducts'_HasProducts : HasProducts >-> HasProducts'.

Class HasCoproducts' (C : Cat) (coproduct : Ob C -> Ob C -> Ob C) : Type :=
{
  finl     : forall {A B : Ob C}, Hom A (coproduct A B);
  finr     : forall {A B : Ob C}, Hom B (coproduct A B);
  copair   : forall {A B : Ob C} {P : Ob C} (f : Hom A P) (g : Hom B P), Hom (coproduct A B) P;
  isCoproduct_HasCoproducts' ::
    forall {A B : Ob C}, isCoproduct C (@coproduct A B) finl finr (@copair A B);
}.

Arguments finl     {C coproduct HasCoproducts' A B}.
Arguments finr     {C coproduct HasCoproducts' A B}.
Arguments copair   {C coproduct HasCoproducts' A B P} _ _.

Class HasCoproducts (C : Cat) : Type :=
{
  coproduct : forall (A B : Ob C), Ob C;
  HasCoproducts'_HasCoproducts :: HasCoproducts' C coproduct;
}.

Arguments coproduct {C HasCoproducts} _ _.

Coercion HasCoproducts'_HasCoproducts : HasCoproducts >-> HasCoproducts'.

Class HasBiproducts (C : Cat) : Type :=
{
  biproduct : Ob C -> Ob C -> Ob C;
  HasProducts'_HasBiproducts :: HasProducts' C biproduct;
  HasCoproducts'_HasBiproducts :: HasCoproducts' C biproduct;
  HasBiproducts_ok :
    forall {A B : Ob C},
      @outl _ _ _ A B .> @finl _ _ _ A B .> @outr _ _ _ A B .> @finr _ _ _ A B
        ==
      outr .> finr .> outl .> finl;
}.

Coercion HasProducts'_HasBiproducts : HasBiproducts >-> HasProducts'.
Coercion HasCoproducts'_HasBiproducts : HasBiproducts >-> HasCoproducts'.

#[export]
Instance HasProducts_HasBiproducts {C : Cat} (hb : HasBiproducts C) : HasProducts C :=
{
  product := biproduct;
}.

#[export]
Instance HasCoproducts_HasBiproducts {C : Cat} (hb : HasBiproducts C) : HasCoproducts C :=
{
  coproduct := biproduct;
}.

Coercion HasProducts_HasBiproducts : HasBiproducts >-> HasProducts.
Coercion HasCoproducts_HasBiproducts : HasBiproducts >-> HasCoproducts.

Class HasIndexedProducts'
  (C : Cat) (indexedProduct : forall {J : Type} (A : J -> Ob C), Ob C) : Type :=
{
  out :
    forall {J : Type} {A : J -> Ob C} (j : J), Hom (indexedProduct A) (A j);
  tuple :
    forall {J : Type} {A : J -> Ob C} {X : Ob C} (f : forall j : J, Hom X (A j)),
      Hom X (indexedProduct A);
  HasIndexedProducts_isIndexedProduct ::
    forall {J : Type} {A : J -> Ob C},
      isIndexedProduct C (indexedProduct A) (@out J A) (@tuple J A)
}.

Arguments out  {C _ _ J A} _.
Arguments tuple {C _ _ J A X} _.

Class HasIndexedProducts (C : Cat) : Type :=
{
  indexedProduct : forall {J : Type} (A : J -> Ob C), Ob C;
  HasIndexedProducts'_HasIndexedProducts :: HasIndexedProducts' C (@indexedProduct);
}.

Arguments indexedProduct {C _ J} _.

Coercion HasIndexedProducts'_HasIndexedProducts :
  HasIndexedProducts >-> HasIndexedProducts'.

Class HasIndexedCoproducts'
  (C : Cat) (indexedCoproduct : forall J : Type, (J -> Ob C) -> Ob C) : Type :=
{
  inj :
    forall (J : Type) (A : J -> Ob C) (j : J),
      Hom (A j) (indexedCoproduct J A);
  cotuple :
    forall (J : Type) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom (A j) X),
      Hom (indexedCoproduct J A) X;
  isIndexedCoproduct_HasIndexedCoproducts' ::
    forall (J : Type) (A : J -> Ob C),
      isIndexedCoproduct C (indexedCoproduct J A) (inj J A) (cotuple J A)
}.

Arguments inj  {C _ _ J A} _.
Arguments cotuple {C _ _ J A X} _.

Class HasIndexedCoproducts (C : Cat) : Type :=
{
  indexedCoproduct : forall J : Type, (J -> Ob C) -> Ob C;
  HasIndexedCoproducts'_HasIndexedCoproducts :: HasIndexedCoproducts' C (@indexedCoproduct);
}.

Arguments indexedCoproduct [C _ J] _.

Coercion HasIndexedCoproducts'_HasIndexedCoproducts :
  HasIndexedCoproducts >-> HasIndexedCoproducts'.

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

#[refine]
#[export]
Instance HasIndexedProducts'_Dual
  {C : Cat} {indexedCoproduct : forall J : Type, (J -> Ob C) -> Ob C}
  (hp : HasIndexedCoproducts' C indexedCoproduct)
  : HasIndexedProducts' (Dual C) indexedCoproduct :=
{
  out := @inj C _ hp;
  tuple := @cotuple C _ hp;
}.
Proof.
  now intros; apply isIndexedProduct_Dual; typeclasses eauto.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts'_Dual
  {C : Cat} {indexedProduct : forall J : Type, (J -> Ob C) -> Ob C}
  (hp : HasIndexedProducts' C indexedProduct)
  : HasIndexedCoproducts' (Dual C) indexedProduct :=
{
  inj := @out C _ hp;
  cotuple := @tuple C _ hp;
}.
Proof.
  now intros; apply isIndexedCoproduct_Dual; typeclasses eauto.
Defined.