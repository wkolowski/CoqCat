From Cat Require Export Cat.
From Cat.Universal Require Import
  Initial Terminal Zero Product Coproduct Biproduct Equalizer Coequalizer Pushout Pullback
  IndexedProduct IndexedCoproduct IndexedBiproduct Limit Colimit.

Set Implicit Arguments.

Lemma isInitial_Dual :
  forall (C : Cat) (X : Ob C) (delete : forall X' : Ob C, Hom X' X),
    @isInitial (Dual C) X delete = @isTerminal C X delete.
Proof. easy. Defined.

Lemma isTerminal_Dual :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @isTerminal (Dual C) X create = @isInitial C X create.
Proof. easy. Defined.

Lemma isZero_Dual :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero (Dual C) X delete create <-> @isZero C X create delete.
Proof. firstorder. Defined.

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

#[export]
Instance HasInit_Dual (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
}.

#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
}.

#[export]
Instance HasZero_Dual (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  HasInit'_HasZero := HasInit_Dual hz;
  HasTerm'_HasZero := HasTerm_Dual hz;
}.

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

#[export]
Instance HasProducts_Dual (C : Cat) (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  product := @coproduct C hp;
  HasProducts'_HasProducts := HasProducts'_Dual hp;
}.

#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coproduct := @product C hp;
  HasCoproducts'_HasCoproducts := HasCoproducts'_Dual hp;
}.

#[export]
Instance HasBiproducts_Dual (C : Cat) (hp : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  HasProducts'_HasBiproducts := HasProducts'_Dual hp;
  HasCoproducts'_HasBiproducts := HasCoproducts'_Dual hp;
}.

Lemma isEqualizer_Dual :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (Q : Ob C) (q : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      @isEqualizer (Dual C) B A f g Q q cofactorize
        <->
      @isCoequalizer C A B f g Q q cofactorize.
Proof. firstorder. Defined.

Lemma isCoequalizer_Dual :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (E : Ob C) (e : Hom E A)
    (factorize : forall (E' : Ob C) (e' : Hom E' A), e' .> f == e' .> g -> Hom E' E),
      @isCoequalizer (Dual C) B A f g E e factorize
        <->
      @isEqualizer C A B f g E e factorize.
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