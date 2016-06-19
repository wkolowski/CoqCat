Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import CatInstances.

Inductive empty : Set := .

Instance HomEmpty : @CatHom empty.
split; intros. exact empty.
Defined.

Instance CompEmpty : @CatComp empty HomEmpty.
split; unfold Hom, HomEmpty; intros. trivial.
Defined.

Instance IdEmpty : @CatId empty HomEmpty.
split; unfold Hom, HomEmpty; intros. trivial.
Defined.

Instance CatEmpty : @Cat empty HomEmpty CompEmpty IdEmpty.
split; destruct f.
Defined.

Instance HomUnit : @CatHom unit.
split; intros. exact unit.
Defined.

Instance CompUnit : @CatComp unit HomUnit.
split; trivial.
Defined.

Instance IdUnit : @CatId unit HomUnit.
split; trivial.
Defined.

Instance CatUnit : @Cat unit HomUnit CompUnit IdUnit.
split; destruct A, B, f; trivial.
Defined.