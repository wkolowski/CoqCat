Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Set Universe Polymorphism.

Inductive sumprod (X Y : Set) : Set :=
    | inl' : X -> sumprod X Y
    | inr' : Y -> sumprod X Y
    | pair' : X -> Y -> sumprod X Y.

Arguments inl' [X] [Y] _.
Arguments inr' [X] [Y] _.
Arguments pair' [X] [Y] _ _.
