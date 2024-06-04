Inductive tree (a : Type) :=
  | Leaf : tree a
  | Node : (a -> tree a) -> tree a.

Check(tree_ind).

Inductive forest := 
  | Cons : tree forest -> forest.
  