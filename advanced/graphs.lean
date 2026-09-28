set_option pp.fieldNotation false


------  Classes:  ------------
------  Monoids and Groups ---

variable {α : Type}

class DiGraph α where
  adj: α -> α -> Prop
infixl:70 (priority := high) " E " => DiGraph.adj

class Graph α extends DiGraph α where
  sym {a b : α} : a E b -> b E a

inductive Path {α} : α -> α -> Type where
  | empty (a : α) (a : α) : Path a a
  | cons (a : α) (b : α) {c : α} (p : Path c b) (h : DiGraph.adj b c) : Path a b
