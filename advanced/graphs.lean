set_option pp.fieldNotation false


------  Classes:  ------------
------  Monoids and Groups ---


--universe u
variable {α : Type}

class DiGraph α where
  adj: α -> α -> Prop
infixl:70 (priority := high) " E " => DiGraph.adj

class Graph α extends DiGraph α where
  sym {a b : α} : a E b -> b E a

inductive Path {α} [DiGraph α] : α -> α -> Type where
  | nil  {a : α} : Path a a
  | cons {a b c : α} (h : a E b) (p : Path b c) : Path a c
open Path

def Reachable {α} [DiGraph α] (a b : α) : Prop := Nonempty (Path a b)
def Cycle {α} [DiGraph α] (a : α) : Type :=  Path a a

def length [DiGraph α] {a b : α} (p : Path a b) : Nat :=
  match p with
  | nil => 0
  | cons h p' => length p + 1
