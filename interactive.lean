namespace My


-- Natural numbers --

inductive N where
  | zero
  | succ (n : N)
open N

def double (n : N) : N :=
  match n with
  | zero => _
  | succ n => _


-- Even numbers --

inductive Even : N -> Prop where
  |  zero_even : Even zero
  |  next_even {n} : Even n -> Even (succ (succ n))
open Even

theorem two_is_even : Even (succ (succ zero)) :=
  _

theorem double_is_even (n : N) : Even (double n) :=
  match n with
  | zero => _
  | succ n => _


-- Equality on Natural numbers --

inductive NEqual : N -> N -> Prop where
  | base : NEqual zero zero
  | step {n m : N}  : NEqual n m -> NEqual (succ n) (succ m)
open NEqual
infix:20 (priority := high) " ≡ " => NEqual

theorem reflexive {n : N} : n ≡ n :=
  match n with
  | zero => _
  | succ n => _

theorem symmetric {n m : N} (p: n ≡ m) : m ≡ n :=
  match p with
  | base   => _
  | step p (n:=n) (m:=m) => _

theorem transitive {n m k : N} (p : n ≡ m) (q : m ≡ k) : n ≡ k :=
  match p, q with
  | base, base => _
  | step (n:=n) (m:=m) p, step (m := k) q => _


-- Addition --

def add (n m : N) : N :=
  match m with
  | zero => n                               -- Base case:      n + 0 := n
  | succ m => succ (add n m)                -- Inductive case: n + (m + 1) := (n + m) + 1
infix:50 (priority := high) " + " => add

theorem right_NE {n : N} : n + zero ≡ n :=
  _

theorem left_NE {n : N} : zero + n ≡ n :=
  _

theorem associativity (n m k : N) : (n + m) + k ≡ n + (m + k) :=
  _


-- Final Boss --

theorem commutative (n m : N) : n + m ≡ m + n :=  -- Hint: You need to define a helper-theorem to solve this one
  _

end My

