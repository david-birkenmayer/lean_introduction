namespace My


-- Natural numbers --

inductive N where
  | zero
  | succ (n : N)
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))


-- Even numbers --

inductive Even : N -> Prop where
  |  zero_even : Even zero
  |  next_even {n} : Even n -> Even (succ (succ n))
open Even

theorem two_is_even : Even (succ (succ zero)) :=
  next_even zero_even

theorem double_is_even (n : N) : Even (double n) :=
  match n with
  | zero => zero_even
  | succ n => next_even (double_is_even n)


-- Equality on Natural numbers --

inductive NEqual : N -> N -> Prop where
  | base : NEqual zero zero
  | step {n m : N}  : NEqual n m -> NEqual (succ n) (succ m)
open NEqual
infix:20 (priority := high) " ≡ " => NEqual

theorem reflexive {n : N} : n ≡ n :=
  match n with
  | zero => base
  | succ n => step (reflexive)

theorem symmetric {n m : N} (p: n ≡ m) : m ≡ n :=
  match p with
  | base   => reflexive
  | step p (n:=n) (m:=m) => step (symmetric p)

theorem transitive {n m k : N} (p : n ≡ m) (q : m ≡ k) : n ≡ k :=
  match p, q with
  | base, base => reflexive
  | step (n:=n) (m:=m) p, step (m := k) q => step (transitive p q)


-- Addition --

def add (n m : N) : N :=
  match m with
  | zero => n                               -- Base case:      n + 0 := n
  | succ m => succ (add n m)                -- Inductive case: n + (m + 1) := (n + m) + 1
infix:50 (priority := high) " + " => add

theorem right_NE {n : N} : n + zero ≡ n :=
  reflexive

theorem left_NE {n : N} : zero + n ≡ n :=
  match n with 
  | zero => reflexive
  | succ _ => step (left_NE)

theorem associativity (n m k : N) : (n + m) + k ≡ n + (m + k) :=
  match k with
  | zero => reflexive
  | succ k => step (associativity n m k)


-- Final Boss --

theorem one_commutative (m n : N) : succ (m + n) ≡ (succ m) + n :=
  match n with
  | zero => reflexive
  | succ n => step (one_commutative m n)

theorem commutative (n m : N) : n + m ≡ m + n :=
  match m with
  | zero => symmetric (left_NE)
  | succ m => transitive (step (commutative n m)) (one_commutative m n)

end My

