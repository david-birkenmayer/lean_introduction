set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

inductive NEqual : N -> N -> Prop where
  | base : NEqual zero zero
  | step {n m : N}  : NEqual n m -> NEqual (succ n) (succ m)
open NEqual
infix:20 (priority := high) " ≡ " => NEqual

theorem reflexive {n : N} : n ≡ n :=
  match n with
  | zero => base
  | succ _ => step (reflexive)

theorem symmetric {n m : N} (p: n ≡ m) : m ≡ n :=
  match p with
  | base   => reflexive
  | step p (n:=n) (m:=m) => step (symmetric p)

theorem transitive {n m k : N} (p : n ≡ m) (q : m ≡ k) : n ≡ k :=
  match p, q with
  | base, base => reflexive
  | step (n:=n) (m:=m) p, step (m := k) q => step (transitive p q)


-------  Part 3:   -------
-------  Addition  -------


def add (n m : N) : N :=
  match m with
  | zero => _
  | succ m => _
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
