set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N


-------  Part 3:   -------
-------  Equality  -------


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
