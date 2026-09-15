-- Natural numbers --

set_option pp.fieldNotation false           -- print succ (succ zero) instead of zero.succ.succ

inductive N where
  | zero : N
  | succ : N -> N
open N

-- Every expression has a type. Put your cursor on a #check line and look at the Infoview.
-- (Parentheses make #check show the type of an expression instead of a definition's signature.)
#check (zero)
#check (succ)
#check succ (succ zero)
#check N


-- Functions are defined by pattern matching and recursion
-- Exercise: define double

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

-- #reduce evaluates an expression
#reduce double (succ (succ zero))


-- Functions are values: they can be passed to other functions
-- Exercise: define twice, which applies f two times to n

def twice (f : N -> N) (n : N) : N :=
  f (f n)

-- Currying: guess the types first, then check!
#check (twice)
#check twice double
#reduce twice double (succ zero)
#reduce twice succ zero
#reduce twice (fun n => double (succ n)) zero   -- fun defines an anonymous function
#reduce twice (twice double) (succ zero)
-- #check twice twice                       -- Uncomment this line: why does it fail?


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
