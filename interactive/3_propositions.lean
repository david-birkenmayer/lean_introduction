namespace MyLogic -- A namespace so the standard functions can be overwritten
set_option pp.fieldNotation false  -- makes terms easier to read

inductive N where
  | zero : N
  | succ : N → N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))

inductive Even : N → Prop where
  | base : Even zero
  | next {n : N} : Even n → Even (succ (succ n))
open Even

----------------------------------------------------------------------------------
-- **Part 3a: The Prop Type**
----------------------------------------------------------------------------------

-- Lean separates propositions into the 'Prop' Type. Its simplest inhabitants are:

inductive True : Prop where  -- True has one element
  | intro : True

inductive False : Prop where  -- False has no elements (since it cannot be proven)

-- When defining functions with output type 'Prop', we write *theorem* instead of 'def'
theorem double_even (n : N) : Even (double n) :=
  match n with
  | zero => base
  | succ n' => next (double_even n')

#reduce double_even (succ (succ zero))  -- Term doesn't unfold like before! Reason: Proof irrelevance

----------------------------------------------------------------------------------
-- **Part 3b: Negation**
----------------------------------------------------------------------------------

-- We use that ¬ A is the same as A → False
-- Hence, negation is just an abbreviation
def Not (P : Prop) : Prop := P → False
notation:max (priority := high) "¬" p:40 => Not p  -- This symbol can be made with \neg

-- One is not even
theorem one_is_not_even : ¬ Even (succ zero) :=
  fun s => nomatch s
-- the compiler can deduce that there is no combination of 'base' and 'next' that produces s.

----------------------------------------------------------------------------------
-- **Part 3c: Logical connectives**
----------------------------------------------------------------------------------

--*AND*--
-- A proof of P ∧ Q is a pair: a proof of P and a proof of Q
inductive And (P Q : Prop) : Prop where
  | intro (p : P) (q : Q) : And P Q
infixr:35 (priority := high) " ∧ " => And  -- This symbol can be made with \and

--*OR*--
-- A proof of P ∨ Q is a proof of P or a proof of Q, and it remembers which
inductive Or (P Q : Prop) : Prop where
  | inl (p : P) : Or P Q
  | inr (q : Q) : Or P Q
infixr:30 (priority := high) " ∨ " => Or  -- This symbol can be made with \or

--*IFF*--
-- A proof of P ↔ Q is a pair of functions, one in each direction
inductive Iff (P Q : Prop) : Prop where  -- This symbol can be made with \iff
  | intro (mp : P → Q) (mpr : Q → P) : Iff P Q
infix:20 (priority := high) " ↔ " => Iff

-- I let the RPTU LLM generate this proof for me!
theorem and_imp_of_or_imp {P Q R : Prop} (h : (P → R) ∨ (Q → R)) : (P ∧ Q) → R :=
  fun pq =>
  match h, pq with
  | Or.inl f, And.intro p _ => f p
  | Or.inr g, And.intro _ q => g q

----------------------------------------------------------------------------------
-- **Part 3d: Quantifiers**
----------------------------------------------------------------------------------

--*FORALL*--
-- '∀' is not a new idea: "for all n, P n" is exactly the function type (n : N) → P n.
-- Hence the symbol ∀ is just "syntactic sugar":
#check (n : N) → Even (double n)

-- So double_even was already a ∀-statement, we just did not call it one:
theorem double_even' : (n : N) → Even (double n) :=
  fun n => double_even n

--*EXISTS*--
-- A proof of "there is an x with P x" is a pair: a witness w, and a proof of P w.
-- Its definition reads:
inductive Exists' {α : Type} (P : α → Prop) : Prop where
  | intro (w : α) (h : P w) : Exists' P

#check ∃ n : N , Even n

-- To prove it you must *hand over* the witness :
theorem some_number_is_even : ∃ n : N , Even n :=
  Exists.intro zero base

----------------------------------------------------------------------------------
-- **Part 3e: Reading statements**
----------------------------------------------------------------------------------

-- *Translate the following theorem statements into mathematics:*

theorem example_1 {n : N} (h : Even n) : ¬ Even (succ n) := _

theorem example_2 : (n : N) → ∃ (m : N) , succ n = m := _

theorem example_3 (n : N) : Even n ↔ ∃ (k : N) , double k = n := _


end MyLogic
