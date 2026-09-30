set_option pp.fieldNotation false  -- makes terms easier to read
namespace MyLogic -- A namespace so the standard functions can be overwritten

inductive N where
  | zero : N
  | succ : N -> N
open N

def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))

inductive Even : N -> Prop where
  | base : Even zero
  | next {n : N} : Even n → Even (succ (succ n))
open Even

----------------------------------------------------------------------------------
-- **Part 2a: The Prop Type**
----------------------------------------------------------------------------------

-- Lean seperates propositions into the 'Prop' Type, which contains True and False

inductive True : Prop where  -- True has one element
  | intro : True

inductive False : Prop where  -- False has no elements

-- When defining functions with output type 'Prop', we write *theorem* instead of 'def'
theorem double_even (n : N) : Even (double n) :=
  match n with
  | zero => base
  | succ n' => next (double_even n')

----------------------------------------------------------------------------------
-- **Part 2b: Negation**
----------------------------------------------------------------------------------

-- We use that ¬ A is the same as A → False
-- Hence, negation just an abbreviation
def Not (P : Prop) : Prop := P → False
notation:max (priority := high) "¬" p:40 => Not p  -- This symbol can be made with \neg

-- *Prove that one is not even*
theorem one_is_not_even : ¬ Even (succ zero) :=
  fun s => nomatch s
-- the compiler can deduce that there is no combination of 'base' and 'next' that produces s.

-- *Show that, from falsity, anything can be proven*
theorem ex_falso_quodlibet {P : Prop} (s : False) : P :=
  nomatch s

-- A more sophisticated negation proof.
theorem succ_even_is_not_even {n : N} (h : Even n) : ¬ Even (succ n) :=
  fun s =>
  match h, s with
  | next h', next s' => succ_even_is_not_even h' s'
-- We have to provide a way of reducing to a impossible case.
-- The compiler rules out the other cases.

----------------------------------------------------------------------------------
-- **Part 2c: Logical connectives**
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
  | intro (mp : P -> Q) (mpr : Q -> P) : Iff P Q
infix:20 (priority := high) " ↔ " => Iff

-- I let the RPTU LLM generate this proof for me!
theorem and_assumption {P Q R : Prop} (h : (P → R) ∨ (Q → R)) : (P ∧ Q) -> R :=
  fun pq =>
  match h, pq with
  | Or.inl f, And.intro p _ => f p
  | Or.inr g, And.intro _ q => g q

----------------------------------------------------------------------------------
-- **Part 2c: Quantifiers**
----------------------------------------------------------------------------------

--*FORALL*--
-- This, like negation, is just an abbreviation, not a datatype.
macro (priority := high) "∀ " x:ident " : " t:term ", " b:term : term =>
  `(($x : $t) -> $b)  -- This symbol can be made with \forall or \all

-- We can rewrite the double even function using this:
theorem double_even' : ∀ n : N , Even (double n):=
  fun n => double_even n

--*EXISTS*--
-- A proof of ∃ x, P x is a pair: a witness w and a proof of P w
inductive Exists {α : Type} (P : α -> Prop) : Prop where
  | intro (w : α) (h : P w) : Exists P
macro (priority := high) "∃ " x:ident " : " t:term ", " b:term : term =>
`(Exists (fun ($x : $t) => $b))  -- This symbol can be made with \exists

-- Here a trivial existence statement.
theorem trivial : ∃ n : N , Even n :=
  Exists.intro zero base

end MyLogic
