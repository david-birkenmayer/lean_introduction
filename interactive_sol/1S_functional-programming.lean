set_option pp.fieldNotation false -- makes terms easier to read

----------------------------------------------------------------------------------
-- **Part 1: Natural Numbers**
----------------------------------------------------------------------------------

-- 'inductive' defines the inductive datatype N
inductive N where
  | zero : N
  | succ : N → N

-- **Click on the #-Keywords with the cursor, and look at the "Messages" tab in the InfoView on the right**

#print N  -- *#print shows all the properties that 'N' has

open N  -- allows us to access 'N.zero' and 'N.succ' as 'zero' and 'succ'

#check zero -- check shows the type of a term
#check succ
#check succ (succ zero)  -- function application is denoted with a space: f x, not f(x). It associates to the left
#check N  -- 'Type' is the "type of small types", like 'Int', 'Bool', 'N', etc.

-- **Define a function which adds two to a number**
def add2 : N → N :=
  fun n => succ (succ n)

#check add2
#check add2 (succ zero)
#reduce add2 (succ zero)  -- #reduce evaluates a term

-- We can declare n in the function signature so we don't have to use the "fun" keyword
def add2' (n : N) : N :=
  succ (succ n)

#check (add2')
#check add2'  -- without brackets, Lean will show n explicitly. This will be important later.

-- **Define double, a function which multiplies the input by two**
-- Functions are often defined by pattern matching and recursion.
-- A natural number is, by definition, either zero or the successor of another natural number n'
def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n' => add2 (double n')

#check (double)
#reduce double (succ (succ zero))


-- Functions are values: they can be passed to other functions
-- **Define "twice", which applies f two times to n**
def twice (f : N → N) (n : N) : N :=
  f (f n)

#check (twice)

-- Currying: If we don't supply all arguments, we get another function
#check twice double

-- **Guess the result without looking**
#reduce twice double (succ zero)
#reduce twice succ zero
#reduce twice (fun n => double (succ n)) zero
#reduce twice (twice double) (succ zero)
