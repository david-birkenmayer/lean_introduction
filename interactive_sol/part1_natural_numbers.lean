set_option pp.fieldNotation false -- option which makes terms easier to read


------  Part 1:  -------------
------  Natural Numbers ------


inductive N where
  | zero : N
  | succ : N -> N

open N  -- allows us to write to zero and succ instead of N.zero and N.succ

-- Every term has a type.
-- Put your cursor on a #check line and look at the "Messages" tab in the InfoView.
#check zero
#check succ
#check succ (succ zero)  -- application is denoted with a space: f x, not f(x).
                         -- It associates to the left: f x y means (f x) y.
#check N

-- Exercise: Define a function which adds two to a number
def add2 : N -> N :=
  fun n => succ (succ n)

#check add2
#check add2 (succ zero)
#reduce add2 (succ zero)  -- #reduce evaluates a term

-- We can declare n in the function signature so we don't have to use the "fun" keyword
def add2' (n : N) : N :=
  succ (succ n)

#check (add2')
#check add2'  -- without brackets, Lean will show n explicitly. This will be important later.


-- Functions are often defined by pattern matching and recursion.
-- Exercise: define double, a function which multiplies the input by two
def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))

#check (double)
#reduce double (succ (succ zero))


-- Functions are values: they can be passed to other functions
-- Exercise: define "twice", which applies f two times to n
def twice (f : N -> N) (n : N) : N :=
  f (f n)

#check (twice)

-- Currying: If we don't supply all arguments, we get another function
#check twice double

-- Guess the result without looking!
#reduce twice double (succ zero)
#reduce twice succ zero
#reduce twice (fun n => double (succ n)) zero
#reduce twice (twice double) (succ zero)
