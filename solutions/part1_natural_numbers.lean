set_option pp.fieldNotation false


------  Part 1:  -------------
------  Natural Numbers ------


inductive N where
  | zero : N
  | succ (n : N) : N
open N

-- Every expression has a type. Put your cursor on a #check line and look at the Infoview.
#check (zero)
#check (succ)
#check succ (succ zero)


-- Functions are defined by pattern matching and recursion
-- Exercise: define double, a function which multiplies the input by two
def double (n : N) : N :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

#check (double)

-- #reduce evaluates an expression
#check double (succ (succ zero))
#reduce double (succ (succ zero))


-- Functions are values: they can be passed to other functions
-- Exercise: define "twice", which applies f two times to n
def twice (f : N -> N) (n : N) : N :=
  f (f n)

#check (twice)

-- Parameters don't have to be named before the colon:
-- we can move them into the type and bind them with "fun" (a lambda abstraction / anonymous function)
def twice' (f : N -> N) : N -> N :=
  fun n => f (f n)

def twice'' : (N -> N) -> N -> N :=
  fun f => fun n => f (f n)

-- Currying: If we don't supply all arguments, we get another function
#check twice double

-- Guess the result without looking!
#reduce twice double (succ zero)
#reduce twice succ zero
#reduce twice (fun n => double (succ n)) zero
#reduce twice (twice double) (succ zero)
#reduce twice (twice (twice double)) (succ zero)
