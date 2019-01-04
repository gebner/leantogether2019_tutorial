/-
  Definitions
-/

def square (m : ℕ) : ℕ :=
m * m

-- We can write the same function as a lambda
def square' : ℕ → ℕ :=
λ (m : ℕ), m * m

-- ... or using pattern matching
def square'' : ℕ → ℕ
| 0     := 0
| (m+1) := square'' m + 2 * m + 1



/-
  Interactive commands
-/

#print square'

#eval square' 12

#check square
#check λ x, square (string.length x)

example (x : ℕ) : ℕ := square'' (2*x)


/-
  Polymorphic definitions
-/

-- types are first-class values
#check ℕ
#check Type
#check Type 1
#check Type 2

universes u v
#check Type u

-- polymorphic functions take the type as an extra argument
def injective (α : Type u) (β : Type v) (f : α → β) : Prop :=
∀ x y, f x = f y → x = y

#check injective ℕ ℕ nat.succ

-- using curly braces, Lean will fill in the type automatically ("implicit argument")
def injective' {α : Type u} {β : Type v} (f : α → β) : Prop :=
injective α β f

#check injective ℕ ℕ nat.succ
#check injective' nat.succ


/-
  Inductive types (≃ free algebras)
-/

inductive mynat : Type
| zero : mynat
| succ (x : mynat) : mynat

#check mynat
#check mynat.zero
#check mynat.succ
#check mynat.rec



/-
  Recursion
-/

def mynat.add (m : mynat) : mynat → mynat
-- pattern matching only applies to the arguments after the colon
| mynat.zero := m
| (mynat.succ x) := mynat.succ (mynat.add x)


/-
  Namespaces
-/

-- names in lean are separated by . (like / for file names)
#check mynat.add

-- after open, we no longer need to write the prefix
open mynat
#check add
#eval add (succ zero) (succ zero)

-- adds the prefix to all definitions
namespace mynat.foo
namespace bar
def baz := succ zero
end bar
end mynat.foo
#check mynat.foo.bar.baz



/-
  Structures
-/

structure point (α : Type u) :=
(x : α)
(y : α)

def pt : point ℕ := { y := 1, x := 2 }

#eval pt.y
#eval point.y pt

example : point ℕ := point.mk 1 2
example : point ℕ := ⟨1, 2⟩
example := { point . x := 1, y := 2 }
example : point ℕ := { x := 1, y := 2 }

example := { pt with x := 5 }

structure point3 (α : Type u) extends point α :=
(z : α)

example : point3 ℕ := { pt with z := 3 }


/-
  Type classes
-/

-- type classes allow us to define 0, 1, +, etc. for arbitrary objects
#check (0 : mynat)
#check (1 : mynat)
#check zero + zero

-- type class instances are just structures:
instance : has_zero mynat :=
{ zero := mynat.zero }

#check (0 : mynat)

instance : has_add mynat :=
{ add := mynat.add }

#check (0 + 0 : mynat)

@[instance] -- instances are just definitions with the [instance] "attribute"
def mynat.has_one : has_one mynat :=
⟨succ zero⟩ -- any structure instance syntax works

-- now numerals work!
#check (7 : mynat)

-- type class arguments are written in square brackets
def double {α : Type u} [has_add α] (x : α) :=
x + x

#check double (7 : mynat)


/-
  Notations
-/

notation `ℕ'` := mynat

#check (5 : ℕ')


/-
  Higher-order functions
-/

def twice {α : Type u} (f : α → α) (a : α) : α :=
f (f a)

def twice' {α : Type u} (f : α → α) : α → α :=
f ∘ f


/-
  Recursion
-/

def reverse {α : Type u} : list α → list α
-- pattern matching only applies to the arguments after the colon
| []      := []
| (x::xs) := reverse xs ++ [x]

def nested_list (α : Type u) : ℕ → Type u
| 0     := α
-- recursive calls only have arguments from after the colon
| (n+1) := list (nested_list n)

#reduce nested_list ℕ 5

-- Why does this work?
example (n : ℕ) (xs : nested_list string (n+1)) :=
reverse xs -- xs needs to be a (list _) here, but it's a nested_list!

-- (nested_list _ (n+1)) reduces to a (list _):
#reduce λ n, nested_list string (n+1)
-- This is called "definitional equality".

-- We can of course write functions that return nested_list
def n_singleton {α : Type u} : ∀ n, α → nested_list α n
-- in the base case, the return type is (nested_list α 0) =def= α
| 0     a := a
-- in the step case, the return type is (list (nested_list α n))
| (n+1) a := [n_singleton n a]


/-
  Inductive families
-/

inductive vector (α : Type u) : ℕ → Type u
| nil : vector 0
| cons {n : ℕ} (head : α) (tail : vector n) : vector (n+1)

def vector.head {α} : ∀ {n}, vector α (n+1) → α
| _ (vector.cons hd tl) := hd

#check vector.cons 3 (vector.cons 4 (vector.nil ℕ))
#eval vector.head $ vector.cons 3 (vector.cons 4 (vector.nil ℕ))