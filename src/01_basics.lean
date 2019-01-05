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

-- "Let mynat be the smallest set containing zero and succ x for every x ∈ mynat"
inductive mynat : Type
| zero : mynat
| succ (x : mynat) : mynat

#check mynat
#check mynat.zero
#check mynat.succ
#check mynat.rec



/-
  Inductive predicates
-/

-- The same mechanism can also define predicates

-- "Let le be the smallest relation containg ..."
inductive mynat.le : mynat → mynat → Prop
| refl {a} : mynat.le a a
| step {a b} : mynat.le a b → mynat.le a (mynat.succ b)



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


#print prefix mynat



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

#print instances has_zero

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
  Logical connectives
-/

section
-- Variables in a section are implicitly added
-- to all definitions/theorems/etc. (as needed)
variables (p q : Prop) (r : mynat → Prop)

#check p → q
#check ∀ x, r x

#check true
#check false
#check 0 = 1
#check 0 = (1 : mynat)
#check p ∨ q
#check ¬q
#check p ∧ q
#check p ↔ q
#check ∃ x, r x

#check ∀ x < 100, ∃ y > 20, ∃ z ∈ {0,1,2,3}, ∃ w, x+y = z+w

end



/-
  Theorems
-/

lemma mynat.zero_add (a : mynat) : 0 + a = a :=
begin
end

lemma mynat.add_comm (a b : mynat) : a + b = b + a :=
begin
end

lemma mynat.add_assoc (a b c : mynat) : a + b + c = a + (b + c) :=
begin
end

-- It's boring to write (a b c : mynat) every time.
section
variables (a b c : mynat)

lemma mynat.eq_iff_succ_eq_succ : succ a = succ b → a = b :=
begin
end

lemma mynat.add_cancel_right : a + c = b + c → a = b :=
begin
end

end



/-
  Notations
-/

notation `ℕ'` := mynat

#check (5 : ℕ')


-- supports various fancy stuff, e.g. mixfix operators and binders
def mysum {α} [has_add α] : mynat → (mynat → α) → α
| 0 f := f 0
| (succ a) f := mysum a f + f (succ a)

local notation `sum` binder `until` b `of` f:(scoped x, x) :=
mysum b f

#check sum i until 10 of i+20
#eval  sum i until 10 of i+20




/-
  There are two different kinds of "truth values":

   - Prop: types, erased at runtime
     ^^^^ this is what you use to state theorems

   - bool: inductive type with values tt/ff, computable
-/

#check true ∧ false ∨ true
#check tt && ff || tt

-- Lean automatically converts ("coerces") bools into Props
-- x  is coerced into  x = tt
example : (tt : Prop) := rfl

-- We can convert a Prop p into a bool if it is "decidable",
-- i.e. there is a function that computes whether p is true or not
#eval (∀ x ∈ [1,2,3,4], x^2 < x + 10 : bool)

-- decidable is implemented as a typeclass, and you can add your own instances
#print instances decidable

-- Many definitions in Lean use decidable propositions instead of bool:
#eval if ∀ x ∈ [1,2,3,4], x^2 < x + 10 then "ok" else "ko"
#check guard $ ∀ x ∈ [1,2,3,4], x^2 < x + 10
#check list.filter (λ x, x^2 < x + 10)

-- Choice implies that all propositions are decidable.
-- If we mark `classical.prop_decidable` as a type-class instance,
-- then if-then-else works on all propositions.
local attribute [instance, priority 0] classical.prop_decidable

-- However we cannot execute definitions that use choice to
-- construct data, such definitions are then marked as "noncomputable".
noncomputable def find_zero (f : ℕ → ℕ) : ℕ :=
if h : ∃ i, f i = 0 then classical.some h else 0

#eval find_zero (λ x, 1)



/-
  Definitional equality
-/

-- the free monoid generated by ℕ'
#check list mynat
#check ([1,4,3] : list mynat)

-- the free monoid generated by the carrier of the free monoid generated by ℕ'
#check list (list mynat)

def nested_list (α : Type u) : ℕ → Type u
| 0     := α
-- recursive calls only have arguments from after the colon
| (n+1) := list (nested_list n)

#reduce nested_list ℕ' 5

-- Why does this work?
example (n : ℕ) (xs : nested_list ℕ' (n+1)) :=
list.length xs -- xs needs to be a (list _) here, but it's a nested_list!

-- (nested_list _ (n+1)) reduces to a (list _):
#reduce λ n, nested_list ℕ' (n+1)
-- This is called "definitional equality".
-- In the underlying logic of Lean, both terms can be used interchangeably*.

#reduce λ n, n+1
#reduce λ n, 1+n

-- We can of course write functions that return nested_list
def n_singleton {α : Type u} : ∀ n, α → nested_list α n
-- in the base case, the return type is (nested_list α 0) =def= α
| 0     a := a
-- in the step case, the return type is
-- (nested_list α (n+1)) =def= (list (nested_list α n))
| (n+1) a := [n_singleton n a]

