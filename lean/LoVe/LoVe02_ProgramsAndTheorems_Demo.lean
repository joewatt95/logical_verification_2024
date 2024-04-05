/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Demo 2: Programs and Theorems

We continue our study of the basics of Lean, focusing on programs and theorems,
without carrying out any proofs yet. We review how to define new types and
functions and how to state their intended properties as theorems. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Type Definitions

An __inductive type__ (also called __inductive datatype__,
__algebraic datatype__, or just __datatype__) is a type that consists all the
values that can be built using a finite number of applications of its
__constructors__, and only those.


### Natural Numbers -/

namespace MyNat

/- Definition of type `Nat` (= `ℕ`) of natural numbers, using unary notation: -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` outputs the definition of its argument. -/

#print Nat

end MyNat

/- Outside namespace `MyNat`, `Nat` refers to the type defined in the Lean core
library unless it is qualified by the `MyNat` namespace. -/

#print Nat
#print MyNat.Nat

/- ### Arithmetic Expressions -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
  deriving BEq, DecidableEq

/- ### Lists -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## Function Definitions

The syntax for defining a function operating on an inductive type is very
compact: We define a single function and use __pattern matching__ to extract the
arguments to the constructors. -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- When there are multiple arguments, separate the patterns by `,`: -/

def add : ℕ → ℕ → ℕ
  | m, .zero   => m
  | m, .succ n => .succ <| add m n

/- `#eval` and `#reduce` evaluate and output the value of a term. -/

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, .zero   => .zero
  | m, .succ n => add m <| mul m n

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, .zero   => 1
  | m, .succ n => mul m <| power m n

#eval power 2 5

/- `add`, `mul`, and `power` are artificial examples. These operations are
already available in Lean as `+`, `*`, and `^`.

If it is not necessary to pattern-match on an argument, it can be moved to
the left of the `:` and made a named argument: -/

def powerParam (m : ℕ) : ℕ → ℕ
  | .zero   => 1
  | .succ n => mul m <| powerParam m n

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | .zero   => z
  | .succ n => f <| iter α z f n

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def append (α : Type) : List α → List α → List α
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x <| append α xs ys

/- Because `append` must work for any type of list, the type of its elements is
provided as an argument. As a result, the type must be provided in every call
(or use `_` if Lean can infer the type). -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

/- If the type argument is enclosed in `{ }` rather than `( )`, it is implicit
and need not be provided in every call (provided Lean can infer it). -/

def appendImplicit {α : Type} : List α → List α → List α
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x <| appendImplicit xs ys

#eval appendImplicit [3, 1] [4, 1, 5]

/- Prefixing a definition name with `@` gives the corresponding definition in
which all implicit arguments have been made explicit. This is useful in
situations where Lean cannot work out how to instantiate the implicit
arguments. -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- Aliases:

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | .num i     => i
  | .var x     => env x
  | .add e₁ e₂ => eval env e₁ + eval env e₂
  | .sub e₁ e₂ => eval env e₁ - eval env e₂
  | .mul e₁ e₂ => eval env e₁ * eval env e₂
  | .div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (λ _x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Lean only accepts the function definitions for which it can prove
termination. In particular, it accepts __structurally recursive__ functions,
which peel off exactly one constructor at a time.


## Theorem Statements

Notice the similarity with `def` commands. `theorem` is like `def` except that
the result is a proposition rather than data or a function. -/

namespace SorryTheorems

attribute [simp] add

example {n} : add n .zero = n := by simp only [add]

@[simp]
lemma zero_add : ∀ {n}, add 0 n = n
  | .zero => by simp only [add]
  | .succ n => by simp only [add, zero_add]

@[simp]
theorem add_comm : ∀ {m n}, add m n = add n m
  | .zero, _ | _, .zero => by simp only [zero_add, add]
  | .succ m, .succ n =>
    have h₀ : add m n = add n m := add_comm
    have h₁ : add (.succ m) n = add n (.succ m) := add_comm
    have h₂ : add m (.succ n) = add (.succ n) m := add_comm
    calc add (.succ m) (.succ n)
      = .succ (add (.succ m) n) := by simp only [add]
    _ = .succ (add n (.succ m)) := by rw [h₁]
    _ = add (add n m) 2 := by simp only [add]
    _ = add (add m n) 2 := by rw [h₀]
    _ = .succ (add m (.succ n)) := by simp only [add]
    _ = .succ (add (.succ n) m) := by rw [h₂]
    _ = add (.succ n) (.succ m) := by simp only [add]

@[simp]
theorem add_assoc {l m} :
  ∀ {n}, add (add l m) n = add l (add m n)
  | .zero => by simp only [add]
  | .succ n =>
    calc add (add l m) (.succ n)
     _ = .succ (add (add l m) n) := by simp only [add]
     _ = .succ (add l (add m n)) := by rw [add_assoc]
     _ = add l (add m (.succ n)) := by simp only [add]

@[simp]
lemma zero_mul : ∀ {n}, mul .zero n = .zero
  | .zero => by simp only [mul]
  | .succ n => by simp only [mul, zero_mul, add]

@[simp]
lemma succ_add {m} : ∀ {n}, add (.succ m) n = .succ (add m n)
  | 0 | .succ n => by simp only [add, succ_add]

@[simp]
lemma succ_mul {m} :
  ∀ {n}, mul (.succ m) n = add (mul m n) n
  | 0 => by simp only [mul, add]
  | .succ n => by simp only [mul, add, succ_mul, succ_add, add_assoc]

@[simp]
lemma add_add {a b} :
  ∀ {c}, add a (add b c) = add b (add a c)
  | 0 => by simp only [add, add_comm]
  | .succ c => by simp only [add, add_add]

@[simp]
theorem mul_comm :
  ∀ {m n}, mul m n = mul n m
  | 0, _ | _, 0 => by simp only [zero_mul, mul]

  | .succ m, .succ n =>
    have : mul m n = mul n m := mul_comm
    by simp only [mul, succ_mul, this, add_comm, add, add_add]

@[simp]
theorem mul_add {l m} :
  ∀ {n}, mul l (add m n) = add (mul l m) (mul l n)
  | 0 => rfl
  | .succ _ => by simp only [mul, mul_add, add_add]

@[simp]
theorem mul_assoc {l m} :
  ∀ {n}, mul (mul l m) n = mul l (mul m n)
  | 0 => by aesop
  | .succ n =>
    have : mul (mul l m) n = mul l (mul m n) := mul_assoc
    calc
      mul (mul l m) (.succ n)
    = add (mul l m) (mul (mul l m) n) := by simp only [mul]
  _ = mul l (add m (mul m n)) := by aesop
  _ = mul l (mul m (.succ n)) := by simp only [mul]

-- lemma eq_nil_of_length {α} : ∀ {xs : List α}, xs.length = 0 → xs = []
--   | [], _ | _ :: _, _ => by aesop

lemma reverse_cons {α} {y : α} :
  ∀ {xs : List α}, reverse (xs ++ [y]) = y :: reverse xs
  | [] => by aesop
  | x :: xs => calc
    reverse (x :: xs ++ [y])
_ = reverse (xs ++ [y]) ++ [x] := by simp only [reverse, List.append_eq]
_ = y :: reverse xs ++ [x] := by simp only [reverse_cons]
_ = y :: reverse (x :: xs) := by simp only [List.cons_append, reverse]

@[simp]
theorem reverse_reverse {α : Type} :
  ∀ {xs : List α}, reverse (reverse xs) = xs
  | [] => rfl
  | x :: xs => by simp only [reverse, reverse_cons, reverse_reverse]

theorem reverse_append {α} {xs : List α} :
  ∀ {ys : List α}, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [] => by aesop
  | y :: ys => calc
    reverse (xs ++ y :: ys)
_ = reverse (xs ++ [y] ++ ys) :=
    by simp only [List.append_assoc, List.singleton_append]
_ = reverse ys ++ reverse (xs ++ [y]) := reverse_append
_ = reverse ys ++ [y] ++ reverse xs :=
    by simp only [reverse_cons, List.append_assoc, List.singleton_append]
_ = reverse (y :: ys) ++ reverse xs := by simp only [reverse]

/- Axioms are like theorems but without proofs. Opaque declarations are like
definitions but without bodies. -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
  a < b

end SorryTheorems

end LoVe
