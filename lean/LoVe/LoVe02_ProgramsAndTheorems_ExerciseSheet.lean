/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo

import Mathlib.Data.Nat.Basic

/- # LoVe Exercise 2: Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Predecessor Function

1.1. Define the function `pred` of type `ℕ → ℕ` that returns the predecessor of
its argument, or 0 if the argument is 0. For example:

    `pred 7 = 6`
    `pred 0 = 0` -/

def pred : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

/- 1.2. Check that your function works as expected. -/

#eval pred 0    -- expected: 0
#eval pred 1    -- expected: 0
#eval pred 2    -- expected: 1
#eval pred 3    -- expected: 2
#eval pred 10   -- expected: 9
#eval pred 99   -- expected: 98


/- ## Question 2: Arithmetic Expressions

Consider the type `AExp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `AExp` or `eval`;
3. click the identifier. -/

#check AExp
#check eval

/- 2.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `AExp`) are unrelated. -/

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

notation Γ:25 "⊢" expr:25 "⇓" val:25 => eval Γ expr = val

#eval eval someEnv (.var "x")   -- expected: 3
-- invoke `#eval` here

example : someEnv ⊢ .var "x" ⇓ 3 := by decide

/- 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : AExp → AExp
  | .num i => .num i
  | .var x => .var x

  -- | .add (.num 0) e | .add e (.num 0) => simplify e
  -- | .add e₁ e₂ => .add (simplify e₁) (simplify e₂)

  | .add e₁ e₂ => match e₁, e₂ with
    | .num 0, _ => simplify e₂
    | _, .num 0 => simplify e₁
    | _, _ => .add (simplify e₁) (simplify e₂)

  | .sub e₁ e₂ => match e₁, e₂ with
   | _, .num 0 => simplify e₁
   | _, _ => if e₁ = e₂ then .num 0 else .sub (simplify e₁) (simplify e₂)

  | .mul e₁ e₂ => match e₁, e₂ with
    | .num 0, _ | _, .num 0 => .num 0
    | .num 1, _ => simplify e₂
    | _, .num 1 => simplify e₁
    | _, _ => .mul (simplify e₁) (simplify e₂)

  | .div e₁ e₂ => match e₁, e₂ with
    | .num 0, _ | _, .num 0 => .num 0
    | _, .num 1 => simplify e₁
    | _, _ => .div (simplify e₁) (simplify e₂)

/- 2.3. Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

section SimplifyCorrect

syntax "recurse" "on" sepBy1(ident, "then") "and" "finally" tactic : term

set_option hygiene false in
macro_rules
  | `(recurse on $[$ids] then* and finally $tactic) => do
    let mut result ← `(by $tactic;)
    for index in [:ids.size] do
      let indexFromEnd := ids.size - 1 - index
      if let some id := ids[indexFromEnd]? then
        result ← `(
          have : ∀ {val}, Γ ⊢ $id ⇓ val ↔ Γ ⊢ simplify $id ⇓ val :=
            simplify_correct
          $result
        )
    `($result)

-- set_option trace.Elab.command true
-- set_option trace.Elab.step true

attribute [simp] eval simplify in
theorem simplify_correct {Γ val} :
  ∀ {expr}, Γ ⊢ expr ⇓ val ↔ Γ ⊢ simplify expr ⇓ val
  | .num _ | .var _ => by simp only [eval]

  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ | .div e₁ e₂ =>
    recurse on e₁ then e₂ and finally aesop

end SimplifyCorrect

/- ## Question 3 (**optional**): Map

3.1 (**optional**). Define a generic `map` function that applies a function to
every element in a list. -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs

#eval map (λ n ↦ n + 10) [1, 2, 3]   -- expected: [11, 12, 13]

/- 3.2 (**optional**). State (without proving them) the so-called functorial
properties of `map` as theorems. Schematically:

     map (λ x ↦ x) xs = xs
     map (λ x ↦ g (f x)) xs = map g (map f xs)

Try to give meaningful names to your theorems. Also, make sure to state the
second property as generally as possible, for arbitrary types. -/

-- enter your theorem statements here

theorem map_id {α} : ∀ {xs : List α}, map id xs = xs
  | [] => rfl
  | _ :: _ => by simp only [map, id_eq, map_id]

theorem map_comp {α β γ} {f : α → β} {g : β → γ} :
  ∀ {xs : List α}, map (g ∘ f) xs = map g (map f xs)
  | [] => rfl
  | _ :: _ => by simp only [map, Function.comp_apply, map_comp]

end LoVe
