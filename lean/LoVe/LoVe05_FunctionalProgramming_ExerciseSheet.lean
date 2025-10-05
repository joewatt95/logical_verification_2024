/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Exercise 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

theorem reverseAccu_eq_reverse_append {α} :
  ∀ {as xs : List α}, reverseAccu as xs = reverse xs ++ as
  | _, [] => rfl
  | _, _ :: _ =>
    by simp only [
      reverseAccu,
      reverseAccu_eq_reverse_append,
      reverse,
      List.append_assoc,
      List.singleton_append
    ]

/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α} {xs : List α} :
  reverseAccu [] xs = reverse xs := by
  simp only [reverseAccu_eq_reverse_append, List.append_nil]

/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
  reverseAccu [] (reverseAccu [] xs) = xs := by
  simp only [reverseAccu_eq_reverse, SorryTheorems.reverse_reverse]

/- 1.4. Prove the following theorem by structural induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how
structural induction works (and is good practice for the final exam).

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the induction hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `rfl` or `simp` need not be
justified if you think they are obvious (to humans), but you should say which
key theorems they depend on. You should be explicit whenever you use a function
definition. -/

-- enter your paper proof here


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α} : ℕ → List α → List α
  | 0, xs => xs
  | _, [] => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. Define the `take` function, which returns a list consisting of the first
`n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α} : ℕ → List α → List α
  | _, [] => []
  | 0, _ => []
  | n + 1, x :: xs => x :: take n xs

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α} :
  ∀ {n}, drop n ([] : List α) = []
  | 0 | _ + 1 => rfl

@[simp] theorem take_nil {α} :
  ∀ {n}, take n ([] : List α) = []
  | 0 | _ + 1 => rfl

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

theorem drop_drop {α} :
  ∀ {m n} {xs : List α}, drop n (drop m xs) = drop (n + m) xs
  | 0, _, _ => by simp only [drop, add_zero]
  | _, _, [] => by simp only [drop_nil]
  | _ + 1, _, _ :: _ => by simp only [drop, Nat.add_eq, drop_drop]

theorem take_take {α} :
  ∀ {m} {xs : List α}, take m (take m xs) = take m xs
  | _ , [] => by simp only [take_nil]
  | 0, _ :: _ => by simp only [take]
  | _ + 1, _ :: _ => by simp only [take, take_take]

theorem take_drop {α} :
  ∀ {n} {xs : List α}, take n xs ++ drop n xs = xs
  | 0, _ => by simp only [drop, List.append_left_eq_self]; unfold take; aesop
  | _ + 1, [] => by simp only [take_nil, drop_nil, List.append_nil]
  | _ + 1, _ :: _ => by simp only [take, drop, List.cons_append, take_drop]


/- ## Question 3: A Type of Terms

3.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

-- enter your definition here
inductive Term
  | var (var : String)
  | lam (var : String) (body : Term)
  | app (fn : Term) (arg : Term)
  deriving Repr

/- 3.2 (**optional**). Register a textual representation of the type `term` as
an instance of the `Repr` type class. Make sure to supply enough parentheses to
guarantee that the output is unambiguous. -/

-- def Term.repr : Term → String
-- enter your answer here

-- instance Term.Repr : Repr Term :=
--   { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 (**optional**). Test your textual representation. The following command
should print something like `(λx. ((y x) x))`. -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
