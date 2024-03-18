/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Snoc

1.1 (3 points). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

def snoc {α : Type} : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: snoc xs a

/- 1.2 (1 point). Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

#eval snoc [1] 2
-- invoke `#eval` or `#reduce` here

attribute [simp] snoc in
theorem snoc_eq_append {α : Type} {a : α} :
  ∀ {xs : List α}, snoc xs a = xs ++ [a]
  | [] => by simp only [snoc, List.nil_append]
  | _ :: _ => by simp only [snoc, snoc_eq_append, List.cons_append]


/- ## Question 2 (6 points): Sum

2.1 (3 points). Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs
  -- | xs => xs.foldl (. + .) 0

#eval sum [1, 12, 3]   -- expected: 16

/- 2.2 (3 points). State (without proving them) the following properties of
`sum` as theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

theorem sum_snoc_eq_sum {n} : ∀ {ms}, sum (snoc ms n) = n + sum ms
  | [] => by simp only [sum, add_zero]
  | x :: xs => by simp only [sum, sum_snoc_eq_sum]; omega

theorem sum_concat_eq_sums :
  ∀ {ms ns}, sum (ms ++ ns) = sum ms + sum ns
  | [], _ => by simp only [List.nil_append, sum, zero_add]
  | _, [] => by simp only [List.append_nil, sum, add_zero]
  | m :: ms, n :: ns =>
    by simp only [sum, List.append_eq, sum_concat_eq_sums]; omega

theorem sum_reverse_eq_sum : ∀ {ns}, sum (reverse ns) = sum ns
  | [] => by simp only [sum]
  | n :: ns =>
    calc sum (reverse <| n :: ns)
       = sum (reverse ns ++ [n]) := by rw [reverse]
     _ = sum ns + sum [n] := by rw [sum_concat_eq_sums, sum_reverse_eq_sum]
     _ = sum (n :: ns) := by simp only [sum, add_zero]; omega

end LoVe
