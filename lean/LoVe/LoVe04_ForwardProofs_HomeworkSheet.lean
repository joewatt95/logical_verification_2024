/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet
import LoVe.LoVe03_BackwardProofs_HomeworkSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term {a b} :
  ¬ a ∨ b → a → b
  | .inl h_not_a, h_a => h_a |> h_not_a |>.elim
  | .inr h_b, _ => h_b

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct {a b} :
  ¬ a ∨ b → a → b :=
  assume h_not_a_or_b : ¬ a ∨ b;
  assume h_a : a;
    match h_not_a_or_b with
    | .inl h_not_a =>
      have : ⊥ := h_not_a h_a
      show b from this.elim
    | .inr h_b => show b from h_b

/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α} {p q : α → Prop} :
  (∀ {x}, p x ∨ q x) ↔ (∀ {x}, q x ∨ p x)
  where
    mp h_forall_p_or_q := match h_forall_p_or_q with
      | .inl h_p => .inr h_p
      | .inr h_q => .inl h_q

    mpr h_forall_q_or_p := match h_forall_q_or_p with
      | .inl h_q => .inr h_q
      | .inr h_p => .inl h_p

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

-- theorem Peirce_of_DN :
--   DoubleNegation → Peirce :=
--   sorry

-- theorem EM_of_Peirce :
--   Peirce → ExcludedMiddle :=
--   sorry

-- theorem dn_of_em :
--   ExcludedMiddle → DoubleNegation :=
--   sorry

end BackwardProofs

end LoVe
