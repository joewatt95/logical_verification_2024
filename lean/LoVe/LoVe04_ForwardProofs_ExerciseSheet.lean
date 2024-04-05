/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) : a → a := id

theorem K (a b : Prop) : a → b → b
  | _, h_b => h_b

theorem C {a b c : Prop} : (a → b → c) → b → a → c
  | h, h_b, h_a => h h_a h_b

theorem proj_fst (a : Prop) : a → a → a
  | h_a, _ => h_a

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) : a → a → a
  | _, h_a => h_a

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c
  | _h_c_of_b_a, h_a, h_c_of_a, _h_b => h_c_of_a h_a

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a
  | h_b_of_a, h_not_b, h_a =>
  have : b := h_b_of_a h_a
  show ⊥ from h_not_b this

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀ {x}, p x ∧ q x) ↔ (∀ {x}, p x) ∧ (∀ {x}, q x)
  where
    mp h_px_and_qx :=
      have h_px {x} : p x := h_px_and_qx.left
      have h_qx {x} : q x := h_px_and_qx.right
      ⟨h_px, h_qx⟩
    mpr h :=
      have ⟨h_px, h_qx⟩ := h
      ⟨h_px, h_qx⟩

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α} {p : α → α → Prop} :
  (∃ x, ∀ {y}, p x y) → ∀ {y}, ∃ x, p x y
  | ⟨x, h⟩, _y => ⟨x, h⟩


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square {a b : ℕ} :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b := calc
    (a + b) * (a + b)
-- = a * (a + b) + b * (a + b) := by ring
_ = a * a + 2 * a * b + b * b := by ring

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α} {t : α} {P : α → Prop} :
  (∀ {x}, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  ⊥ :=
  sorry

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α} (t : α) (P : α → Prop) :
  (∃ x, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  ⊥ :=
  sorry

end LoVe
