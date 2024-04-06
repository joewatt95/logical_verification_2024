/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo
import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
  a → a := by
  intro ha
  apply ha

theorem K (a b : Prop) :
  a → b → b := by
  intro _ha hb
  apply hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c := by
  intro h_c_of_a_b hb ha
  apply h_c_of_a_b
  apply ha
  apply hb

theorem proj_fst (a : Prop) :
  a → a → a := by
  intro ha _ha
  apply ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a := by
  intro _ha ha
  apply ha

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c := by
  intro _h_c_of_a_b ha h_c_of_a _hb
  apply h_c_of_a
  apply ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive {a b : Prop} :
  (a → b) → ¬ b → ¬ a := by
  intro h_b_of_a h_not_b h_a
  apply h_not_b
  apply h_b_of_a
  exact h_a

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) := by
  apply Iff.intro
  . intro (h : ∀ x, p x ∧ q x)
    apply And.intro
    . intro x
      have ⟨(h_px : p x), _⟩ := h x
      exact h_px
    . intro x
      have ⟨_, (h_qx : q x)⟩ := h x
      exact h_qx
  . intro ⟨(h_px : ∀ x, p x), (h_qx : ∀ x, q x)⟩ x
    apply And.intro
    . exact h_px x
    . exact h_qx x

/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero : ∀ {n}, mul 0 n = 0 := SorryTheorems.zero_mul

#check add_succ
theorem mul_succ {m n} :
  mul (.succ m) n = add (mul m n) n :=
  by simp only [SorryTheorems.succ_mul, SorryTheorems.add_comm]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) : mul m n = mul n m := SorryTheorems.mul_comm

theorem mul_assoc (l m n : ℕ) : mul (mul l m) n = mul l (mul m n) :=
  SorryTheorems.mul_assoc

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
  by simp only [SorryTheorems.mul_add, mul_comm]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

abbrev ExcludedMiddle : Prop :=
  ∀ {a : Prop}, a ∨ ¬ a

abbrev Peirce : Prop :=
  ∀ {a b : Prop}, ((a → b) → a) → a

abbrev DoubleNegation : Prop :=
  ∀ {a : Prop}, ¬¬ a → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM : ExcludedMiddle → Peirce
  | (h_em : ∀ {φ}, φ ∨ ¬ φ), φ, ψ, (h : (φ → ψ) → φ) =>
    match h_em with
    | .inl h_φ => h_φ
    | .inr h_not_φ =>
      suffices φ → ψ from h this
      λ h_φ ↦
        have : ⊥ := h_not_φ h_φ
        this.elim

/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation
  | (h_peirce : ∀ {φ ψ}, ((φ → ψ) → φ) → φ), φ, (h_not_not_φ : ¬¬φ) =>
  suffices (φ → ⊥) → φ from h_peirce this
  λ h_not_φ : ¬ φ ↦
    have : ⊥ := h_not_not_φ h_not_φ
    this.elim

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

lemma not_and_not_of_not_or {φ ψ} (h_not_φ_or_ψ : ¬ (φ ∨ ψ)) : ¬ φ ∧ ¬ ψ
  where
    left := (. |> .inl |> h_not_φ_or_ψ)
    right := (. |> .inr |> h_not_φ_or_ψ)

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle
  | (h_dne : ∀ {φ}, ¬¬φ → φ), φ =>
  suffices ¬¬ (φ ∨ ¬ φ) from h_dne this
  λ h : ¬ (φ ∨ ¬ φ) ↦
    have ⟨h_not_φ, h_not_not_φ⟩ : ¬ φ ∧ ¬ ¬ φ := not_and_not_of_not_or h
    h_not_φ |> h_not_not_φ |>.elim

end SorryTheorems

end BackwardProofs

end LoVe
