/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE


/- # LoVe Homework 3 (10 points): Backward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (5 points): Connectives and Quantifiers

1.1 (4 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem B (a b c : Prop) :
  (a → b) → (c → a) → c → b := by
  intro h_b_of_a h_c_of_a h_c
  apply h_b_of_a
  apply h_c_of_a
  exact h_c

theorem S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c := by
  intro h_c_of_b_a h_b_of_a h_a
  apply h_c_of_b_a
  . exact h_a
  . apply h_b_of_a at h_a
    exact h_a

theorem more_nonsense (a b c d : Prop) :
  ((a → b) → c → d) → c → b → d := by
  intro h h_c h_b
  apply h
  . intro _h_a
    exact h_b
  . exact h_c

theorem even_more_nonsense (a b c : Prop) :
  (a → b) → (a → c) → a → b → c := by
  intro _h_b_of_a h_c_of_a h_a _h_b
  apply h_c_of_a
  exact h_a

/- 1.2 (1 point). Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b := by
  intro h
  apply h
  intro h'
  apply h'
  intro h_a
  apply h
  intro _h
  exact h_a


/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about double negation using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `False` at a key point in the
  proof. -/

theorem herman {a} : ¬ ¬ (¬ ¬ a → a) :=
  suffices ¬ ¬ (a ∨ ¬ a) from this |> not_not_implies dne_of_lem
  λ h : ¬ (a ∨ ¬ a) ↦
    have ⟨(h_not_a : ¬ a), (h_not_not_a : ¬ ¬ a)⟩ :=
      SorryTheorems.not_and_not_of_not_or h
    show ⊥ from h_not_not_a h_not_a
  where
    dne_of_lem {a} : (a ∨ ¬ a) → ¬ ¬ a → a
      | .inl h_a, _ => h_a
      | .inr h_not_a, h_not_not_a =>
        have : ⊥ := h_not_not_a h_not_a
        this.elim

    not_not_implies {a b} : (a → b) → ¬ ¬ a → ¬ ¬ b
      | h_b_of_a, h_not_not_a, h_not_b =>
        have : ¬ b → ¬ a := contrapositive h_b_of_a
        have : ¬ a := this h_not_b
        show ⊥ from h_not_not_a this

/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw DoubleNegation` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN : DoubleNegation → ExcludedMiddle := SorryTheorems.EM_of_DN

/- 2.3 (2 points). We have proved three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

-- enter your solution here

theorem tfae_classical_axioms :
  List.TFAE [ExcludedMiddle, Peirce, DoubleNegation] := by
  tfae_have 1 → 2 := Peirce_of_EM
  tfae_have 2 → 3 := DN_of_Peirce
  tfae_have 3 → 1 := EM_of_DN
  tfae_finish

macro "get_tfae_classical_axioms" "(" index₀:term "," index₁:term ")" : term =>
  `(tfae_classical_axioms
    |> (List.TFAE.out . $index₀ $index₁)
    |>.mp)

theorem EM_of_Peirce : Peirce → ExcludedMiddle :=
  get_tfae_classical_axioms(1, 0)

theorem Peirce_of_DN : DoubleNegation → Peirce :=
  get_tfae_classical_axioms(2, 1)

theorem DN_of_EM : ExcludedMiddle → DoubleNegation :=
  get_tfae_classical_axioms(0, 2)

end BackwardProofs

end LoVe
