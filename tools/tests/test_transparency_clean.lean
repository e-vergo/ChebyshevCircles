/-
Test file with no transparency violations.
This file should PASS the transparency check.
-/

-- OK: Legitimate theorem with real content
theorem nat_add_zero : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

-- OK: Another legitimate theorem
theorem nat_zero_add : ∀ n : Nat, 0 + n = n := by
  intro n
  rfl

-- OK: Legitimate sorry (incomplete work, not a violation)
theorem nat_add_comm : ∀ n m : Nat, n + m = m + n := by
  sorry

-- OK: Trivial tactic used legitimately (proving actually trivial proposition)
theorem true_is_true : True := trivial

-- OK: Real definition (not a placeholder)
def IsEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

-- OK: Instance based on real definition
instance : Decidable (IsEven 4) := by
  unfold IsEven
  decide

-- OK: Lemma with proof
lemma even_four : IsEven 4 := by
  unfold IsEven
  use 2
  rfl
