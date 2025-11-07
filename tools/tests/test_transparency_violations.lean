/-
Test file with deliberate transparency violations.
This file should FAIL the transparency check.
-/

-- Violation 1: Trivial abuse - theorem proves True but name suggests content
theorem interval_injective : True := trivial

-- Violation 2: Placeholder definition
def IsStandard (x : Nat) : Prop := True

-- Violation 3: Another placeholder
instance : Decidable (IsStandard 42) := by
  unfold IsStandard
  exact instDecidableTrue

-- Violation 4: Custom axiom
axiom myCustomAxiom : ∀ n : Nat, n = n + 1

-- Violation 5: Admitted proof
theorem bad_theorem : 2 + 2 = 5 := by
  admit

-- Violation 6: Unsafe definition
unsafe def dangerousFunction : Nat := 42

-- This is OK - legitimate sorry (not a violation, just incomplete)
theorem work_in_progress : ∀ n : Nat, n + 0 = n := by
  sorry
