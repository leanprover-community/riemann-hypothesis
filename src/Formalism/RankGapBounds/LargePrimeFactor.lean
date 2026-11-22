module

public import Mathlib

@[expose] public section

open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

namespace Data

end Data

def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)

end

end Formalism.RankGapBounds.ChebyshevFactorialBounds
