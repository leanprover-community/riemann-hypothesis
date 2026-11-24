module

public import Formalism.WindowSums.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.WindowSums

open Polynomial

theorem annihilatorPoly_kills : KillerKills := by
  intro ℓ _ c ell JJ V _ _ T
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, hx⟩
    have hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      unfold PP
      rw [← Finset.mul_prod_erase _ _ hi]
      ring
    have hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0 := by
      simp [hx]
    rw [hsplit, map_mul, Module.End.mul_apply, hk, map_zero]
  · intro v hv
    have hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k)
        (T v - v) = 0 := by
      have h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v := by simp
      rw [h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]
      simp [hv]
    unfold PP
    rw [map_mul, Module.End.mul_apply, hS, map_zero]

end Formalism.WindowSums
