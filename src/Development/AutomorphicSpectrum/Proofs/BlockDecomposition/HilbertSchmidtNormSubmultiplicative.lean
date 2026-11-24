module

public import Formalism.RealPlaceAnalysis.Complexify
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe

theorem hs_mul_le_mul {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  have key : ∀ i j, ‖(P * Q) i j‖ ^ 2 ≤ (∑ k, ‖P i k‖ ^ 2) * (∑ k, ‖Q k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(P * Q) i j‖ ≤ ∑ k, ‖P i k‖ * ‖Q k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hQ : Formalism.REAL.hs Q = ∑ j, ∑ k, ‖Q k j‖ ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_comm
  rw [hQ]
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j

end GlobalTheory.CompanionTheory.RgHe
