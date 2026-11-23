module

public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.StatementN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
