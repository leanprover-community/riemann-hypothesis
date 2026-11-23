module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairBaseOfLag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PlaneIsUnitOfSubOneMem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open Matrix

namespace PI.SqPair.LCP

theorem base_lagrangian : BaseLag := by
  intro R _ _ R₀ _ _ ϖ hI κ _ _ hev A hA
  obtain ⟨θ, hθ⟩ := hI.unr
  exact PI.LocCartanPair.lag_exists hI.fix hθ hev A hA.1 hA.2

theorem hyperbolic_plane : Plane := by
  intro R _ _ R₀ _ ϖ hI α β hα
  obtain ⟨θ, hθ⟩ := hI.unr
  have hσ : ∀ x : R, (starRingAut : R ≃+* R) ((starRingAut : R ≃+* R) x) = x := fun x => by
    simp [starRingAut_apply]
  have hR₀ : ∀ x, x ∈ R₀ ↔ (starRingAut : R ≃+* R) x = x := fun x => by
    rw [starRingAut_apply]
    exact hI.fix x
  have hθ' : IsUnit (θ - (starRingAut : R ≃+* R) θ) := by
    rw [starRingAut_apply]
    exact hθ
  obtain ⟨τ, hτ⟩ := tau_of_theta (starRingAut : R ≃+* R) hσ θ hθ'
  obtain ⟨w, hw1, hw2, hw3⟩ := plane_w (starRingAut : R ≃+* R) hσ R₀ hR₀ τ hτ α β hα
  refine ⟨w, hw1, ?_, hw3⟩
  have hct : wᴴ = (w.map (starRingAut : R ≃+* R))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, starRingAut_apply]
  rw [hct, hw2]
  rfl

end PI.SqPair.LCP
