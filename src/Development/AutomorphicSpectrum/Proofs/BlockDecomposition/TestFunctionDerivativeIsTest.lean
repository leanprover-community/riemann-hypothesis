module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

theorem isTest_dTest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
