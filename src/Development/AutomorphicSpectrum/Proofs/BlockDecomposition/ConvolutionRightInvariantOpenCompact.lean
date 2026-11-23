module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_finGL_inv_mul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (u : GL (Fin a) (Af E)) (hu : u ∈ U)
    (y : GA E a) : tst U β ((finGL E a u)⁻¹ * y) = tst U β y := by
  have hinv : ((finGL E a u)⁻¹ * y)⁻¹ = y⁻¹ * finGL E a u := by
    rw [_root_.mul_inv_rev, inv_inv]
  have hfin : GeneralLinearGroup.map (pFin E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pFin E) y⁻¹ * u := by
    rw [map_mul, pFin_finGL]
  have hinf : GeneralLinearGroup.map (pInf E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pInf E) y⁻¹ := by
    rw [map_mul, pInf_finGL, mul_one]
  unfold tst ker
  rw [hinv, hfin, hinf]
  by_cases hm : GeneralLinearGroup.map (pFin E) y⁻¹ ∈ U
  · rw [if_pos (U.mul_mem hm hu), if_pos hm]
  · rw [if_neg (fun h => hm (by simpa using U.mul_mem h (U.inv_mem hu))), if_neg hm]

theorem convR_tst_mul_finGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ)
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (x : GA E a) :
    convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  unfold convR
  have h := integral_mul_left_eq_self (μ := μ)
    (fun y => tst U β ((finGL E a u)⁻¹ * y) * Fl (x * y)) (finGL E a u)
  simp only [inv_mul_cancel_left] at h
  simp only [tst_finGL_inv_mul U β u hu] at h
  simpa only [mul_assoc] using h

theorem convR_tst_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  intro E _ _ _ a μ _ _ U β Fl u hu x
  exact convR_tst_mul_finGL E a μ U β Fl u hu x

end GlobalTheory.CompanionTheory.SmoothRep
