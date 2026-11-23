module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  first | exact @GlobalTheory.RSCellB.bInt_continuous_invariant_finite | exact GlobalTheory.RSCellB.bInt_continuous_invariant_finite | (intros; apply GlobalTheory.RSCellB.bInt_continuous_invariant_finite <;> assumption)
