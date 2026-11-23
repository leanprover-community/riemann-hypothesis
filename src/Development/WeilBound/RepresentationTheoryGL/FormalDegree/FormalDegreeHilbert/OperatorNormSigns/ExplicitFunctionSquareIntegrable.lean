module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.ExplicitFunctionSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.ExplicitFunctionSquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pl_opNorm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : ‖A‖ ^ 2 ≤ (Module.finrank ℂ V : ℝ) * hsOp A := by
  apply CompanionTheory.RgFd.pl_opNorm_le <;> assumption

theorem square_integrable_of_norm : PsiNorm → PositivityTheory.RgDs.ExplicitFunctionSquareIntegrable := by
  intro hN n ε lam T μ hl hμ ν hν
  have hfin := hN n ε lam hl T μ hμ
  haveI : (show Measure (UJ ε) from muCD ε).IsHaarMeasure := muCD_isHaar ε
  set f : UJ ε → (T.V →L[ℂ] T.V) := fun g => PsiM T μ (toM g) with hf
  have hcont : Continuous f :=
    (psiM_continuousOn T μ hμ).comp_continuous (continuous_toM ε) (fun g => g.2)
  have hmCD : MemLp f 2 (muCD ε) := by
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ g : Formalism.REAL.UJ ε, ‖‖f g‖ ^ 2‖ₑ ≤
        ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) * ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) := by
      intro g
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.eNorm_eq_ofReal (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pl_opNorm_le _)
    calc ∫⁻ g, ‖‖f g‖ ^ 2‖ₑ ∂(muCD ε) ≤ ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) := lintegral_mono hle
      _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := by rw [hfin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have heq := Measure.isMulLeftInvariant_eq_smul ν (show Measure (UJ ε) from muCD ε)
  rw [heq]
  exact hmCD.smul_measure_nnreal

end PositivityTheory.RgFd
