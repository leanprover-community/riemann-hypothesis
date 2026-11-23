module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_coefOn_of {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ)
    (v w : H) : Continuous (coefOn (ε := ε) σ v w) := by
  have h1 : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
    (hU.2.2 v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun g => g.2)
  exact continuous_const.inner h1

theorem integral_coefOn_sq_pos {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ)
    {w : H} (hw : w ≠ 0) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsOpenPosMeasure)
    (hI : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) μ) :
    0 < ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ := by
  have hc : Continuous (coefOn (ε := ε) σ w w) := continuous_coefOn_of hU w w
  have hf : Continuous fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2 := (continuous_norm.comp hc).pow 2
  have h1 : coefOn (ε := ε) σ w w 1 = ⟪w, w⟫_ℂ := by
    show ⟪w, σ (umat (1 : Formalism.REAL.UJ ε)) w⟫_ℂ = ⟪w, w⟫_ℂ
    have hu : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
    rw [hu, hU.1.1, ContinuousLinearMap.one_apply]
  have hne : (1 : Formalism.REAL.UJ ε) ∈ Function.support fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2 := by
    rw [Function.mem_support]
    show ‖coefOn (ε := ε) σ w w 1‖ ^ 2 ≠ 0
    rw [h1]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))
  have hopen : IsOpen (Function.support fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) :=
    isOpen_ne_fun hf continuous_const
  rw [integral_pos_iff_support_of_nonneg (fun g => sq_nonneg _) hI]
  exact hopen.measure_pos μ ⟨1, hne⟩

theorem fdegOf_pos_of {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ)
    {w : H} (hw : w ≠ 0) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsOpenPosMeasure)
    (hI : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) μ) : 0 < fdegOf μ σ w :=
  div_pos (pow_pos (norm_pos_iff.2 hw) 4) (integral_coefOn_sq_pos hU hw μ hμ hI)

end Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.MassDataX

theorem dvPosC_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (v : NumberField.InfinitePlace X.B.I.F) : 0 < X.dv v := by
  have hw : X.B.w v ≠ 0 := by
    intro h
    have h1 := (X.low v).1
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hμ : (Formalism.REAL.muG (X.B.I.ε v)).IsOpenPosMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  exact Formalism.MainNotions.S.fdegOf_pos_of (X.ds v).2.2.1 hw _ hμ
    ((X.ds v).2.2.2.2.1 (X.B.w v) (X.B.w v)).norm.integrable_sq

end Formalism.L2.SG.Pf.MassDataX
