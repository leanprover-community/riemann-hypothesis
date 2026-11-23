module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormAinfDiscStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDomainClosedDiscGaugeCompletionOfEquivNormStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem discAinf_isDomain : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    IsDomain (bk.DA ρ) ∧ (∀ x y : bk.DA ρ, (ρ : ℝ) ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ∧
      ∀ a : bk.DA ρ, a ≠ 0 → ∃ C : ℝ, ∀ y, ‖y‖ ≤ C * ‖a * y‖ := by
  intro l _ K bk ρ h0 h1
  obtain ⟨N, hmul, hadd, hl, hle, hge⟩ := GlobalTheory.T.exists_gaussNorm_ainf_disc l K bk ρ h0 h1
  have hρ : (0 : ℝ) < (ρ : ℝ) := h0
  obtain ⟨hdom, hnorm⟩ := GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm l (Ainf l) (bk.ev X) ρ N (ρ : ℝ) hρ hmul hadd hl hle hge
  refine ⟨hdom, hnorm, fun a ha => ⟨((ρ : ℝ) ^ 2 * ‖a‖)⁻¹, fun y => ?_⟩⟩
  have hpos : 0 < (ρ : ℝ) ^ 2 * ‖a‖ := mul_pos (pow_pos hρ 2) (norm_pos_iff.2 ha)
  have h := hnorm a y
  rw [← mul_assoc] at h
  calc ‖y‖ = ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ((ρ : ℝ) ^ 2 * ‖a‖ * ‖y‖) := by field_simp
    _ ≤ ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ‖a * y‖ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hpos.le)

end GlobalTheory.BSP
