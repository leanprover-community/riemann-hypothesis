module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField IsDedekindDomain
open GlobalTheory.AutomorphicL2Unitary (conv)

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsFullLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
  {μ : Measure (GAd σ J)} {fa fa' : ∀ w, GArch σ J w → ℂ} {ff ff' : ∀ v, GLoc σ J v → ℂ}


omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem unitLoc_mul_translate {v : HeightOneSpectrum (𝓞 F)} {y : GLoc σ J v} (hy : y ∈ stabLoc σ J L v) :
    (fun x => unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y)) = unitLoc σ J L v := by
  funext x
  by_cases hx : x ∈ stabLoc σ J L v
  · simp [unitLoc, hx, mul_mem (inv_mem hx) hy]
  · simp [unitLoc, hx]

theorem conv_unitLoc {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (GLoc σ J v)) :
    conv ν (unitLoc σ J L v) (unitLoc σ J L v) = (ν.real (stabLoc σ J L v) : ℂ) • unitLoc σ J L v := by
  funext y
  by_cases hy : y ∈ stabLoc σ J L v
  · rw [conv, unitLoc_mul_translate hy, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Pi.smul_apply, indicator_of_mem hy, Complex.real_smul]
    rfl
  · have : ∀ x, unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ stabLoc σ J L v
      · simp [unitLoc, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
      · simp [unitLoc, hx]
    rw [conv]
    simp only [this, integral_zero]
    simp [unitLoc, hy]

theorem IsFinFamily.conv (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff')
    (h1 : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) : IsFinFamily σ J L fun v => conv (μf v) (ff v) (ff' v) := by
  refine ⟨fun v => conv_mem_SB (hf.1 v) (hf'.1 v), ?_⟩
  filter_upwards [hf.2, hf'.2, h1] with v e e' e1
  rw [e, e', conv_unitLoc, Measure.real, e1]
  simp

theorem IsFinFamily.mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    IsFinFamily σ J L fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  refine ⟨fun v => ⟨(hf.1 v).1.mul ((hf'.1 v).1.comp_continuous (by fun_prop)), (hf.1 v).2.mul_right⟩, ?_⟩
  filter_upwards [hf.2, hf'.2, eventually_proj_mem_stabLoc σ J L y] with v e e' hy
  rw [e, e', unitLoc_mul_translate hy]

end GlobalTheory.Orb
