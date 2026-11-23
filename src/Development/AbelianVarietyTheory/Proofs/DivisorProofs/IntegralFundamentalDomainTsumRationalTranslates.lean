module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaUnfoldInt

theorem integral_fundamentalDomain_tsum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ 𝓕₁ h𝓕 hfin h hc hB
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := hB
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (GlobalTheory.ThetaUnfold.ratEquiv F κ)
  have hcont : ∀ η : κ → F, Continuous fun x => h ((fun i => algebraMap F (AF F) (η i)) + x) :=
    fun η => hc.comp (continuous_const.add continuous_id)
  have hreidx : ∀ f : (κ → AF F) → ENNReal,
      ∫⁻ x, f x ∂μ = ∑' η : κ → F, ∫⁻ x in 𝓕₁, f ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ := by
    intro f
    rw [h𝓕.lintegral_eq_tsum' f, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
    rfl
  have hpt : ∀ x, ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ≤ ENNReal.ofReal B := by
    intro x
    obtain ⟨hs, hle⟩ := hB x
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hle
  have hfinite : ∑' η : κ → F, ∫⁻ x in 𝓕₁, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun η => (hcont η).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hint : Integrable h μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖h a‖ₑ ∂μ < ⊤
    rw [hreidx fun a => ‖h a‖ₑ]
    exact hfinite.lt_top
  rw [integral_tsum (fun η => (hcont η).aestronglyMeasurable) hfinite,
    h𝓕.integral_eq_tsum' h hint, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl

end GlobalTheory.ThetaUnfoldInt

end
