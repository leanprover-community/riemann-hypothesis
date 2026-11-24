module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.IsOrthogonalProjectionTwoLines
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

@[expose] public section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ex_rep (d : ℕ) (β : ℝ → ℂ) (v : Eu d) (hβ : Continuous β) (hc : HasCompactSupport β) :
    ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v := by
  have h1 : Continuous fun x => β x • v := hβ.smul continuous_const
  have h2 : HasCompactSupport fun x => β x • v := hc.smul_right (f' := fun _ => v)
  have h3 : MemLp (fun x => β x • v) 2 (volume : Measure ℝ) := h1.memLp_of_hasCompactSupport h2
  exact ⟨h3.toLp _, h3.coeFn_toLp⟩

private theorem orth_zero (d : ℕ) (U : Set ℝ) (hU : IsOpen U) (w : L (Eu d))
    (hw : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ x, x ∉ U → β x = 0) →
      (∀ᵐ x : ℝ, u x = β x • v) → inner ℂ u w = 0) :
    ∀ᵐ x : ℝ, x ∈ U → w x = 0 := by
  have hli : LocallyIntegrable (fun x => w x) (volume : Measure ℝ) :=
    (Lp.memLp w).locallyIntegrable (by norm_num)
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.locallyIntegrableOn U) ?_
  intro g hg hc hs
  have hint : Integrable (fun x => g x • w x) (volume : Measure ℝ) :=
    hli.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  refine ext_inner_left ℂ fun v => ?_
  rw [inner_zero_right, ← integral_inner hint]
  have hβ : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hβc : HasCompactSupport fun x => (g x : ℂ) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  obtain ⟨u, hu⟩ := ex_rep d _ v hβ hβc
  have h0 := hw _ v u hβ hβc (fun x hx => by
    have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    simp [this]) hu
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx, inner_smul_left, Complex.conj_ofReal, ← Complex.coe_smul, inner_smul_right]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc :
    ∀ (d : ℕ), Dense ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧ ∀ᵐ x : ℝ, u x = β x • v} :
        Submodule ℂ (L (Eu d))) : Set (L (Eu d))) ∧
      (∀ (β : ℝ → ℂ) (v : Eu d), Continuous β → HasCompactSupport β → ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v) ∧
      ∀ (s : ℝ) (u : L (Eu d)), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → u ∈ closure ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d),
        Continuous β ∧ HasCompactSupport β ∧ (∀ x, x ≤ s → β x = 0) ∧ ∀ᵐ x : ℝ, u x = β x • v} : Submodule ℂ (L (Eu d))) : Set (L (Eu d))) := by
  intro d
  refine ⟨?_, ex_rep d, ?_⟩
  · rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro w hw
    have h := orth_zero d univ isOpen_univ w fun β v u h1 h2 _ h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span ⟨β, v, h1, h2, h4⟩)
    rw [Submodule.mem_bot]
    refine Lp.ext ?_
    filter_upwards [h, Lp.coeFn_zero (Eu d) 2 (volume : Measure ℝ)] with x hx h0
    rw [hx (mem_univ x), h0]
    rfl
  · intro s u hu
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure, SetLike.mem_coe,
      Submodule.mem_orthogonal]
    intro w hw
    have h := orth_zero d (Ioi s) isOpen_Ioi w fun β v u h1 h2 h3 h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span
        ⟨β, v, h1, h2, fun x hx => h3 x (fun h => not_lt.2 hx h), h4⟩)
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h, hu] with x h1 h2
    rcases le_or_gt x s with hx | hx
    · simp [h2 hx]
    · simp [h1 hx]
