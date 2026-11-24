module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
