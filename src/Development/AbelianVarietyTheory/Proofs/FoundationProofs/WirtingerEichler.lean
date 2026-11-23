module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerDbar

def P (s : ℂ) (G : ℂ → ℂ) (d : ℂ) : Prop :=
  ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = d

lemma wirtinger_eq_zero_of_hasDerivAt {s : ℂ} {g : ℂ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' s) : P s g 0 := by
  refine ⟨_, hg.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp

lemma wirtinger_sub {s : ℂ} {G H : ℂ → ℂ} {d e : ℂ} (hG : P s G d) (hH : P s H e) :
    P s (fun z => G z - H z) (d - e) := by
  obtain ⟨L, hL, hd⟩ := hG
  obtain ⟨M, hM, he⟩ := hH
  refine ⟨L - M, hL.sub hM, ?_⟩
  simp only [ContinuousLinearMap.sub_apply]
  rw [← hd, ← he]; ring

lemma wirtinger_sum {s : ℂ} {ι : Type} (S : Finset ι) (G : ι → ℂ → ℂ) (d : ι → ℂ)
    (h : ∀ i ∈ S, P s (G i) (d i)) : P s (fun z => ∑ i ∈ S, G i z) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) s, by simp⟩
  | insert a S ha ih =>
    obtain ⟨L, hL, hd⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨M, hM, he⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨L + M, ?_, ?_⟩
    · refine (hL.add hM).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha, ← hd, ← he]; simp only [ContinuousLinearMap.add_apply]; ring

lemma wirtinger_conj_mul_pow {s : ℂ} {b : ℂ → ℂ} {b' : ℂ} (hb : HasDerivAt b b' s) (j : ℕ) :
    P s (fun z => starRingEnd ℂ (b z) * z ^ j) (-2 * Complex.I * s ^ j * starRingEnd ℂ b') := by
  have h1 : HasFDerivAt (fun z => starRingEnd ℂ (b z))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) b').restrictScalars ℝ)) s :=
    Complex.conjCLE.hasFDerivAt.comp s (hb.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun z : ℂ => z ^ j)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((j : ℂ) * s ^ (j - 1))).restrictScalars ℝ) s :=
    ((hasDerivAt_pow j s).hasFDerivAt.restrictScalars ℝ)
  refine ⟨_, h1.mul h2, ?_⟩
  simp
  ring

theorem wirtinger_eichler : ∀ (w : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → ∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun z : ℂ => (eichler w f (ofComplex z) - (eichler w h (ofComplex z)).map (starRingEnd ℂ) - p).eval z) L s ∧
      L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s)) := by
  intro w f h p hf hh s hs
  have he : ∀ (g : ℍ → ℂ) (z : ℂ), 0 < z.im → eichler w g (ofComplex z) =
      ∑ j ∈ Finset.range (w + 1), C ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w g j z) * X ^ j := by
    intro g z hz
    rw [ofComplex_apply_of_im_pos hz]
    rfl
  have hF : P s (fun z => ∑ j ∈ Finset.range (w + 1), (w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w f j z * z ^ j)
      (∑ j ∈ Finset.range (w + 1), (0 : ℂ)) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_eq_zero_of_hasDerivAt
      (((GlobalTheory.EichlerChange.hasDerivAt_ecoef w f hf j s hs).const_mul _).mul (hasDerivAt_pow j s))
  have hH : P s (fun z => ∑ j ∈ Finset.range (w + 1), starRingEnd ℂ ((w.choose j : ℂ) * GlobalTheory.EichlerChange.ecoef w h j z) * z ^ j)
      (∑ j ∈ Finset.range (w + 1), -2 * Complex.I * s ^ j *
        starRingEnd ℂ ((w.choose j : ℂ) * ((h ∘ ofComplex) s * (-s) ^ (w - j)))) :=
    wirtinger_sum _ _ _ fun j _ => wirtinger_conj_mul_pow ((GlobalTheory.EichlerChange.hasDerivAt_ecoef w h hh j s hs).const_mul _) j
  obtain ⟨L, hL, hd⟩ := wirtinger_sub (wirtinger_sub hF hH) (wirtinger_eq_zero_of_hasDerivAt (Polynomial.hasDerivAt p s))
  refine ⟨L, hL.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hs] with z hz
    rw [he f z hz, he h z hz]

    simp [Polynomial.map_sum, eval_finsetSum]
  · rw [hd]
    have hb : (s - (starRingEnd ℂ) s) ^ w = ∑ j ∈ Finset.range (w + 1),
        s ^ j * (-(starRingEnd ℂ) s) ^ (w - j) * (w.choose j : ℂ) := by
      rw [sub_eq_add_neg, add_pow]
    rw [hb, Finset.mul_sum, Finset.sum_mul, Finset.sum_const_zero]
    simp only [zero_sub, sub_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_mul, map_natCast, map_pow, map_neg]
    ring

end GlobalTheory.EichlerDbar
