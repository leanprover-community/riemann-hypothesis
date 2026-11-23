module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tspDiag_of :
    UpperTheory.Gal.W2.TspDiag := by
  intro F _ _ g ty t₀ i₀ hc hi hij W hW
  classical
  have hpat : ∀ S : Matrix (Fin g) (Fin g) ℂ, S ∈ W → ∀ i j, S i j ≠ 0 →
      ty j = ComplexEmbedding.conjugate (ty i) := by
    intro S hS i j hne
    have h := ((hW S).1 hS).2
    have hcc : ∀ c : 𝓞 F, ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := fun c =>
      mul_left_cancel₀ hne (by rw [h c i j, mul_comm])
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) ?_
    ext c
    simpa [ComplexEmbedding.conjugate_coe_eq] using hcc c
  have hi₀ : ty i₀ = t₀ := (hi i₀).2 rfl
  have hnot : ∀ j, ty j = ComplexEmbedding.conjugate t₀ → j ≠ i₀ := by
    rintro j hj rfl
    exact hc (by rw [← hj, hi₀])
  constructor
  · intro S S' hSS
    apply Subtype.ext
    have hzero : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, i ≠ i₀ → j ≠ i₀ → T i j = 0 := by
      intro T hT i j hi' hj'
      by_contra hne
      rcases hij i j (hpat T hT i j hne) with h | h
      · exact hi' h
      · exact hj' h
    have hrow : ∀ j, S.1 i₀ j = S'.1 i₀ j := by
      intro j
      by_cases hj : ty j = ComplexEmbedding.conjugate t₀
      · exact congrFun hSS ⟨j, hj⟩
      · have hz : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → T i₀ j = 0 := by
          intro T hT
          by_contra hne
          exact hj (by rw [hpat T hT i₀ j hne, hi₀])
        rw [hz _ S.2, hz _ S'.2]
    have hsym : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, T i j = T j i := by
      intro T hT i j
      have h := congrFun (congrFun ((hW T).1 hT).1 i) j
      rw [Matrix.transpose_apply] at h
      exact h.symm
    ext i j
    by_cases h1 : i = i₀
    · subst h1; exact hrow j
    · by_cases h2 : j = i₀
      · subst h2
        rw [hsym _ S.2, hsym _ S'.2]; exact hrow i
      · rw [hzero _ S.2 i j h1 h2, hzero _ S'.2 i j h1 h2]
  · intro v
    let T : Matrix (Fin g) (Fin g) ℂ := fun i j =>
      if h : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀ then v ⟨j, h.2⟩
      else if h' : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀ then v ⟨i, h'.2⟩ else 0
    have hT : T ∈ W := by
      refine (hW T).2 ⟨?_, ?_⟩
      · ext i j
        show T j i = T i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · have h2 : ¬ (j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀) := fun h => hnot j h1.2 h.1
          simp only [T, dif_pos h1, dif_neg h2]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_pos h2, dif_neg h1]
          · simp only [T, dif_neg h1, dif_neg h2]
      · intro c i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · simp only [T, dif_pos h1]
          have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
            rw [h1.2, h1.1, hi₀, ComplexEmbedding.conjugate_coe_eq]
          rw [e, mul_comm]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_neg h1, dif_pos h2]
            have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
              rw [h2.2, h2.1, hi₀, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
            rw [e, mul_comm]
          · simp only [T, dif_neg h1, dif_neg h2]
            simp
    refine ⟨⟨T, hT⟩, ?_⟩
    funext j
    show T i₀ j.1 = v j
    have h1 : i₀ = i₀ ∧ ty j.1 = ComplexEmbedding.conjugate t₀ := ⟨rfl, j.2⟩
    simp only [T, dif_pos h1]
