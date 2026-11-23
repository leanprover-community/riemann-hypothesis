module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveEmbedOrbit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

namespace CurveEmbedOrbit

theorem sameOrbit_refl {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : SameOrbit w z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z w u : (Σ k, ι k) → ℂ} (h1 : SameOrbit z w)
    (h2 : SameOrbit w u) : SameOrbit z u := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun p => by simp only; ring⟩

theorem eq_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} (hB : Birational y) {σ τ : Ω →+* ℂ}
    (hst : SameOrbit (fun p => σ (y p)) (fun p => τ (y p))) : σ = τ := by
  obtain ⟨c, hc, hcy⟩ := hst
  ext s
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
  have key : ∀ ρ : Ω →+* ℂ, ρ s * eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) h) =
      eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) g) := fun ρ => by
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp, hgs, map_mul]
  have e1 := key σ
  have e2 := key τ
  rw [hcy, CurveOrbit.eval_smul _ _ hh, CurveOrbit.eval_smul _ _ hg] at e1
  have hE : eval (fun p => τ (y p)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    rw [CurveOrbit.eval_comp]
    exact (map_ne_zero τ).mpr hh0
  have hC : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  apply mul_right_cancel₀ (mul_ne_zero hC hE)
  linear_combination e1 - (∏ k, c k ^ d k) * e2

end CurveEmbedOrbit


open CurveEmbedOrbit in
theorem CurveEmbedOrbit.proof : CurveEmbedOrbit.Statement := by
  intro K _ ι _ Ω _ y R hP hB hR hRu
  classical
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hex : ∀ t : R, ∃ σ : Ω →+* ℂ, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => σ (y p)) :=
    fun t => CurveOrbit.exists_sameOrbit hP hB (hR t t.2)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro t s hts
    have h1 : SameOrbit (t : (Σ k, ι k) → ℂ) s :=
      sameOrbit_trans (hf t) (by rw [hts]; exact sameOrbit_symm (hf s))
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, sameOrbit_refl _⟩ ⟨s.2, h1⟩)
  have hsurj : Function.Surjective f := by
    intro τ
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu _ (CurveOrbit.mem_mcPts τ y hj)
    exact ⟨⟨t, htR⟩, eq_of_sameOrbit hB
      (sameOrbit_trans (sameOrbit_symm (hf ⟨t, htR⟩)) (sameOrbit_symm hzt))⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end GroundTheory.Heights₂.Heights.Targets
