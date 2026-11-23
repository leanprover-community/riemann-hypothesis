module

public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.Analysis.Complex.Cardinality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LbMarking

theorem linearLift_bijective_of_discrete_kernels : ∀ (M : Type) [Group M] (g g' : ℕ) (ex : (Fin g' → ℂ) → M) (r : (Fin g → ℂ) → M) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z w, ex (z + w) = ex z * ex w) → (∀ x, ex (h x) = r x) → Function.Surjective r → (∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x‖ < δ → r x = 1 → x = 0) → (∃ δ : ℝ, 0 < δ ∧ ∀ y, ‖y‖ < δ → ex y = 1 → y = 0) → Function.Bijective h := by
  intro M _ g g' ex r h hadd hr hsurj ⟨δ, hδ, hsep⟩ ⟨ε, hε, hsep'⟩
  have hex0 : ex 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have hs : 0 < δ / (2 * ‖x‖) := by positivity
    have ht : ((δ / (2 * ‖x‖) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hs.ne'
    have h1 : r (((δ / (2 * ‖x‖) : ℝ) : ℂ) • x) = 1 := by
      rw [← hr, map_smul, hx, smul_zero, hex0]
    have h2 : ‖((δ / (2 * ‖x‖) : ℝ) : ℂ) • x‖ < δ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      have : δ / (2 * ‖x‖) * ‖x‖ = δ / 2 := by
        field_simp
      rw [this]
      linarith
    have h3 := hsep _ h2 h1
    exact hne ((smul_eq_zero.mp h3).resolve_left ht)
  · intro v
    by_contra hv
    have hsub : ∀ a b, ex a = 1 → ex b = 1 → a ≠ b → ε ≤ ‖a - b‖ := by
      intro a b ha hb hab
      by_contra hlt
      have h1 : ex (a - b) = 1 := by
        have h2 := hadd (a - b) b
        rw [sub_add_cancel, ha, hb, _root_.mul_one] at h2
        exact h2.symm
      exact hab (sub_eq_zero.mp (hsep' _ (not_le.mp hlt) h1))
    have hK : {y | ex y = 1}.Countable := by
      have hdisj : ({y | ex y = 1} : Set (Fin g' → ℂ)).PairwiseDisjoint
          (fun y => ball y (ε / 2)) := by
        intro a ha b hb hab
        refine Set.disjoint_left.mpr ?_
        intro z hza hzb
        have h1 := hsub a b ha hb hab
        have h2 : dist z a < ε / 2 := hza
        have h3 : dist z b < ε / 2 := hzb
        have h4 : dist a b ≤ dist z a + dist z b := dist_triangle_left a b z
        rw [dist_eq_norm a b] at h4
        linarith
      exact hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
        (fun y _ => ⟨y, mem_ball_self (half_pos hε)⟩)
    choose x hx using fun t : ℂ => hsurj (ex (t • v))
    have hkK : ∀ t, ex (t • v - h (x t)) = 1 := by
      intro t
      have h2 := hadd (t • v - h (x t)) (h (x t))
      rw [sub_add_cancel, hr, hx t] at h2
      exact right_eq_mul.mp h2
    have hinj : Function.Injective (fun t : ℂ =>
        (⟨t • v - h (x t), hkK t⟩ : {y | ex y = 1})) := by
      intro s t hst
      by_contra hne
      have h1 : s • v - h (x s) = t • v - h (x t) := congrArg Subtype.val hst
      have hc : s - t ≠ 0 := sub_ne_zero.mpr hne
      apply hv
      refine ⟨(s - t)⁻¹ • (x s - x t), ?_⟩
      have h2 : (s - t) • v = h (x s - x t) := by
        rw [map_sub, sub_smul]
        rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
        rw [h1, add_comm]
      rw [map_smul, ← h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    haveI : Countable {y | ex y = 1} := hK.to_subtype
    have hC : Countable ℂ := hinj.countable
    have hle := Cardinal.mk_le_aleph0_iff.mpr hC
    rw [Cardinal.mk_complex] at hle
    exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr hle)

end GlobalTheory.CompanionTheory.Ar.LbMarking
