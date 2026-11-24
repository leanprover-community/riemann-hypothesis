module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
public import Formalism.HermitianLattices.StatementMass
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

section Gen

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_algebraMap_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩

theorem inner_sum_orthonormal (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a b : Fin n → K) :
    h (∑ i, a i • e i) (∑ j, b j • e j) = ∑ i, star (a i) * b i := by

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, he,
  smul_eq_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem fg_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) : L.FG := by
  obtain ⟨e, -, -, rfl, -⟩ := hL
  exact Submodule.fg_span (Set.finite_range e)

theorem integral_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsIntegralLat h L := by
  obtain ⟨e, -, -, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy
  have e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm
  have e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm
  rw [e1, e2, inner_sum_orthonormal h e he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a', ha'⟩ := star_algebraMap_mem_range (a i)
  rw [← ha', ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem unimodular_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by
  apply Formalism.HermitianLattices.Ext.L3.isUnimodular_of_ortho <;> assumption

theorem genus_orthonormal_integral_unimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by
  have hG := (final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2
  exact ⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩

theorem mass_le_of_card_class_reps_le (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by
  classical
  unfold mass
  split_ifs with hs
  · refine le_trans ?_ (hc _ hs.choose_spec)
    calc ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ hs.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
      _ = (hs.choose.card : ℝ) := by simp
  · exact hB

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
