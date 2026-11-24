module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.MassSt
public import Formalism.HermitianLattices.StatementMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

def stdForm (K : Type) [Field K] [StarRing K] (n : ℕ) :
    (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

theorem stdForm_isSymm (K : Type) [Field K] [StarRing K] (n : ℕ) : (stdForm K n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp [stdForm_apply, mul_comm, starRingEnd_apply]

section Ortho

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

namespace StandardSymmetricSums

theorem form_sum {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (c d : Fin n → K) :
    h (∑ i, c i • e i) (∑ j, d j • e j) = ∑ i, star (c i) * d i := by

  simp [map_sum, LinearMap.sum_apply, he, mul_comm, starRingEnd_apply]

theorem form_left {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (i : Fin n) (d : Fin n → K) :
    h (e i) (∑ j, d j • e j) = d i := by

  simp [map_sum, he]

theorem star_int (r : 𝓞 K) : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

theorem exists_coord {n : ℕ} {e : Fin n → V} (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ c : Fin n → K, ∑ i, c i • e i = x :=
  (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)

theorem mem_lat_iff {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]

end StandardSymmetricSums

open StandardSymmetricSums

theorem finiteDimensional_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : FiniteDimensional K V := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  exact (Basis.mk hli hsp.ge).finiteDimensional_of_finite

theorem finrank_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : finrank K V = n := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  simpa using finrank_eq_card_basis (Basis.mk hli hsp.ge)

theorem isLattice_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Submodule.IsLattice K L := by
  obtain ⟨e, hli, hsp, rfl, -⟩ := hL
  exact Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range e))

theorem isFullLattice_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Submodule.IsFullLattice K L := by
  haveI := isLattice_of_ortho hL
  obtain ⟨e, hli, hsp, rfl, -⟩ := hL
  refine ⟨?_⟩
  apply top_unique
  rw [← hsp]
  exact Submodule.span_mono (Submodule.subset_span)
theorem isTotPosDef_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    IsTotPosDef h := by
  apply Formalism.HermitianLattices.Ext.L3.isTotPosDef_of_ortho <;> assumption

theorem trace_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := isTotPosDef_of_ortho hK hs hL x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

theorem isIntegralLat_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  apply Formalism.HermitianLattices.Ext.L3.isIntegralLat_of_ortho <;> assumption

theorem isUnimodular_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsUnimodular h L := by
  apply Formalism.HermitianLattices.Ext.L3.isUnimodular_of_ortho <;> assumption

theorem mass_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    0 < Formalism.HermitianLatticesTheory.mass h L := by
  have := finiteDimensional_of_ortho hL
  exact (Formalism.HermitianLatticesTheory.massBasic K V h hs (trace_pos_of_ortho hK hs hL) L (isFullLattice_of_ortho hL)).2.2

end Ortho

end ReciprocityTheory.ChartRestriction.L3
