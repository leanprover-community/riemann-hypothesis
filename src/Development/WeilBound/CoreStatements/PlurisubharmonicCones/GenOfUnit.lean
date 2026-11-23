module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.gen_unit <;> assumption

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.gen_untens <;> assumption

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

end LevelTowerAlt
