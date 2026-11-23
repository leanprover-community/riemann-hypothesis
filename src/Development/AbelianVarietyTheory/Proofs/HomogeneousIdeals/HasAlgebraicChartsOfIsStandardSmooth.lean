module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

structure IsAlgebraicChart (e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)) : Prop where
  exists_eq_div : ∃ (x : Fin d → A) (s : A), ∀ p ∈ e.source, p s ≠ 0 ∧ ∀ i, e p i = p (x i) / p s
  analyticOnNhd : ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target

variable [CompleteSpace 𝕜]

theorem exists_isAlgebraicChart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g := by
  obtain ⟨e, hp, he, ha⟩ := exists_chart_of_etale g hg p
  refine ⟨e, ⟨⟨fun i => g (X i), 1, fun q _ => ⟨by simp, fun i => ?_⟩⟩, ha⟩, hp, he⟩
  rw [he]
  simp [coords]

theorem exists_isAlgebraicChart_of_away (s : A) (B : Type*) [CommRing B] [Algebra 𝕜 B]
    [Algebra A B] [IsScalarTower 𝕜 A B] [IsLocalization.Away s B]
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 B] (p : A →ₐ[𝕜] 𝕜) (hp : p s ≠ 0) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d 𝕜 B
  have hj : IsOpenEmbedding (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) :=
    isOpenEmbedding_comap_away s
  obtain ⟨q, rfl⟩ : p ∈ range (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) := by
    rw [range_comap_away s]
    exact hp
  have : Nonempty (B →ₐ[𝕜] 𝕜) := ⟨q⟩
  obtain ⟨F, hFs, hFt, hFc⟩ : ∃ F : OpenPartialHomeomorph (B →ₐ[𝕜] 𝕜) (A →ₐ[𝕜] 𝕜),
      F.source = univ ∧ F.target = range (comap (IsScalarTower.toAlgHom 𝕜 A B)) ∧
      ⇑F = comap (IsScalarTower.toAlgHom 𝕜 A B) :=
    ⟨IsOpenEmbedding.toOpenPartialHomeomorph _ hj, by simp, by simp, by simp⟩
  have hinv : ∀ q', F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') = q' := fun q' => by
    have := F.left_inv (x := q') (by rw [hFs]; trivial)
    rwa [hFc] at this
  obtain ⟨eB, heB, hqB, -⟩ := exists_isAlgebraicChart_of_etale g hg q
  obtain ⟨xB, sB, hB⟩ := heB.exists_eq_div
  obtain ⟨⟨b, hb⟩, hxb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers s) xB
  obtain ⟨⟨c, ⟨u, hu⟩⟩, hcu⟩ := IsLocalization.surj (Submonoid.powers s) sB
  have hxb' : ∀ i, ∃ a, algebraMap A B a = b • xB i := fun i => hxb i
  choose a ha using hxb'
  have hbu : IsUnit (algebraMap A B b) := IsLocalization.map_units B (⟨b, hb⟩ : Submonoid.powers s)
  have huu : IsUnit (algebraMap A B u) := IsLocalization.map_units B (⟨u, hu⟩ : Submonoid.powers s)
  refine ⟨F.symm.trans eB, ⟨⟨fun i => a i * u, c * b, ?_⟩, fun a' => ?_⟩, ?_⟩
  · rintro p' ⟨hp'1, hp'2⟩
    have hp'3 : p' ∈ F.target := hp'1
    rw [hFt] at hp'3
    obtain ⟨q', rfl⟩ := hp'3
    have hp'4 : F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') ∈ eB.source := hp'2
    rw [hinv] at hp'4
    have h1 : ∀ i, q' (xB i) = q' (algebraMap A B (a i)) / q' (algebraMap A B b) := fun i =>
      apply_eq_div_of_mul_eq q' hbu (by rw [ha i, Algebra.smul_def, mul_comm])
    have h2 : q' sB = q' (algebraMap A B c) / q' (algebraMap A B u) :=
      apply_eq_div_of_mul_eq q' huu hcu
    have hb0 : q' (algebraMap A B b) ≠ 0 := (hbu.map q').ne_zero
    have hu0 : q' (algebraMap A B u) ≠ 0 := (huu.map q').ne_zero
    have hs0 : q' sB ≠ 0 := (hB q' hp'4).1
    have hc0 : q' (algebraMap A B c) ≠ 0 := by
      intro h0
      rw [h2, h0, zero_div] at hs0
      exact hs0 rfl
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinv, comap_apply,
      IsScalarTower.toAlgHom_apply, map_mul]
    refine ⟨mul_ne_zero hc0 hb0, fun i => ?_⟩
    rw [(hB q' hp'4).2 i, h1 i, h2]
    field_simp
  · have hfun : (fun z => (F.symm.trans eB).symm z a') = fun z => eB.symm z (algebraMap A B a') := by
      funext z
      simp [hFc, comap_apply]
    rw [hfun]
    exact (heB.analyticOnNhd _).mono fun z hz => hz.1
  · refine ⟨?_, ?_⟩
    · show _ ∈ F.target
      rw [hFt]
      exact mem_range_self q
    · show F.symm _ ∈ eB.source
      rw [hinv]
      exact hqB

end GlobalTheory.AffinePoints
