module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
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

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkNorm_mem {G : Type} [Group G] (I : Subgroup G) (x y : G) :
    (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, y = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I) := ha
    rw [QuotientGroup.eq] at h
    exact ⟨a, a.2, _, h, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl

private theorem hkNorm_reps {G : Type} [Group G] (I : Subgroup G) (x : G) (h : FinOrb I I x) :
    ∃ s : Finset G, (∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I)) ∧
      ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q := by
  classical
  refine ⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']
    exact (Set.Finite.mem_toFinset h).1 hq
  · refine ⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩
    rintro y ⟨hy, rfl⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']

private theorem hkNorm_tr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x u w : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (hw : w ∈ Subgroup.normalizer (I : Set G))
    (s : Finset G) (h1 : ∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I))
    (h2 : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q) (v : fixd ρ I) :
    (hk ρ I (u * x * w) v : M) = ∑ y ∈ s, ρ (u * y * w) v := by
  classical
  have cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha
  have cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha
  have cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha
  have cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha
  have key := (hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at key
    exact key
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I x z).1 (h1 z hz)
    exact (hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩
  · intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    obtain ⟨y, ⟨hy, hyq⟩, huniq⟩ := h2 ((u⁻¹ * a * u * x : G) : G ⧸ I)
      ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)
    refine ⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩
    · rw [QuotientGroup.eq] at hyq ⊢
      convert mul_mem (cw' _ hyq) hb using 1
      group
    · rintro y' ⟨hy', h⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [huniq z ⟨hz, ?_⟩]
      rw [QuotientGroup.eq] at h ⊢
      convert cw _ (mul_mem h (inv_mem hb)) using 1
      group

private theorem hkNorm_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (v : fixd ρ I) : (hk ρ I u v : M) = ρ u v := by
  have h := hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    refine ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩
    rw [QuotientGroup.eq]
    simpa using mul_mem ha hb) v
  simpa using h

private theorem hkNorm_mul {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  obtain ⟨s, h1, h2⟩ := hkNorm_reps I x (hI x)
  have h0 := hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2
  have hl := hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2
  have hr := hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2
  simp only [one_mul, mul_one] at h0 hl hr
  constructor
  · ext v

    rw [hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]
    simp only [map_mul, Module.End.mul_apply]
  · ext v
    rw [hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]
    simp only [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.AlgebraTools.hkNorm :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (u : G), HeckePair I → u ∈ Subgroup.normalizer (I : Set G) → (∀ v : fixd ρ I, (hk ρ I u v : M) = ρ u v) ∧ hk ρ I 1 = 1 ∧ IsUnit (hk ρ I u) ∧ ∀ x : G, hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  intro A G M _ _ _ _ ρ I u hI hu
  have h1 : hk ρ I 1 = 1 := by
    ext v
    rw [hkNorm_one ρ I hI 1 (one_mem _)]
    simp
  refine ⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]
