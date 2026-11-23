module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_surj : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  intro T _ _ ι _ _ 𝒜 hmono hunion E _ _ Q _ Ek _ _ e h he hh hsurj g hg b
  classical
  obtain ⟨⟨z, ⟨m, hm⟩⟩, hb0⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) b
  obtain ⟨c, hc, hcm⟩ := hm
  subst hcm
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hz0⟩ := IsLocalization.mk'_surjective Q.primeCompl z
  simp only at hb0 hz0
  subst hz0
  obtain ⟨k₁, y₁, hy₁⟩ := hsurj x
  obtain ⟨k₂, t₂, ht₂⟩ := hsurj s
  obtain ⟨k₃, hc₃⟩ := hunion c
  obtain ⟨k₁₂, h1, h2⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨k, h12, h3⟩ := directed_of (· ≤ ·) k₁₂ k₃
  have hk1 : k₁ ≤ k := h1.trans h12
  have hk2 : k₂ ≤ k := h2.trans h12
  set y := h k₁ k hk1 y₁
  set t := h k₂ k hk2 t₂
  have hy : e k y = x := by rw [hh, hy₁]
  have ht : e k t = s := by rw [hh, ht₂]
  have htQ : t ∈ (Q.comap (e k)).primeCompl := by
    show t ∉ Q.comap (e k)
    rw [Ideal.mem_comap, ht]; exact hs
  set c' : 𝒜 k := ⟨c, hmono h3 hc₃⟩
  have hc' : c' ∈ nonZeroDivisors (𝒜 k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    apply nonZeroDivisors.ne_zero hc
    have := congrArg (fun a : 𝒜 k => (a : T)) h0
    simpa [c'] using this
  set z' : (Localization.AtPrime (Q.comap (e k))) := IsLocalization.mk' (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  set m' : (Localization.AtPrime (Q.comap (e k))) := algebraMap (𝒜 k) (Localization.AtPrime (Q.comap (e k))) c'
  have hm' : m' ∈ Algebra.algebraMapSubmonoid (Localization.AtPrime (Q.comap (e k))) (nonZeroDivisors (𝒜 k)) := ⟨c', hc', rfl⟩
  refine ⟨k, IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩, ?_⟩
  have hu1 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c)) :=
    IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T))
  have hu2 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) :=
    (IsLocalization.map_units (Localization.AtPrime Q) (⟨s, hs⟩ : Q.primeCompl)).map _
  have hgm : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m') = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) := by
    have hm'e : m' = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) (algebraMap (𝒜 k) (Ek k) c') :=
      IsScalarTower.algebraMap_apply (𝒜 k) (Ek k) (Localization.AtPrime (Q.comap (e k))) c'
    rw [hm'e, hg, he, ← IsScalarTower.algebraMap_apply]
    rfl
  have hgt : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s) := by rw [hg, ht]
  have hgy : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by rw [hg, hy]
  have hz' : z' * algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y :=
    IsLocalization.mk'_spec (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  have hX : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩ * algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m' = algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩
  have hz : IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩ * algebraMap E (Localization.AtPrime Q) s = algebraMap E (Localization.AtPrime Q) x :=
    IsLocalization.mk'_spec (Localization.AtPrime Q) x ⟨s, hs⟩
  have hb : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩)
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) *
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩) :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) _ _
  have e1 : b * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hb0, ← mul_assoc, hb, ← map_mul, hz]
  have e2 : g k (IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩) * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hgm, ← hgt, ← mul_assoc, ← map_mul, hX, ← map_mul, ← map_mul, hz', hgy]
  exact (hu1.mul hu2).mul_left_inj.mp (e2.trans e1.symm)

end GlobalTheory
