module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  intro S P hloc hrep R' _ x hx
  have key : ∀ (V : S.Opens) (hV : IsAffineOpen V) (r : R'),
      (∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V) →
      P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x) := by
    intro V hV r hsub
    have e : (⊤ : (Sp (Localization.Away r)).Opens) ≤
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) ⁻¹ᵁ V := by
      intro q _
      show x.base ((spMap (algebraMap R' (Localization.Away r))).base q) ∈ V
      apply hsub
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))
    let g' : Γ(S, V) ⟶ CommRingCat.of (Localization.Away r) :=
      (spMap (algebraMap R' (Localization.Away r)) ≫ x).appLE V ⊤ e ≫ (Scheme.ΓSpecIso _).hom
    have hy : spMap (algebraMap R' (Localization.Away r)) ≫ x = spMap g'.hom ≫ hV.fromSpec := by
      have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (spMap (algebraMap R' (Localization.Away r)) ≫ x) hV
        (isAffineOpen_top (Sp (Localization.Away r))) e
      rw [IsAffineOpen.fromSpec_top] at h1
      rw [(Iso.inv_comp_eq _).1 h1.symm, Scheme.isoSpec_Spec_hom]
      simp only [spMap, CommRingCat.ofHom_hom, g', Spec.map_comp, Category.assoc]
    have hker : killIdeal (ptQ P V hV) ≤ RingHom.ker g'.hom := by
      refine (hx V hV).trans ?_
      intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      have hg : g' = x.app V ≫ ((spMap (algebraMap R' (Localization.Away r))).appLE (x ⁻¹ᵁ V) ⊤ e ≫
          (Scheme.ΓSpecIso _).hom) := by
        simp only [g', Scheme.Hom.comp_appLE, Category.assoc]
      rw [hg, CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
    have := (hrep V hV (Localization.Away r) g'.hom).2 hker
    rw [hy]
    exact this
  let G : Set R' := {r | ∃ V : S.Opens, IsAffineOpen V ∧ ∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum R' := ⟨m, hm.isPrime⟩
    obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
      (show x.base p ∈ (⊤ : S.Opens) from trivial)
    have hpV' : p ∈ (x ⁻¹ᵁ V : TopologicalSpace.Opens (PrimeSpectrum R')) := hpV
    obtain ⟨W, ⟨r, rfl⟩, hpW, hW⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (PrimeSpectrum.isBasis_basic_opens (R := R'))) hpV'
    have hr : r ∈ G := ⟨V, hV, fun q hq => hW (show q ∈ PrimeSpectrum.basicOpen r from hq)⟩
    exact hpW (hle (Ideal.subset_span hr))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine hloc R' x t hspan fun r hr => ?_
  obtain ⟨V, hV, hsub⟩ := ht hr
  exact key V hV r hsub

end GlobalTheory.PtClosed
