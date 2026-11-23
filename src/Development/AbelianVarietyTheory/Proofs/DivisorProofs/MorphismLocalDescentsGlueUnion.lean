module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem descend_glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  intro R _ _ _ _ S Y Z W π y p q hπp hπs hSi hy hpb O h I V hV h₀ hh
  have hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O := by
    rw [Scheme.Hom.preimage_iSup]; exact iSup_le hV
  haveI := hy
  have hflat : Flat ((⨆ i, V i).ι ≫ y) := inferInstance
  have hsq : IsPullback (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) ((⨆ i, V i).ι ≫ y) π :=
    (isPullback_morphismRestrict p (⨆ i, V i)).paste_vert hpb
  have loc : ∀ (i : I) (T : Scheme.{0}) (k : T ⟶ (p ⁻¹ᵁ (⨆ i, V i)).toScheme) (t : T ⟶ (V i).toScheme),
      k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι ≫ p = t ≫ (V i).ι → k ≫ Z.homOfLE hV' ≫ h = t ≫ h₀ i := by
    intro i T k t hkt
    have sq := isPullback_morphismRestrict p (V i)
    have w : t ≫ (V i).ι = (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) ≫ p := by rw [Category.assoc]; exact hkt.symm
    have h1 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ∣_ V i) = t := sq.lift_fst _ _ _
    have h2 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ⁻¹ᵁ V i).ι = k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι :=
      sq.lift_snd _ _ _
    have h3 : k ≫ Z.homOfLE hV' = sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ Z.homOfLE (hV i) := by
      rw [← cancel_mono O.ι]; simp [h2]
    rw [reassoc_of% h3, ← hh i, reassoc_of% h1]
  have heq : pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) =
      pullback.snd (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) := by
    let a : pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ⟶ Y :=
      pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι
    have hcov : TopologicalSpace.IsOpenCover (fun i => a ⁻¹ᵁ V i) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, eq_top_iff]
      intro x _
      have hx : a.base x ∈ Set.range (⨆ i, V i).ι.base := by
        have ha : a = (pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i))) ≫ (⨆ i, V i).ι :=
          (Category.assoc _ _ _).symm
        rw [ha]
        first
          | exact ⟨_, rfl⟩
          | (rw [Scheme.comp_base]; exact ⟨_, rfl⟩)
          | exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.Opens.range_ι] at hx
      exact hx
    refine Scheme.Cover.hom_ext ((pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i))).openCoverOfIsOpenCover _ hcov)
      _ _ fun i => ?_
    change (a ⁻¹ᵁ V i).ι ≫ _ = (a ⁻¹ᵁ V i).ι ≫ _
    rw [← Category.assoc, loc i _ _ (a ∣_ V i), ← Category.assoc, loc i _ _ (a ∣_ V i)]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι]
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq (Z.homOfLE hV' ≫ h) heq
  refine ⟨hV', m, hm, fun W' g g' hg => ?_⟩
  have key := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W' π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq ((p ∣_ (⨆ i, V i)) ≫ g)
    (by rw [pullback.condition_assoc])
  exact key.unique rfl hg.symm

end GlobalTheory.MorDescent
