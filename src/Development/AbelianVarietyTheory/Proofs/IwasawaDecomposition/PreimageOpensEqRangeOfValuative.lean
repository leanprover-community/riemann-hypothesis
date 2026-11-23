module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
