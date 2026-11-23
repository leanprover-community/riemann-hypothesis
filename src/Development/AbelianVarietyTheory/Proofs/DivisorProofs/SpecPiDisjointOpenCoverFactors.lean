module

public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecPi

theorem specPi_cover : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  intro R _ n D _ _
  let S := sigmaSpec (fun i => CommRingCat.of (D i))
  have hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i) :=
    fun i => ι_sigmaSpec _ i
  have hinv : ∀ y, (inv S) (S y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hsurj : ∀ x, S ((inv S) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine ⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k),
        (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y :=
      fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩
    obtain ⟨k, z, hz⟩ := hcov ((inv S) x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, z, ?_⟩
    rw [← hS k, Scheme.Hom.comp_apply, hz, hsurj]
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hS, Scheme.Hom.comp_apply] at ha hb
    have e := congrArg (inv S) (ha.trans hb.symm)
    rw [hinv, hinv] at e
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp e
    exact absurd rfl hij
  · intro i
    refine ⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩
    simp only [Over.mk_hom, Iso.symm_hom]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

end GlobalTheory.SpecPi
