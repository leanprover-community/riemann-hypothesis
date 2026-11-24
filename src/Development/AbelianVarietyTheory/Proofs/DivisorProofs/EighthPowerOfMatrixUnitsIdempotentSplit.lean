module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace MatUnitIdem

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod' {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp' {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end MatUnitIdem


open MatUnitIdem in
theorem matUnits_univ_of_idem : ∀ {S : Scheme.{0}} (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] (E : Fin 8 → Fin 8 → (G ⟶ G)) (hE : ∀ a b, IsMonHom (E a b)) (hrel : ∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) (hsum : ∏ a, E a a = 𝟙 G) (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = E 0 0), ∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ (E a 0 ≫ r) = y a := by
  intro S G H _ _ _ E hE hrel hsum i r hi hr hir hri T y
  have key : ∀ b, E b b = (E b 0 ≫ r) ≫ i ≫ E 0 b := by
    intro b
    have h1 : E b 0 ≫ E 0 b = E b b := by rw [hrel]; simp
    have h2 : E b 0 ≫ E 0 0 = E b 0 := by rw [hrel]; simp
    calc E b b = E b 0 ≫ E 0 b := h1.symm
      _ = (E b 0 ≫ E 0 0) ≫ E 0 b := by rw [h2]
      _ = (E b 0 ≫ r) ≫ i ≫ E 0 b := by rw [← hri]; simp only [Category.assoc]
  refine ⟨∏ a, y a ≫ i ≫ E 0 a, ?_, ?_⟩
  · intro b
    haveI := hE b 0
    haveI := hr
    have hx : (∏ a, y a ≫ i ≫ E 0 a) ≫ E b 0 = y b ≫ i ≫ E 0 0 := by
      rw [prod_comp', Finset.prod_eq_single b]
      · have h3 : E 0 b ≫ E b 0 = E 0 0 := by rw [hrel]; simp
        simp only [Category.assoc, h3]
      · intro a _ hab
        have h3 : E 0 a ≫ E b 0 = 1 := by rw [hrel]; simp [hab]
        simp only [Category.assoc, h3, MonObj.comp_one]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [← Category.assoc, hx, ← hri]
    simp only [Category.assoc]
    simp only [reassoc_of% hir, hir, Category.comp_id]
  · intro z hz
    calc z = z ≫ ∏ b, E b b := by rw [hsum, Category.comp_id]
      _ = ∏ b, z ≫ E b b := comp_prod' _ _ _
      _ = ∏ b, y b ≫ i ≫ E 0 b := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [key, ← Category.assoc, hz]

end GlobalTheory
