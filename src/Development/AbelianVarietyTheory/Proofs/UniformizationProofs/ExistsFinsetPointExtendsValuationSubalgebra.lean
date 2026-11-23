module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFactorFractionRing
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finset_point_extends_valuationSubalgebra (V F : Type) [CommRing V] [Field F]
    [Algebra V F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  first
  | exact @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends
  | (apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply _root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AffineFactorExists.exists_finset_extends <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AffineFactorExists.exists_finset_extends ..)

theorem exists_finset_points_extend_valuationSubalgebra : ∀ (V F : Type) [CommRing V] [Field F] [Algebra V F] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (s : Set (Spec (CommRingCat.of F) ⟶ B.left)), s.Finite → (∀ x ∈ s, x ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V F)))) → ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W → (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) → ∀ x ∈ s, ∃ y : Spec (CommRingCat.of W) ⟶ B.left, y ≫ B.hom = (Spec.map (CommRingCat.ofHom (algebraMap V W))) ∧ (Spec.map (CommRingCat.ofHom (algebraMap W F))) ≫ y = x := by
  intro V F _ _ _ B _ s hs hx
  classical
  choose t ht using fun x : s =>
    exists_finset_point_extends_valuationSubalgebra V F B.hom x.1 (hx x.1 x.2)
  haveI := hs.fintype
  refine ⟨Finset.univ.biUnion t, fun W hW h x hxs => ht ⟨x, hxs⟩ W hW fun a ha => h a ?_⟩
  exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, ha⟩

end GlobalTheory
