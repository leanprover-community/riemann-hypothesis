module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransAff

theorem comp_mul_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) (f g : T ⟶ G') :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one_hom {R' : Type} [CommRing R'] {G' T T' : Over (Sp R')} [GrpObj G'] (x : T' ⟶ T) :
    x ≫ (1 : T ⟶ G') = 1 := by
  simp [Hom.one_def]

theorem comp_inv_eq (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G']
    (a : 𝟙_ (Over (Sp R')) ⟶ G') (b : 𝟙_ (Over (Sp R')) ⟶ G') (hab : a * b = 1) :
    (𝟙 G' * (toUnit G' ≫ a)) ≫ (𝟙 G' * (toUnit G' ≫ b)) = 𝟙 G' := by
  rw [comp_mul_hom, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit G') (toUnit G'),
    _root_.mul_assoc, ← comp_mul_hom, hab, comp_one_hom, _root_.mul_one]

theorem isAffineOpen_translates :
    ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  intro R' _ G' _ hs a W hW
  have e1 := comp_inv_eq R' G' a a⁻¹ (mul_inv_cancel a)
  have e2 := comp_inv_eq R' G' a⁻¹ a (inv_mul_cancel a)
  have i1 : IsIso (𝟙 G' * (toUnit G' ≫ a)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a⁻¹)).left, by rw [← Over.comp_left, e1]; rfl,
      by rw [← Over.comp_left, e2]; rfl⟩⟩
  have i2 : IsIso (𝟙 G' * (toUnit G' ≫ a⁻¹)).left :=
    ⟨⟨(𝟙 G' * (toUnit G' ≫ a)).left, by rw [← Over.comp_left, e2]; rfl,
      by rw [← Over.comp_left, e1]; rfl⟩⟩
  have : IsSeparated G'.hom := hs
  have : G'.left.IsSeparated := ⟨by rw [← terminal.comp_from G'.hom]; infer_instance⟩
  exact (hW.preimage_of_isIso _).inf (hW.preimage_of_isIso _)

end GlobalTheory.TransAff
