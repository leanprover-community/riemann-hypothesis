import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteSubfieldSpecial
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend

theorem exists_numberField_point (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C]
    (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X),
      spMap e ≫ x' = x :=
  _root_.UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main C X π x

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_point_over_number_field : ∀ (C : Type) [Field C] [CharZero C] [Algebra.IsAlgebraic ℚ C] (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : Sp C ⟶ X), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (e : K →+* C) (x' : Sp K ⟶ X), spMap e ≫ x' = x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Sl.Reg.Descend.exists_numberField_point
