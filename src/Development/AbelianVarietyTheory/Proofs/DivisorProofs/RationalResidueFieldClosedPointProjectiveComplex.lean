import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed_of_isProjOver : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  intro X _ p hP x hx
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hP
  exact ratRes_locRing_of_isClosed X p x hx

end GlobalTheory.FieldPair
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  atlas_forward_decl GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver
