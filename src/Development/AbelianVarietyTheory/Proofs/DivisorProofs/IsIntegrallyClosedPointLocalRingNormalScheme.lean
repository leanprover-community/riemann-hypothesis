import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_locRing : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  intro X _ _ x
  let e : X.presheaf.stalk x ≃+* locRing x := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective _ X.functionField (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk x
  exact IsIntegrallyClosed.of_equiv e

end GlobalTheory.FieldPair
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_pointLocalRing_normalScheme : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  atlas_forward_decl GlobalTheory.FieldPair.isIntegrallyClosed_locRing
