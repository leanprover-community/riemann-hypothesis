import Mathlib
import BuildAid.ForwardExisting

section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  atlas_forward_decl GlobalTheory.natCard_homology_restrictScalars
