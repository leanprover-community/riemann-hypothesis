import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.UnitsPowers
import BuildAid.ForwardExisting

section
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  obtain ⟨vr, top, hloc, -⟩ := GlobalTheory.LocFieldOfDVR.exists_isNonarchimedeanLocalField K.O K.E
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  atlas_forward_decl GlobalTheory.UnitLemma.UQ.finite_units_mod_sq
