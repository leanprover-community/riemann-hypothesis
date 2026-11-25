module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteQuotientComap
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.IntegerMulIntegral

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)) (v : Fin n → E),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (m : Int) ↦ And (Ne.{1} m 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m v)) :=
  GlobalTheory.FiniteQuotientComap.exists_int_smul_mem

end Bl.IntegerMulIntegral
