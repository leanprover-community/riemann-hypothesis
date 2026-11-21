import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationsTypePrimesOfJetTableSplitPrime

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_aAtG_of_rowPin : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    (∀ K X f T c, Q K X f T c →
      (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) →
    AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk :=
  GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient GlobalTheory.T.jetTableBound_splitPrime

end GlobalTheory.AtG
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holds_at_bundlePoints_of_trueColumns : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  atlas_forward_decl GlobalTheory.AtG.row_aAtG_of_rowPin
