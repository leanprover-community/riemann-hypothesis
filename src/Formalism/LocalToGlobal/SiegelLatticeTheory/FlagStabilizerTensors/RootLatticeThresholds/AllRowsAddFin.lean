module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsAddFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem eHom_fin (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) := by
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have : FiniteDimensional ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
    Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_gap X hHC hG
  exact Formalism.L2.SG.RowsDef.finiteDimensional_eHom hB.1 hB.2

theorem rowsAdd_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : RowsAdd X :=
  Formalism.L2.SG.Pf.AllRowsAdd.rowsAdd_of X (eHom_fin X hHC hG)

end Formalism.L2.SG.Pf.AllRowsAddFin
