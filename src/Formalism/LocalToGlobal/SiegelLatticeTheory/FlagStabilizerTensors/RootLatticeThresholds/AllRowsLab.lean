module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAddFin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsDcount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.L2.SG.Pf.AllRowsLab

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rowsGood_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι)
    (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι) : RowsGood X :=
  Formalism.L2.SG.Pf.RowsGoodRed.rowsGood_of X G ι hT hL (Formalism.L2.SG.Pf.AllRowsAdd.projT_holds X G)
    (Formalism.L2.SG.Pf.AllRowsDcount.dcountEq_holds X hG)

theorem rowsLab_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (G : Formalism.L2.SG.RowDict.GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)
    (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι) (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι)
    (hAT : AutTie D X.B X.pl) : RowsLab X :=
  rowsLab_of X (Formalism.L2.SG.Pf.AllRowsAddFin.rowsAdd_holds X hHC hG) (rowsGood_holds X hG G ι hT hL)
    (Formalism.L2.SG.Pf.AllRowsClosed.etUniv_holds X) hAT

end Formalism.L2.SG.Pf.AllRowsLab
