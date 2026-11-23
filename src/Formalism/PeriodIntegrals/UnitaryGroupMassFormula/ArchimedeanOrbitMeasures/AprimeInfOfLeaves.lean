module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GinfTestHolds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.AprimeInfW

theorem aprimeInf_iff : Formalism.L2.SG.Pf.NcReal.AprimeInf ↔ AprimeInfS := Iff.rfl

theorem aprimeInf_of (hV : AinfValue) (hG : GinfTest) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_iff.2 (aprimeInfS_of hV hG)

theorem aprimeInf_of_steps (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hH : HtotInf) (hG : GinfTest) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of (ainfValue_of hE hP hW hH) hG

theorem aprimeInf_of_open (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hF : HinfFin) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_steps hE hP hW (htotInf_of hF) ginfTest_holds

theorem aprimeInf_of_leaves (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hC : MassDataMassesW.HinfCompact) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_open hE hP hW (hinfFin_of hC)

end PI.AprimeInfW
