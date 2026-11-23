module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AprimeInf
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

namespace Formalism.L2.SG.Closed

theorem AprimeInf_holds [hG : Fact PI.AprimeInfW.GaugeVolUD] : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  PI.AprimeInfAsm.aprime_infinite_real Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds hG.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem JacGauge_holds : Formalism.L2.SG.Pf.JacGauge := Formalism.L2.SG.Pf.jacGauge

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_holds (hC : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  Formalism.L2.SG.Pf.NcReal.JX.realBracket_of_jac JacGauge_holds hC AprimeInf_holds
    (fun n ε => Formalism.MainNotions.S.Gauge.gauge_density_exists n ε)

end Formalism.L2.SG.Closed
