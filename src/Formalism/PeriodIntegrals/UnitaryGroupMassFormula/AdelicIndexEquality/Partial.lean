module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertQRG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LiftMatMapSame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Reduce
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_open (hG : GLChi) (hQ : QReflPow) : PI.AdIndexEq.IndexEq :=
  indexEq_of_loc compact_commensurated lift_unitary' matrix_v_injective matrix_v_unitary compact_local_global reduce_local
    (locSplitChi_of hG) (locInertChi_of_qReflPow hQ)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
