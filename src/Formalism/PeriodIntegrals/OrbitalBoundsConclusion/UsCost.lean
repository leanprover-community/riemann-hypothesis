module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ContinuousBlockDiagEmbedRingHom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ContinuousBlockMatrixThree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.EntryLeLsz
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Letters
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.RightRegularActionListDLREqAppend
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Smooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.UnitarySumCostOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZCostOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem operator_word_cost : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  PI.UnitaryGroupMassFormula.UsCost.unitarySum_cost_of_parts PI.UnitaryGroupMassFormula.UsCost.wordsId PI.UnitaryGroupMassFormula.UsCost.letterSize PI.UnitaryGroupMassFormula.UsCost.starScale
    PI.UnitaryGroupMassFormula.UsCost.commLR PI.UnitaryGroupMassFormula.UsCost.offK PI.UnitaryGroupMassFormula.UsCost.zSmooth
    (PI.UnitaryGroupMassFormula.UsCost.zCost_of PI.UnitaryGroupMassFormula.UsCost.zSmooth PI.UnitaryGroupMassFormula.UsCost.zDeriv PI.UnitaryGroupMassFormula.UsCost.dirSize)
