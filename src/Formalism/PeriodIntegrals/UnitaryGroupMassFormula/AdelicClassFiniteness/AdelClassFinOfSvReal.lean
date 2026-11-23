module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.BlkMulVecCat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.ExistsBoundedMultiplier
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Partial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorCodifferent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorGramDet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorMajorantE
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

namespace PIW.AdelClassFin

theorem adelClassFin_of_svReal (h : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_open spOne existsBoundedMultiplier successive_vector_majorant_e successive_vector_codifferent successive_vector_basis successive_vector_gram_det h

end PIW.AdelClassFin

end
