module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IdealMulPrincipal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IsImgTrans
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.KsetMulVecMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StHOfOpen
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

theorem stKFin : StKFin := stKFin_of (stLatFin_of lattice_dense)

theorem adelClassFin_of_H (h : StH) : PI.AdelClassFin.AdelClassFin :=
  stTop stCong stKFin (stGenusOf stDict h)

theorem adelClassFin_of_open (h1 : SpOne) (h2 : IdealBoundAll) (h3 : SvMajE) (h4 : SvCodiff) (h5 : SvBasis)
    (h6 : SvGramDet) (h7 : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_H (stH_of_open h1 h2 h3 h4 h5 h6 h7)

end PIW.AdelClassFin
