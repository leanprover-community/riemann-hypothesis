module

public import Formalism.PeriodIntegrals.DiscIn
public import Formalism.PeriodIntegrals.ZerosWindowIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthZeta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalProofs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogWindowLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronGlue
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

namespace PI.EF

theorem localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C :=
  localLemma_of hLI (localAbstract_of hDF hDL)
    ⟨7, max 300000 53946, by norm_num, lt_max_of_lt_left (by norm_num),
      lGrowth_of hLB (zetaGrowth_of hZB)⟩ zeroLocus hZW

theorem explicitFormula_main (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) : PI.ExplicitFormula :=
  explicitFormula_of_local hZW (localLemma_of_helpers hZW hDF hDL hLB hZB hLI) perron_gluing_sides

end PI.EF
