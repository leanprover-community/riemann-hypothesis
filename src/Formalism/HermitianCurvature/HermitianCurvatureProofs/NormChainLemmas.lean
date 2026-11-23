module

public import Formalism.HermitianCurvature.StatementPN
public import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Formalism.FlagUnipotentLattices.ValuationProductBound
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
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

namespace Formalism.FourierDecayAlt.P.NormChainLemmas

open Formalism.FourierDecayAlt.PN Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem exactCores : Formalism.FourierDecayAlt.PN.ExactCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.S4.step4, Formalism.HermitianLatticeCounting.Final.S4.omCount, Formalism.HermitianLatticeCounting.Final.S4.weightedCS,
   Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four⟩

theorem loopCores : Formalism.FourierDecayAlt.PN.LoopCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.single_row_lattice_sum_bound,
   Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gainSqrt, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lattice_exp_sum_upper_bound, Formalism.FourierDecayAlt.Final.pb_loopsJoint,
   Formalism.FourierDecayAlt.Final.pb_loopsGiveRows⟩

theorem nGChain : Formalism.FourierDecayAlt.PN.NGChain :=
  ⟨exactCores, Formalism.FourierDecayAlt.Final.pn_classSquaresSum, Formalism.FourierDecayAlt.Final.pn_rowFromClasses,
   Formalism.FourierDecayAlt.Final.pn_classCS, Formalism.FourierDecayAlt.Final.pn_firstBracket, Formalism.FourierDecayAlt.Final.pn_secondBracket,
   Formalism.FourierDecayAlt.Final.pn_meanAmpJoint, Formalism.FourierDecayAlt.Final.pn_rowNGAbstract, Formalism.FourierDecayAlt.Final.pn_normBound,
   Formalism.FourierDecayAlt.Final.pn_framePassage, Formalism.FourierDecayAlt.Final.pn_normRe, Formalism.FourierDecayAlt.Final.pn_exponentSum,
   Formalism.FourierDecayAlt.Final.pn_nGNumbers⟩

end Formalism.FourierDecayAlt.P.NormChainLemmas

namespace Formalism.FourierDecayAlt.P

theorem loop_kernels : Formalism.FourierDecayAlt.PN.LoopCores := NormChainLemmas.loopCores

theorem norm_chain : Formalism.FourierDecayAlt.PN.NGChain := NormChainLemmas.nGChain

end Formalism.FourierDecayAlt.P
