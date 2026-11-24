module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Branch
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem stripsMem : StripsMem := by
  first
  | exact stripsMem_proof
  | exact P.stripsMem_proof
  | exact strips_mem
theorem gtPieri : GTPieri := by
  first
  | exact gtPieri_proof
  | exact P.gtPieri_proof
  | exact gelfand_tsetlin_pieri
theorem stdCountGT : StdCountGT := by
  first
  | exact stdCountGT_proof
  | exact P.stdCountGT_proof
  | exact standard_count_gt
theorem countCont : CountCont := countCont_of stripsMem gtPieri stdCountGT
theorem countPAll : CountPAll := countPAll_of countCont

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
