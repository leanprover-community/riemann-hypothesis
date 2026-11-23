module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
public import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.EqToBdRPlusOfBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCZero
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem comparison_toBdRPlus (x : Reformulated.AutPerF.Acris l (Cmp6.OC l)) :
    Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x) := by
  have h := eq_toBdRPlus_of_bounded (jOC l) (jOC_zero l) (jOC_bounded l)
  rw [← h]
  show Cmp6.cP l ((Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end Formalism.BasicNotions.CmpTie.Incl
