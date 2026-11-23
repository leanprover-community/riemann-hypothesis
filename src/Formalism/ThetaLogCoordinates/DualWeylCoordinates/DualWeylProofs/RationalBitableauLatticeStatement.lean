module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EvalIdBracketCanonical
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnEvalMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem highest_weight_corollary_two : RationalBitableauLatticeStatement := by
  intro n _ mu hmu
  have h := qn_main n (qn_nu mu) (qn_nu_anti hmu) (fun I : TIdx mu => brkPol mu I) (canT mu)
    (fun I => bracket_mem_dualWeyl hmu I) (dualWeyl_le_span_bracket hmu) (eval_id_bracket_canonical mu)
  rw [qn_nu_cast hmu] at h
  exact h

end Formalism.InvariantFactorPaths.ColumnFamilies
