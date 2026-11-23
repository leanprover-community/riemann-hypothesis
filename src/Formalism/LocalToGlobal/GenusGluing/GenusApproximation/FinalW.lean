module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.ApproximationAdelicHolds
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.Cayley
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.DetAddDiagonalCons
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.EvaluationNeZeroHolds
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.WeakApproxAllOf
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem shiftDiagonal_holds : ShiftDiag := shiftDiag_of shiftOne_holds

theorem cayleyApproximation_holds : CayleyStep := cayleyStep_of evaluationNeZero_holds approximationAdelic_holds unitNearOne_holds

theorem weakApproximationAll_holds : WeakApproxAll := weakApproxAll_of shiftDiagonal_holds cayleyApproximation_holds integralAtInverse_holds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem weakApproximation_unitary (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : WeakApproxU hc n := weakApproximationAll_holds F E hc n

theorem unimodGenus_iff (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : UnimodGenusLoc E n ↔ UnimodGenus hc n :=
  localAdelicEquiv_holds F E hc n (weakApproximation_unitary hc n)

end Formalism.L2.GenusGluing.Gen
