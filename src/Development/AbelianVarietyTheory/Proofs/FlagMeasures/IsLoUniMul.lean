module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  apply PI.TermAttrConst.UnitaryGroupMassFormula.isLoUni_mul <;> assumption

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
