module

import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_factorial_mul_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  apply Reformulated.AutPerF.exists_factorial_mul_eq_pow <;> assumption

theorem exists_factorial_mul_eq_pow_ainf (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : Ainf l, ((n.factorial : ℕ) : Ainf l) * c = ((l : ℕ) : Ainf l) ^ n := by
  obtain ⟨c, hc⟩ := exists_factorial_mul_eq_pow l n
  refine ⟨algebraMap ℤ_[l] (Ainf l) c, ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using congrArg (algebraMap ℤ_[l] (Ainf l)) hc

end GlobalTheory.Per
