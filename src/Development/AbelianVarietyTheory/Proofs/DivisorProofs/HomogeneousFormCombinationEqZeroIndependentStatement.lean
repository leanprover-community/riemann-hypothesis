module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.homogeneousFormCombination_eq_zero_independent : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ) (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  first | exact @GlobalTheory.HSAmp.homogComb_eq_zero | exact GlobalTheory.HSAmp.homogComb_eq_zero | (intros; apply GlobalTheory.HSAmp.homogComb_eq_zero <;> assumption)
