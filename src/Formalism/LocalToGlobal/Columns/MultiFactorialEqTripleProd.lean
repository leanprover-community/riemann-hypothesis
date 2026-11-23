module

public import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
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
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LocalToGlobal.GlobalTheory.HLatOps

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (AddMonoidAlgebra.coeff P m)‖ ^ 2 = ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) * ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι]

end Gen

end Formalism.L2.Col
