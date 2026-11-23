module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedge
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory GlobalTheory.LogDR


theorem _root_.GlobalTheory.T.logDifferential_mul_logCoordinateWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  first | exact @GlobalTheory.LogDR.dlog_mul_logWedge | exact GlobalTheory.LogDR.dlog_mul_logWedge | (intros; apply GlobalTheory.LogDR.dlog_mul_logWedge <;> assumption)
