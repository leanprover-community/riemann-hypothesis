module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.LogU

theorem _root_.GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ, ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  first | exact @GlobalTheory.LogUIntg.logDefect_coeff_dvd | exact GlobalTheory.LogUIntg.logDefect_coeff_dvd | (intros; apply GlobalTheory.LogUIntg.logDefect_coeff_dvd <;> assumption)
