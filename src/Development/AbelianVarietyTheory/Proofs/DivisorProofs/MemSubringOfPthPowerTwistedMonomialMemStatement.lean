module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
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


theorem _root_.GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  first | exact @GlobalTheory.LogDR.round_coeff_mem | exact GlobalTheory.LogDR.round_coeff_mem | (intros; apply GlobalTheory.LogDR.round_coeff_mem <;> assumption)
