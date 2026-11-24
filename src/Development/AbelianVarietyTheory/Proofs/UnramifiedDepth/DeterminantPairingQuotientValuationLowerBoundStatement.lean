module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.Valuation.Basic
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  first | exact @GlobalTheory.DetPairingBound.main | exact GlobalTheory.DetPairingBound.main | (intros; apply GlobalTheory.DetPairingBound.main <;> assumption)
