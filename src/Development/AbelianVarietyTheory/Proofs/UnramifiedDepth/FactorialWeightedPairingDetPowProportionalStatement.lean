module

public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportional
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

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.factorialWeightedPairing_detPow_proportional : (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (Y - M) * Q) A) * (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A) = (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) * (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A)) := by
  first | exact @GlobalTheory.DetPowPairing.pairing_pow_proportional | exact GlobalTheory.DetPowPairing.pairing_pow_proportional | (intros; apply GlobalTheory.DetPowPairing.pairing_pow_proportional <;> assumption)
