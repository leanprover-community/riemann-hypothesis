module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentral
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

open GlobalTheory.CasimirOrder

theorem _root_.GlobalTheory.T.integralCasimirElement_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_central) | (exact GlobalTheory.CasimirOrder.casimir_central) | (intros; apply GlobalTheory.CasimirOrder.casimir_central  <;> assumption)
