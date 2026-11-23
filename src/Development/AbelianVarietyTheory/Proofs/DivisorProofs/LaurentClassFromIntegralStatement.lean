module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegral
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.laurent_class_from_integral : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧ ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  first | (exact @GlobalTheory.EtC.LiftWitness.lift_witness) | (exact GlobalTheory.EtC.LiftWitness.lift_witness) | (intros; apply GlobalTheory.EtC.LiftWitness.lift_witness  <;> assumption)
