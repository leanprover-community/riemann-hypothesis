module

public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendLinearIndependentDifferentials
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

open scoped TensorProduct Polynomial

theorem _root_.GlobalTheory.T.extend_linear_independent_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) → ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧ LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  first | exact @GlobalTheory.kaehler_baseChange_independent_extend | exact GlobalTheory.kaehler_baseChange_independent_extend | (intros; apply GlobalTheory.kaehler_baseChange_independent_extend <;> assumption)
