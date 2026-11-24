module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates : ∀ (D : D7), Inp D → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → 0 < Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∃ (b : Fin (fF D * P.a * P.d) → Matrix (Fin P.d) (Fin P.a) D.host.E) (k M : ℕ) (r : Fin k → Qbar) (s : Fin k → VC D P.a P.d), OnB D b ∧ LocBasis D p (YYl D (stdL D P.a) (stdL D P.d)) b ∧ 0 < M ∧ Nat.Coprime M p ∧ (∀ i, (M * Q) • s i ∈ LaB D (tor0 D ⊤ δ) b) ∧ (∀ i, ‖lam (r i)‖ ≤ (‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) ∧ P.W.Om g g' P.F = fun z => ∑ i, (r i : ℂ) * U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z := by
  first | exact @GlobalTheory.NormSum.kernel_eq_sum_translates | exact GlobalTheory.NormSum.kernel_eq_sum_translates | (intros; apply GlobalTheory.NormSum.kernel_eq_sum_translates <;> assumption)
