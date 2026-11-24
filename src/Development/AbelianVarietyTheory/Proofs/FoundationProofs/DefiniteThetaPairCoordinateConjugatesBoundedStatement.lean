module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBounded
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

theorem _root_.GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.ArchFree.coord.coord_conj_le | exact GlobalTheory.ArchFree.coord.coord_conj_le | (intros; apply GlobalTheory.ArchFree.coord.coord_conj_le <;> assumption)
