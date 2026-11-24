module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
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

theorem _root_.GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  first | exact @GlobalTheory.NormVal.norm_mem_and_le | exact GlobalTheory.NormVal.norm_mem_and_le | (intros; apply GlobalTheory.NormVal.norm_mem_and_le <;> assumption)
