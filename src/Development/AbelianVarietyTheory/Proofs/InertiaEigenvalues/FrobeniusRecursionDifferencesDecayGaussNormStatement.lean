module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusRecursionDifferencesDecayGaussNorm
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

open PowerSeries GlobalTheory.BK Filter Topology

theorem _root_.GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  first | exact @GlobalTheory.BK.frob_recursion_decay | exact GlobalTheory.BK.frob_recursion_decay | (intros; apply GlobalTheory.BK.frob_recursion_decay <;> assumption)
