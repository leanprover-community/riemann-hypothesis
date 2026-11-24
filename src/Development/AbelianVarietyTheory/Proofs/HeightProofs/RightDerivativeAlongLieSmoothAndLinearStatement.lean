module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  first | exact @GlobalTheory.SmoothForms.der_smooth_and_linear | exact GlobalTheory.SmoothForms.der_smooth_and_linear | (intros; apply GlobalTheory.SmoothForms.der_smooth_and_linear <;> assumption)
