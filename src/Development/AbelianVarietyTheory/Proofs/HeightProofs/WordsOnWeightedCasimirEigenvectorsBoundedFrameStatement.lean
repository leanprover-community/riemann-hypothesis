module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.frame_bounded | exact GlobalTheory.TypeSum.CasBasis.frame_bounded | (intros; apply GlobalTheory.TypeSum.CasBasis.frame_bounded <;> assumption)
