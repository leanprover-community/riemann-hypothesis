module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt
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

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | exact GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | (intros; apply GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt <;> assumption)
