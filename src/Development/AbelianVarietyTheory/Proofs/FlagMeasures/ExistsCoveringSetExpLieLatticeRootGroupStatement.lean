module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoveringSetExpLieLatticeRootGroup
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

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exists_covering_set_exp_lie_lattice_rootGroup : ∀ (ι : Type) [Fintype ι] (N : ℕ) (R : Finset (Fin N × Fin N)) (Λ : Submodule ℤ (ι → R → ℂ)) (Ω₀ : Set (ι → R → ℂ)), (∀ q ∈ R, q.1 < q.2) → (∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) → MeasurableSet Ω₀ → MeasureTheory.IsAddFundamentalDomain Λ Ω₀ MeasureTheory.volume → MeasureTheory.volume Ω₀ ≠ ⊤ → DiscreteTopology Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ v, expT (ofRoots R (x v) - 1) * expT (ofRoots R (y v) - 1) = expT (ofRoots R (z v) - 1)) → ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω = MeasureTheory.volume Ω₀ ∧ ∀ c : ι → R → ℂ, ∃ x ∈ Λ, (fun v (q : R) => (expT (ofRoots R (x v) - 1) * ofRoots R (c v) : Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopV.Cover.cover | exact GlobalTheory.LoopV.Cover.cover | (intros; apply GlobalTheory.LoopV.Cover.cover <;> assumption)
