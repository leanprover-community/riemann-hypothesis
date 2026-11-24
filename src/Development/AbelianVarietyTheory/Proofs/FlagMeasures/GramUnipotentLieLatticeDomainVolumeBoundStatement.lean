module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentLieLatticeDomainVolumeBound
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

theorem _root_.GlobalTheory.T.gramUnipotentLieLattice_domain_volume_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → 1 ≤ B → (∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix I J).det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∀ Λ : Submodule ℤ (ι → roots (ptMat p) → ℂ), (∀ c, c ∈ Λ ↔ ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧ ∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.IsAddFundamentalDomain Λ Ω MeasureTheory.volume ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) * ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  first | exact @GlobalTheory.LieCovol.lie_lattice_domain | exact GlobalTheory.LieCovol.lie_lattice_domain | (intros; apply GlobalTheory.LieCovol.lie_lattice_domain <;> assumption)
