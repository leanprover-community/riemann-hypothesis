module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open Matrix Topology

namespace GlobalTheory

theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) (by simpa only [Matrix.finrank_range_mulVecLin] using h)
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
