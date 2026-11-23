module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isCompact_entryBall (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by
  have h : IsCompact (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have e : {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} =
      (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
        Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) := by
    ext M
    constructor
    · intro hM i _ j _
      have := hM i j
      rw [Matrix.sub_apply] at this
      exact mem_closedBall_iff_norm.2 this
    · intro hM i j
      have := mem_closedBall_iff_norm.1 (hM i (Set.mem_univ _) j (Set.mem_univ _))
      rw [Matrix.sub_apply]
      exact this
  rw [e]
  exact h

theorem isCompact_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  have hS := isCompact_entryBall L n r
  have hS' := hS.image MulOpposite.continuous_op
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  have e : (congK L n r h0 h1 : Set (GL (Fin n) L)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) L) ⁻¹'
        ({M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} ×ˢ
          (MulOpposite.op '' {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r})) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      Set.mem_image, Set.mem_setOf_eq, MulOpposite.op_inj, exists_eq_right]
    exact ⟨fun hk => ⟨fun i j => (hk i j).1, fun i j => (hk i j).2⟩,
      fun hk i j => ⟨hk.1 i j, hk.2 i j⟩⟩
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CartGL
