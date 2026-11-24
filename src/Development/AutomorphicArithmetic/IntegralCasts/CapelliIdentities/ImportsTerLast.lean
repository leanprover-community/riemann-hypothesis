module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
