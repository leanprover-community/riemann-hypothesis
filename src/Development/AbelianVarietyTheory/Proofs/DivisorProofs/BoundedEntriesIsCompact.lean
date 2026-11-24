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

namespace GlobalTheory.BoundedUnitsCompact

theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
