module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
