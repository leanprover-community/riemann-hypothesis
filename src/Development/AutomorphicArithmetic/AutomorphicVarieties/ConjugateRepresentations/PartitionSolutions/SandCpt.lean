module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Cj.A.sandCpt :
    SandCpt := by
  intro E _ _ a
  have hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) := by
    refine Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _
    change Continuous fun g : GL (Fin a) (Cinf E) =>
      (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))
    exact (Units.continuous_val.mul continuous_const).mul Units.continuous_val.star
  refine ⟨hcont, fun K hK hKc => ?_⟩
  obtain ⟨C, hC⟩ := boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)
  have hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C} := by
    have h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C) := isCompact_closedBall _ _
    have e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C} := by
      ext m; simp
    rw [e] at h
    exact h
  have hT := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  refine hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩
  · exact hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)
  · refine hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_
    have e : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e]
    exact Set.mem_insert _ _
