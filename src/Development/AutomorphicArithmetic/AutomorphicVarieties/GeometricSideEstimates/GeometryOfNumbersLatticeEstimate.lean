module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ScalingInvarianceOfGeometricFunctional
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

@[expose] public section

open UpperTheory.V.Lit.Geo NumberField

theorem UpperTheory.geometry_of_numbers_lattice_estimate :
    LatScale := by
  intro E _ _ _ a ha L hL
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)) :=
    InnerProductSpace.rclikeToReal ℂ _
  refine ⟨Module.finrank ℝ (EuclideanSpace ℂ (Fin a × InfinitePlace E)), fun g => ?_⟩
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨-, hrt, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v ∈ lat L (rt g), v ≠ 0 → 1 ≤ B * qf (pt (rt g) v) := ⟨_, hmin (rt g)⟩
  have hlat : lat L (rt g) = lat L g := by
    unfold lat
    rw [(hrt g).2.2]
  rw [hlat] at hB
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    (euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hM : (0 : ℝ) < max B 1 := lt_max_of_lt_right one_pos
  have key := UpperTheory.scaling_invariance_of_geometric_functional (lat L g) (EuclideanSpace ℂ (Fin a × InfinitePlace E)) φ
    (Real.sqrt (1 / max B 1)) (Real.sqrt_pos.2 (by positivity)) (fun v hv => by
      have h1 := hB v.1 v.2 (fun h => hv (Subtype.ext h))
      rw [← hφ] at h1
      apply Real.sqrt_le_iff.2
      refine ⟨norm_nonneg _, ?_⟩
      rw [div_le_iff₀ hM, mul_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  simpa only [hφ] using key
