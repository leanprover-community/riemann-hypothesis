module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
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

open UpperTheory.V.Cj.A UpperTheory.V.Lit
open scoped ContDiff

theorem UpperTheory.V.Cj.A.partMem :
    PartMem := by
  intro Γ V S I _ _ _ _ d G φ hφ q c
  rw [Dr.Geo.mem_Om]
  intro s
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨N, hN, hfin⟩ := hφ.locFin s p hp
    have hsum : ContDiffAt ℝ ∞ (fun x => ∑ i ∈ hfin.toFinset, φ i s x • (c i).1 s x) p :=
      ContDiffAt.sum fun i _ =>
        ((hφ.smooth i s).contDiffAt (G.isOpen.mem_nhds hp)).smul (Dr.Geo.contDiffAt_Om (c i) s hp)
    refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hN] with x hx
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hx, fun h => hi ?_⟩
    simp only [h, zero_smul]
  · have h : ∀ i : I, φ i s p • (c i).1 s p = 0 := fun i => by
      rw [((c i).2 s).2 p hp, smul_zero]
    simp only [h, finsum_zero]
