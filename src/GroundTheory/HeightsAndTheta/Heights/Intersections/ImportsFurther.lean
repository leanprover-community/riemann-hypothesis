module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherRest
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTer
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PullbackVanishingOfNullCycle.proof (hElim : PullbackEliminationOfVariable.Statement) : PullbackVanishingOfNullCycle.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' J' n Ψ hv hP' hP hΨ hJ hJP
  obtain ⟨h, a, hha, hhP, hvan⟩ := hElim K ι K' ι' κ v P' J' n hv hP' hP hJ hJP
  have hJh : IsMultiHomogIdeal (Ideal.span {h}) :=
    ⟨{h}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hha⟩, rfl⟩
  have hJhP : ¬ Ideal.span {h} ≤ imageZ v P' := fun hle => hhP (hle (Ideal.subset_span rfl))
  refine measure_mono_null ?_ (projB_null Ψ hP hΨ hJh hJhP)
  rintro y ⟨z', hz'P, hz'J, -, -, -, hΨy⟩
  set w : (Σ k, ι k) → ℂ := fun p => z' (v p) with hw
  have hw1 : (Ψ (segre w) 0)⁻¹ * Ψ (segre w) 0 = 1 := by
    have := congrFun hΨy 0
    simpa [map_smul] using this
  have h0 : Ψ (segre w) 0 ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre w) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre w) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hwP : w ∈ mcPts (imageZ v P') := IntersectionWithSection.comp_mem_mcPts hv hz'P
  have hwh : w ∈ mcPts (Ideal.span {h}) := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hvan z' hz'P hz'J, mul_zero]
  refine ⟨fun p => c p.1 * w p, mcPts_smul hP.2.1.2.1 c hc hwP, mcPts_smul hJh c hc hwh, ?_⟩
  rw [segre_smul, hpc]
  exact hΨy

end GroundTheory.Heights₂.Heights.Inter
