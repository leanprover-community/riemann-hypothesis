module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option backward.isDefEq.respectTransparency false

@[expose] public section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

theorem GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by
  intro X _ _ _
  set b := Module.finBasis ℝ X
  let L : Fin (Module.finrank ℝ X) → ℂ →L[ℝ] X →L[ℝ] ℂ := fun i =>
    StrongDual.smulRightL ℝ X ℂ (LinearMap.toContinuousLinearMap (b.coord i))
  refine ⟨∑ i, ‖L i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro g hg n z
  have hsm : ∀ i, ContDiff ℝ ∞ (fun w => fderiv ℝ g w (b i)) := fun i =>
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdec : fderiv ℝ g = fun w => ∑ i, (L i ∘ (fun w => fderiv ℝ g w (b i))) w := by
    funext w
    apply ContinuousLinearMap.ext
    intro v
    have hv := b.sum_repr v
    simp [L, ContinuousLinearMap.sum_apply]

    conv_lhs => rw [← hv, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Complex.real_smul]
  have key : iteratedFDeriv ℝ n (fderiv ℝ g) z =
      ∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z := by
    conv_lhs => rw [hdec]
    rw [iteratedFDeriv_sum (fun i _ => ((L i).contDiff.comp (hsm i)).of_le (by exact_mod_cast le_top)),
      Finset.sum_apply]
  rw [← norm_iteratedFDeriv_fderiv, key]
  calc ‖∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact (L i).norm_iteratedFDeriv_comp_left (hsm i).contDiffAt (by exact_mod_cast le_top)
    _ ≤ ∑ i, (∑ j, ‖L j‖) * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖L j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ = (∑ j, ‖L j‖) * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        rw [Finset.mul_sum]
