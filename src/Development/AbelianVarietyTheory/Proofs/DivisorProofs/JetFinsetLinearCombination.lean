module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem GlobalTheory.ColNorms.jetC_sum_mul : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  intro ι _ a b cD α R c F hF m
  have key : ∀ (k : ℕ) (v : Fin k → VCx ι a b),
      iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v =
        ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v := by
    intro k v
    have hC : ∀ i ∈ R, ContDiff ℂ k (F i) := fun i hi =>
      GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _
    have h1 := iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k)
      (fun i hi => contDiff_const.mul (hC i hi))
    rw [h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 := iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0)
      (hC i hi).contDiffAt
    simp only [smul_eq_mul] at h2
    rw [h2]
    simp
  unfold jetC derivAt0
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
