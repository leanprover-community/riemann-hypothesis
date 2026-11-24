module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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

open UpperTheory.V.Lit.Geo
open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.hermitian_space_moment_identity :
    MomQuad := by
  intro E _ _ _ a ha L hL g p
  obtain ⟨-, h2⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have hP : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E),
      (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
    intro i j w
    have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => star (x i w)
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }, rfl⟩
    have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => x j w
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, rfl⟩
    exact (poly E a).mul_mem h1 h2
  have hS : ∀ (w : NumberField.InfinitePlace E) (i j : Fin a), HasSum
      (fun v : lat L g => (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) (pt (rt g) v.1) * p j i w).re)
      (gsum L (pg (fun x : Fin a → Cinf E => star (x i w) * x j w)) g * p j i w).re := by
    intro w i j
    exact Complex.hasSum_re ((((h2 _ (hP i j w)).1 g).hasSum).mul_right (p j i w))
  have hT := hasSum_sum (s := Finset.univ) fun w _ => hasSum_sum (s := Finset.univ) fun i _ =>
    hasSum_sum (s := Finset.univ) fun j _ => hS w i j
  have hq : ∀ x : Fin a → Cinf E, quad p x * gauss x = ∑ w : NumberField.InfinitePlace E, ∑ i, ∑ j,
      (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) x * p j i w).re := by
    intro x
    simp only [quad, Finset.sum_mul, pg, dotProduct, Matrix.vecMul, Finset.sum_apply, Complex.re_sum, Pi.mul_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.re_mul_ofReal]
    congr 1
    ring
  simp only [hq]
  rw [hT.tsum_eq]
  simp only [UpperTheory.V.Lit.Bor.trF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Complex.re_sum, Finset.sum_div, Pi.mul_apply]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.div_ofReal_re]
  congr 1
  change mean L _ g * _ = _
  rw [mean]
  ring
