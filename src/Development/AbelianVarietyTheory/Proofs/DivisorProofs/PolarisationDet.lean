module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PolDet

theorem det_sum_smul_eq {D : ℕ} (x : Fin D → ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    (∑ i, x i • H i).det =
      ∑ m : Fin D → Fin D, (∏ l, x (m l)) * (Matrix.of fun j l => H (m l) j l).det := by
  simp only [Matrix.det_apply', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem coeff_eq {D : ℕ} (m : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      if Function.Surjective m then 1 else 0 := by
  classical
  set T := Finset.univ.image m with hT
  have h1 : ∀ S : Finset (Fin D), ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      (-1 : ℂ) ^ D * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) := by
    intro S
    rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_ite, mul_one,
      mul_zero, Finset.mem_sdiff, Finset.mem_univ, true_and, hT, Finset.mem_image]
    congr 1
    apply propext
    constructor
    · rintro h i hi ⟨l, rfl⟩
      exact hi (h l trivial)
    · intro h l _
      by_contra hl
      exact h (m l) hl ⟨l, rfl⟩
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card *
      ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) =
      ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    simp [Finset.prod_const]
  have h3 : ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) =
      if Function.Surjective m then (-1 : ℂ) ^ D else 0 := by
    have : ∀ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if i ∈ T then (-1 : ℂ) else 0 := by
      intro i; by_cases hi : i ∈ T <;> simp [hi]
    simp_rw [this]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_implies,
      hT, Finset.mem_image, true_and]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [h1, mul_left_comm _ ((-1 : ℂ) ^ D), ← Finset.mul_sum, h2, h3]
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

theorem polarisation_det (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det =
      ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  classical
  simp_rw [det_sum_smul_eq, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coeff_eq, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun τ : Equiv.Perm (Fin D) => (τ : Fin D → Fin D)) ?_ ?_ ?_ ?_
  · intro τ _
    simpa using τ.surjective
  · intro τ _ σ _ h
    exact DFunLike.coe_injective h
  · intro m hm
    have hs : Function.Surjective m := by simpa using hm
    exact ⟨Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, by simp, rfl⟩
  · intro τ _
    rfl

end GlobalTheory.PolDet
