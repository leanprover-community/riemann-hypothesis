module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm

    rw [hx, MultilinearMap.map_sum]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [RingHom.id_apply]

end GlobalTheory
