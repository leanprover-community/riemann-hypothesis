module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernConj

theorem charpolyRev_map_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) : M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_conj {R : Type} [CommRing R] {m : ℕ} (P Q M : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) : (P * M * Q).charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix (Fin m) (Fin m) (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q).map Polynomial.C
      = P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_mul, Matrix.map_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

theorem chernPoly_conj_subst : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  intro n r F v v' J S hS h k
  set φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) with hφ
  have hP : (S⁻¹).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : curvPoly F v = (S⁻¹).map C * (curvPoly F v').map φ * S.map C := by
    refine Matrix.ext fun i j => ?_

    simp only [curvPoly, h, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, aeval_C, aeval_X, hφ, MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => enter [2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q, 2, c]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hN : -curvPoly F v = (S⁻¹).map C * (-curvPoly F v').map (φ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C := by
    rw [hA, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    · rfl
    · exact fun a => map_neg φ a
  unfold chernPoly
  rw [hN, charpolyRev_conj _ _ _ hP, ← charpolyRev_map_hom, Polynomial.coeff_map]
  rfl

end GlobalTheory.ChernConj
