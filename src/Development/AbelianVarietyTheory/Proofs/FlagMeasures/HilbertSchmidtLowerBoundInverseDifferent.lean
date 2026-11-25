module

public import Formalism.HarderNarasimhan.StatementPl
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.DualBound

theorem opNorm_sq_le_hs {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by positivity
  have h : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hS, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i‖ ≤
        ∑ j, ‖M i j‖ * ‖x j‖ := by
      have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i =
          ∑ j, M i j * x j := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
      rw [this]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  calc _ ≤ (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem card_mul_geom_sq_le {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * ((∏ i, z i) ^ ((1 : ℝ) / (Fintype.card ι : ℝ))) ^ 2 ≤
      ∑ i, z i ^ 2 := by
  have hf : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (1 : ℝ) / (Fintype.card ι : ℝ)) (fun i => z i ^ 2)
    (fun _ _ => by positivity) (by simp [hf.ne']) (fun _ _ => by positivity)
  have hp : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), Finset.prod_pow, ← Finset.mul_sum] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp, mul_comm (1 / _ : ℝ), Real.rpow_mul hp,
    Real.rpow_natCast]
  calc _ ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left h hf.le
    _ = _ := by field_simp

end GlobalTheory.DualBound
