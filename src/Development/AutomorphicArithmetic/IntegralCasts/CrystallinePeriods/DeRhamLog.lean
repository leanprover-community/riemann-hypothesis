module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

@[expose] public section

noncomputable section

open Ideal Polynomial

namespace Reformulated.AutPerF

universe u v

section Trunc

variable {B : Type*} [CommRing B] [Algebra ℚ B]

end Trunc

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace BdRPlus

theorem eval_pow_eq_zero {x : BdRPlus p R} (hx : theta p R x = 0) (n : ℕ) :
    eval p R n x ^ n = 0 := evalₐ_pow_eq_zero _ ((theta_eq_zero_iff x).1 hx) n

theorem eval_two_log (u : BdRPlus p R) (hu : theta p R u = 1) :
    eval p R 2 (log u hu) = eval p R 2 (u - 1) := by
  rw [eval_log, truncLog, Finset.sum_range_succ, Finset.sum_range_one,
    eval_pow_eq_zero (x := u - 1) (by simp [hu]) 2]
  simp

def logTeich (η : tateModule p R) : BdRPlus p R :=
  log (algebraMap (Ainf p R) _ (Ainf.teich p η.1)) (by
    rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap,
      Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, map_one])

theorem p_mul_inv : (p : BdRPlus p R) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]

end BdRPlus

end Reformulated.AutPerF
