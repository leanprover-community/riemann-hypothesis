module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
public import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA

@[expose] public section

open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem minpoly_int_coeff_zero_ne_zero {F : Type} [Field F] [NumberField F] (x : 𝓞 F) (hx : x ≠ 0) :
    (minpoly ℤ x).coeff 0 ≠ 0 := by
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.of_finite ℚ (x : F)) hxF
  have h2 : minpoly ℚ (x : F) = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ F hi
  rw [h2, coeff_map] at h1
  intro h; exact h1 (by rw [h, map_zero])

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natAbs_eq_minpoly_coeff_zero_pow {F : Type} [Field F] [NumberField F] (x : 𝓞 F) :
    ∃ r : ℕ, r * (minpoly ℤ x).natDegree = Module.finrank ℚ F ∧
      (Algebra.norm ℤ x).natAbs = ((minpoly ℤ x).coeff 0).natAbs ^ r := by
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow x
  have hm : (minpoly ℤ x).Monic := minpoly.monic (RingOfIntegers.isIntegral x)
  refine ⟨r, ?_, ?_⟩
  · rw [← ReciprocityTheory.ChartRestriction.T1.lat_cp_natDegree x, hr, hm.natDegree_pow]
  · have e : Algebra.norm ℤ x = (-1) ^ Module.finrank ℤ (𝓞 F) * (ReciprocityTheory.ChartRestriction.T1.lat_cp x).coeff 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]; rfl
    rw [e, hr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow]
    simp

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

end GlobalTheory.AV.AbVar
