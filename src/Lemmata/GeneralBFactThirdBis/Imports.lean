module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

universe u_1

namespace Bl.general_b_fact_third_bis

theorem goal1 {E : Type u_1} [Field E] [NumberField E] (φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (hL : L.FG) (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    IsIntegral ℤ M.trace := by
  classical
  have : Module.Finite ℤ (L.restrictScalars ℤ) := Module.Finite.iff_fg.mpr hL.restrictScalars
  let f : Module.End ℤ (L.restrictScalars ℤ) :=
    ((Matrix.mulVecLin M).restrictScalars ℤ).restrict fun x hx => hM x hx
  obtain ⟨p, hpm, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ f
  have hpow (k : ℕ) (x : L.restrictScalars ℤ) : ((f ^ k) x : Fin n → E) = (M ^ k).mulVec (x : Fin n → E) := by
    induction k generalizing x with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_apply_eq_comp, ih, pow_succ, ← Matrix.mulVec_mulVec]; rfl
  have hz : Polynomial.aeval M p = 0 := by
    have hlin : Matrix.mulVecLin (Polynomial.aeval M p) = 0 := LinearMap.ext_on hspan fun x hx => by
      have h := congrArg (fun h : Module.End ℤ (L.restrictScalars ℤ) => (h ⟨x, hx⟩ : Fin n → E)) hp0
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
        Submodule.coe_sum, Submodule.coe_smul, hpow, LinearMap.zero_apply, Submodule.coe_zero] at h
      rw [LinearMap.zero_apply, Matrix.mulVecLin_apply, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
      simpa only [Matrix.smul_mulVec] using h
    ext i j
    simpa [Matrix.mulVec_single_one] using congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
  have hN : Polynomial.aeval (M.map φ) p = 0 := by
    have h2 := congrArg (φ.mapMatrix (m := Fin n)) hz
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h2
    rw [Polynomial.aeval_def]
    convert h2 using 2 <;> first | exact RingHom.ext_int _ _ | rfl
  have hint : IsIntegral ℤ (φ M.trace) := by
    rw [AddMonoidHom.map_trace φ M, Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun r hr => ⟨p, hpm, ?_⟩
    have hsp := Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.mem_roots'.mp hr).2
    have h1 := spectrum.subset_polynomial_aeval (M.map φ) (p.map (algebraMap ℤ ℂ)) ⟨r, hsp, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hN] at h1
    rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with _ | _
    · exact absurd hsp (by rw [spectrum.mem_iff, not_not]; exact isUnit_of_subsingleton _)
    · rw [spectrum.zero_eq, Set.mem_singleton_iff] at h1
      simpa [Polynomial.eval_map, Polynomial.aeval_def] using h1
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hint

end Bl.general_b_fact_third_bis
