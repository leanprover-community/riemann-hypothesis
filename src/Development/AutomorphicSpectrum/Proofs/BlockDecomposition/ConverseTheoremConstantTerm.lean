import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ConverseGL3

local notation "A" => algebraMap ℚ 𝔸[ℚ]

theorem vecCoeff_one_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → ℚ} (h : ξ ≠ 0) :
    vecCoeff (fun _ : ι → 𝔸[ℚ] => (1 : ℂ)) ξ = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : ξ i ≠ 0 := hi
  obtain ⟨t, ht⟩ : ∃ t, adelicChar ℚ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact adelicChar_ne_one (K := ℚ) (by ext t; simp [hc t])
  have hpa : pair ξ (Pi.single i (A (ξ i)⁻¹ * t)) = t := by
    rw [pair, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  have key := vecCoeff_translate (K := ℚ) (ι := ι) (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    (Pi.single i (A (ξ i)⁻¹ * t)) ξ
  rw [hpa] at key
  have h1 : ((adelicChar ℚ t : Circle) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
  have h2 : (1 - ((adelicChar ℚ t : Circle) : ℂ)) * vecCoeff (fun _ : ι → 𝔸[ℚ] => (1 : ℂ)) ξ = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))

theorem setIntegral_char_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → ℚ} (h : ξ ≠ 0) :
    ∫ y in vecDomain ℚ ι, (adelicChar ℚ (pair ξ y) : ℂ) ∂vecMeasure ℚ ι = 0 := by
  have h' : -ξ ≠ 0 := neg_ne_zero.2 h
  have := vecCoeff_one_eq_zero h'
  simpa [vecCoeff, pair_neg_left] using this

local instance countable_GL2 : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable (f := fun (γ : GL (Fin 2) ℚ) (i j : Fin 2) => γ.val i j)
    fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)





theorem continuous_uni {X : Type*} [TopologicalSpace X] {y z : X → 𝔸[ℚ]} (hy : Continuous y)
    (hz : Continuous z) : Continuous fun t => (uni 0 (y t) (z t) : G3) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [uni, Function.comp_def] <;> first | exact continuous_const | assumption
  · show Continuous fun t => (!![1, -0, 0 * z t - y t; 0, 1, -z t; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

theorem continuous_lowM {X : Type*} [TopologicalSpace X] {c : X → 𝔸[ℚ]} (hc : Continuous c) :
    Continuous fun t => (lowM (c t) : G3) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · show Continuous fun t => (!![1, 0, 0; c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop
  · show Continuous fun t => (!![1, 0, 0; -c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

theorem det_ne_zero (γ : GL (Fin 2) ℚ) : γ.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero





end GlobalTheory.CompanionTheory.ConverseGL3
