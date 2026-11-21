import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open GroundTheory.Automorphic.FourierWhittaker
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ConverseGL3NF

variable {K : Type} [Field K] [NumberField K]

local notation "A" => algebraMap K 𝔸[K]

theorem vecCoeff_one_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → K} (h : ξ ≠ 0) :
    vecCoeff (fun _ : ι → 𝔸[K] => (1 : ℂ)) ξ = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : ξ i ≠ 0 := hi
  obtain ⟨t, ht⟩ : ∃ t, adelicChar K t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact adelicChar_ne_one (K := K) (by ext t; simp [hc t])
  have hpa : pair ξ (Pi.single i (A (ξ i)⁻¹ * t)) = t := by
    rw [pair, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  have key := vecCoeff_translate (K := K) (ι := ι) (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    (Pi.single i (A (ξ i)⁻¹ * t)) ξ
  rw [hpa] at key
  have h1 : ((adelicChar K t : Circle) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
  have h2 : (1 - ((adelicChar K t : Circle) : ℂ)) * vecCoeff (fun _ : ι → 𝔸[K] => (1 : ℂ)) ξ = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))

theorem setIntegral_char_eq_zero {ι : Type*} [Fintype ι] {ξ : ι → K} (h : ξ ≠ 0) :
    ∫ y in vecDomain K ι, (adelicChar K (pair ξ y) : ℂ) ∂vecMeasure K ι = 0 := by
  have h' : -ξ ≠ 0 := neg_ne_zero.2 h
  have := vecCoeff_one_eq_zero h'
  simpa [vecCoeff, pair_neg_left] using this

omit [NumberField K] in
theorem countable_GL2' [Countable K] : Countable (GL (Fin 2) K) :=
  Function.Injective.countable (f := fun (γ : GL (Fin 2) K) (i j : Fin 2) => γ.val i j)
    fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)

theorem countable_field : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

theorem countable_NQ : Countable (NQ K) :=
  haveI : Countable K := countable_field
  haveI : Countable (GL (Fin 2) K) := countable_GL2'
  inferInstance





theorem continuous_uni {X : Type*} [TopologicalSpace X] {y z : X → 𝔸[K]} (hy : Continuous y)
    (hz : Continuous z) : Continuous fun t => (uni 0 (y t) (z t) : G3K K) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [uni, Function.comp_def] <;> first | exact continuous_const | assumption
  · show Continuous fun t => (!![1, -0, 0 * z t - y t; 0, 1, -z t; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

theorem continuous_lowM {X : Type*} [TopologicalSpace X] {c : X → 𝔸[K]} (hc : Continuous c) :
    Continuous fun t => (lowM (c t) : G3K K) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => ?_,
    continuous_pi fun a => continuous_pi fun b => ?_⟩
  · show Continuous fun t => (!![1, 0, 0; c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop
  · show Continuous fun t => (!![1, 0, 0; -c t, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K]) _ _
    fin_cases a <;> fin_cases b <;> simp <;> first | exact continuous_const | fun_prop

omit [NumberField K] in
theorem det_ne_zero (γ : GL (Fin 2) K) : γ.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero





end GlobalTheory.CompanionTheory.ConverseGL3NF
