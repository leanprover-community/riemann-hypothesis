import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA.unipotentTranslateContinuity

variable {K : Type} [Field K] [NumberField K]

local notation "𝔞" => algebraMap K 𝔸[K]

theorem psi_add (a b : 𝔸[K]) :
    (adelicChar K (a + b) : ℂ) = (adelicChar K a : ℂ) * (adelicChar K b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem psi_rat (q : K) : (adelicChar K (𝔞 q) : ℂ) = 1 := by
  rw [adelicChar_algebraMap, Circle.coe_one]

theorem psi_zero : (adelicChar K 0 : ℂ) = 1 := by
  rw [AddChar.map_zero_eq_one, Circle.coe_one]

theorem norm_psi (a : 𝔸[K]) : ‖(adelicChar K a : ℂ)‖ = 1 := Circle.norm_coe _

theorem exists_psi_ne_one : ∃ b : 𝔸[K], (adelicChar K b : ℂ) ≠ 1 := by
  by_contra h
  push Not at h
  refine adelicChar_ne_one (K := K) (DFunLike.ext _ _ fun b => ?_)
  rw [AddChar.one_apply]
  ext
  simpa using h b

theorem psi_comb {A B C D : 𝔸[K]} (e : A + B = C + D) (w : ℂ) :
    (adelicChar K A : ℂ) * w * (adelicChar K B : ℂ) =
      (adelicChar K C : ℂ) * (w * (adelicChar K D : ℂ)) := by
  calc (adelicChar K A : ℂ) * w * (adelicChar K B : ℂ) = w * (adelicChar K (A + B) : ℂ) := by
        rw [psi_add]; ring
    _ = w * (adelicChar K (C + D) : ℂ) := by rw [e]
    _ = _ := by rw [psi_add]; ring

def splitAt {ι : Type*} [DecidableEq ι] (i : ι) : ι ≃ {j // j ≠ i} ⊕ Unit where
  toFun j := if h : j = i then Sum.inr () else Sum.inl ⟨j, h⟩
  invFun := Sum.elim Subtype.val fun _ => i
  left_inv j := by
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨j, hj⟩ | ⟨⟩
    · simp [hj]
    · simp

theorem setIntegral_eq_zero_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → 𝔸[K]) → ℂ} (hc : Continuous F) (i : ι) {r : K} (hr : r ≠ 0)
    (hF : ∀ y s, F (y + Pi.single i s) = (adelicChar K (𝔞 r * s) : ℂ) * F y) :
    ∫ y in vecDomain K ι, F y ∂vecMeasure K ι = 0 := by
  rw [FourierWhittaker.setIntegral_vecDomain_sum (splitAt i) hc]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
  let G : (Unit → 𝔸[K]) → ℂ := fun y => F fun j => Sum.elim x y (splitAt i j)
  show ∫ y in vecDomain K Unit, G y ∂vecMeasure K Unit = 0
  have hvec : ∀ (y a : Unit → 𝔸[K]), (fun j => Sum.elim x (y + a) (splitAt i j)) =
      (fun j => Sum.elim x y (splitAt i j)) + Pi.single i (a ()) := by
    intro y a
    funext j
    by_cases h : j = i
    · subst h; simp [splitAt]
    · simp [splitAt, h]
  have hG : ∀ y a, G (y + a) = (adelicChar K (𝔞 r * a ()) : ℂ) * G y := by
    intro y a
    simp only [G, hvec, hF]
  have hper : ∀ ξ ∈ FourierWhittaker.vecLattice K Unit, ∀ y, G (ξ + y) = G y := by
    intro ξ hξ y
    obtain ⟨η, rfl⟩ := FourierWhittaker.mem_vecLattice.1 hξ
    rw [add_comm, hG]
    show (adelicChar K (𝔞 r * 𝔞 (η ())) : ℂ) * G y = G y
    rw [← map_mul, psi_rat, one_mul]
  obtain ⟨b, hb⟩ := exists_psi_ne_one (K := K)
  have h1 := FourierWhittaker.setIntegral_comp_add (fun _ => 𝔞 r⁻¹ * b) hper
  have hrb : 𝔞 r * (𝔞 r⁻¹ * b) = b := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]
  simp only [hG, hrb] at h1
  rw [integral_const_mul] at h1
  have h2 : ((adelicChar K b : ℂ) - 1) * ∫ y in vecDomain K Unit, G y ∂vecMeasure K Unit = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hb)

theorem setIntegral_eq_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → 𝔸[K]) → ℂ}
    (hF : ∀ y i s, F (y + Pi.single i s) = F y) :
    ∫ y in vecDomain K ι, F y ∂vecMeasure K ι = F 0 := by
  have key : ∀ y, F y = F 0 := by
    intro y
    have : ∀ S : Finset ι, F (∑ i ∈ S, Pi.single i (y i)) = F 0 := by
      intro S
      refine Finset.induction_on S (by simp) ?_
      intro a S ha ih
      rw [Finset.sum_insert ha, add_comm, hF, ih]
    rw [← this Finset.univ, Finset.univ_sum_single]
  rw [setIntegral_congr_fun FourierWhittaker.measurableSet_vecDomain (fun y _ => key y),
    setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain, ENNReal.toReal_one,
    one_smul]


instance countable_field : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable

instance countable_GL2 : Countable (GL (Fin 2) K) := by
  have : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    fun a b h => Units.ext h

instance countable_NQ : Countable (NQ K) := Quotient.countable

theorem continuous_uni {X : Type*} [TopologicalSpace X] {a b c : X → 𝔸[K]} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) : Continuous fun x => (uni (a x) (b x) (c x) : G3K K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, a x, b x; 0, 1, c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x =>
      (!![1, -a x, a x * c x - b x; 0, 1, -c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_lowM {X : Type*} [TopologicalSpace X] {a : X → 𝔸[K]} (ha : Continuous a) :
    Continuous fun x => lowM (a x) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, 0, 0; a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x => (!![1, 0, 0; -a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem val_uni (x y z : 𝔸[K]) :
    ((uni x y z : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) = !![1, x, y; 0, 1, z; 0, 0, 1] := rfl

theorem val_lowM (c : 𝔸[K]) :
    ((lowM c : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) = !![1, 0, 0; c, 1, 0; 0, 0, 1] := rfl

theorem diagonal_embed_GL2_matrix (γ : GL (Fin 2) K) :
    ((diaK (e1 K γ) : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) =
      !![𝔞 (γ.val 0 0), 𝔞 (γ.val 0 1), 0; 𝔞 (γ.val 1 0), 𝔞 (γ.val 1 1), 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, b1M]

theorem val_dia_e2sw (γ : GL (Fin 2) K) :
    ((diaK (e2 K γ * sw K) : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) =
      !![0, 1, 0; 𝔞 (γ.val 0 0), 0, 𝔞 (γ.val 0 1); 𝔞 (γ.val 1 0), 0, 𝔞 (γ.val 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2, b2M, sw, Matrix.mul_apply, Fin.sum_univ_three]

theorem lowM_zero : lowM (0 : 𝔸[K]) = 1 := by
  apply Units.ext
  rw [val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uni_zero : (uni 0 0 0 : G3K K) = 1 := by
  apply Units.ext
  rw [val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem inv_rel (γ : GL (Fin 2) K) (i j : Fin 2) :
    𝔞 ((γ⁻¹).val i 0) * 𝔞 (γ.val 0 j) + 𝔞 ((γ⁻¹).val i 1) * 𝔞 (γ.val 1 j) =
      if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => 𝔞 (X i j)) (Units.inv_mul γ)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply] at this
  rw [this]
  split_ifs <;> simp

theorem heisenberg_lower_commute_corner (c x t s : 𝔸[K]) :
    lowM c * uni 0 x (t + s) = uni 0 0 s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem heisenberg_lower_commute_middle (c x t s : 𝔸[K]) :
    lowM c * uni 0 (x + s) t = uni 0 s (c * s) * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem hH_c (c x t s : 𝔸[K]) :
    lowM (c + s) * uni 0 x t = lowM s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring



theorem GL2_embed_commute_corner (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e1 K γ) * uni 0 0 s = uni 0 (𝔞 (γ.val 0 1) * s) (𝔞 (γ.val 1 1) * s) * diaK (e1 K γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem GL2_embed_commute_middle (γ : GL (Fin 2) K) (s w : 𝔸[K]) :
    diaK (e1 K γ) * uni 0 s w = uni 0 (𝔞 (γ.val 0 0) * s + 𝔞 (γ.val 0 1) * w)
      (𝔞 (γ.val 1 0) * s + 𝔞 (γ.val 1 1) * w) * diaK (e1 K γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_ne_zero2 (γ : GL (Fin 2) K) : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 ≠ 0 := by
  have h := congrArg Matrix.det (Units.mul_inv γ)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem dU_c (γ : GL (Fin 2) K) (h11 : γ.val 1 1 = 0) (s : 𝔸[K]) :
    diaK (e1 K γ) * lowM s = uni (𝔞 (γ.val 0 1 / γ.val 1 0) * s) 0 0 * diaK (e1 K γ) := by
  have h10 : γ.val 1 0 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h11] at this; simp at this
  have hq : 𝔞 (γ.val 0 1 / γ.val 1 0) * 𝔞 (γ.val 1 0) = 𝔞 (γ.val 0 1) := by
    rw [← map_mul, div_mul_cancel₀ _ h10]
  generalize 𝔞 (γ.val 0 1 / γ.val 1 0) = A at hq ⊢
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h11] <;>
    first | linear_combination s * hq | linear_combination -s * hq | ring1

theorem GL2_swap_embed_commute_corner (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e2 K γ * sw K) * uni 0 0 s =
      uni (𝔞 ((γ⁻¹).val 1 0) * s) (𝔞 ((γ⁻¹).val 1 1) * s) 0 * diaK (e2 K γ * sw K) := by
  have r0 := inv_rel γ 1 0
  have r1 := inv_rel γ 1 1
  simp only [Fin.isValue, one_ne_zero, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

theorem dV_c (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e2 K γ * sw K) * lowM s =
      uni (𝔞 ((γ⁻¹).val 0 0) * s) (𝔞 ((γ⁻¹).val 0 1) * s) 0 * diaK (e2 K γ * sw K) := by
  have r0 := inv_rel γ 0 0
  have r1 := inv_rel γ 0 1
  simp only [Fin.isValue, zero_ne_one, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

theorem GL2_swap_embed_commute_middle (γ : GL (Fin 2) K) (h10 : γ.val 1 0 = 0) (s w : 𝔸[K]) :
    diaK (e2 K γ * sw K) * uni 0 s w =
      uni 0 (𝔞 (γ.val 1 1)⁻¹ * w) (𝔞 (γ.val 0 0 / γ.val 1 1) * s) * diaK (e2 K γ * sw K) := by
  have h11 : γ.val 1 1 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h10] at this; simp at this
  have q1 : 𝔞 (γ.val 1 1)⁻¹ * 𝔞 (γ.val 1 1) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h11, map_one]
  have q2 : 𝔞 (γ.val 0 0 / γ.val 1 1) * 𝔞 (γ.val 1 1) = 𝔞 (γ.val 0 0) := by
    rw [← map_mul, div_mul_cancel₀ _ h11]
  generalize 𝔞 (γ.val 1 1)⁻¹ = A1 at q1 ⊢
  generalize 𝔞 (γ.val 0 0 / γ.val 1 1) = A2 at q2 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10] <;>
    first | linear_combination w * q1 | linear_combination -w * q1 |
      linear_combination s * q2 | linear_combination -s * q2 | ring1

end Ad3.K.GA.unipotentTranslateContinuity
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing Classical

namespace Ad3.K.GA.CtvP

variable {K : Type} [Field K] [NumberField K]

open Ad3.K.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap K 𝔸[K]

theorem W_shift {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V) {D L X : G3K K}
    {a b z : 𝔸[K]} (hDL : D * L = uni a b z * D) (g : G3K K) :
    W (D * (L * X * g)) = (adelicChar K (a + z) : ℂ) * W (D * (X * g)) := by
  have e : D * (L * X * g) = uni a b z * (D * (X * g)) := by
    calc D * (L * X * g) = D * L * (X * g) := by simp only [mul_assoc]
      _ = uni a b z * D * (X * g) := by rw [hDL]
      _ = uni a b z * (D * (X * g)) := mul_assoc _ _ _
  rw [e, hV.psi W hW]






theorem out_rel (γ : GL (Fin 2) K) : γ * ((Quotient.mk _ γ : NQ K).out)⁻¹ ∈ (nU K) :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk _ γ : NQ K)))


theorem inv_rel_q (γ : GL (Fin 2) K) (i j : Fin 2) :
    (γ⁻¹).val i 0 * γ.val 0 j + (γ⁻¹).val i 1 * γ.val 1 j = if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X i j) (Units.inv_mul γ)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this


theorem inverse_lower_left_ne_zero (γ : GL (Fin 2) K) (h10 : γ.val 1 0 ≠ 0) : (γ⁻¹).val 1 0 ≠ 0 := by
  intro hN
  have r10 := inv_rel_q γ 1 0
  have r11 := inv_rel_q γ 1 1
  rw [hN, zero_mul, zero_add] at r10 r11
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r11
  rcases r10 with h | h
  · rw [h, zero_mul] at r11; exact zero_ne_one r11
  · exact h10 h

theorem diag_ne_zero (γ : GL (Fin 2) K) (h10 : γ.val 1 0 = 0) :
    γ.val 0 0 ≠ 0 ∧ γ.val 1 1 ≠ 0 := by
  have hd := det_ne_zero2 γ
  rw [h10, mul_zero, sub_zero] at hd
  exact mul_ne_zero_iff.1 hd

theorem inv_upper (γ : GL (Fin 2) K) (h10 : γ.val 1 0 = 0) :
    (γ⁻¹).val 1 0 = 0 ∧ (γ⁻¹).val 0 0 * γ.val 0 0 = 1 := by
  have r10 := inv_rel_q γ 1 0
  have r00 := inv_rel_q γ 0 0
  rw [h10, mul_zero, add_zero] at r10 r00
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r00
  exact ⟨r10.resolve_right (diag_ne_zero γ h10).1, r00⟩




def chiH (ξ : Fin 2 → K) (y : Fin 3 → 𝔸[K]) : ℂ :=
  (adelicChar K (-(𝔞 (ξ 0) * y 0 + 𝔞 (ξ 1) * y 1)) : ℂ)

theorem continuous_chiH (ξ : Fin 2 → K) : Continuous (chiH ξ) :=
  continuous_subtype_val.comp (continuous_adelicChar.comp (by fun_prop))

theorem continuous_hH : Continuous fun y : Fin 3 → 𝔸[K] => lowM (y 0) * uni 0 (y 1) (y 2) :=
  (continuous_lowM (continuous_apply 0)).mul
    (continuous_uni continuous_const (continuous_apply 1) (continuous_apply 2))

def fU (W : G3K K → ℂ) (g : G3K K) (ξ : Fin 2 → K) (γ : GL (Fin 2) K) (y : Fin 3 → 𝔸[K]) : ℂ :=
  W (diaK (e1 K γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

def fV (W : G3K K → ℂ) (g : G3K K) (ξ : Fin 2 → K) (γ : GL (Fin 2) K) (y : Fin 3 → 𝔸[K]) : ℂ :=
  W (diaK (e2 K γ * sw K) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

theorem continuous_fU {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) (hC : ContW K) {W : G3K K → ℂ}
    (hW : W ∈ V) (g : G3K K) (ξ : Fin 2 → K) (γ : GL (Fin 2) K) : Continuous (fU W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

theorem continuous_fV {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) (hC : ContW K) {W : G3K K → ℂ}
    (hW : W ∈ V) (g : G3K K) (ξ : Fin 2 → K) (γ : GL (Fin 2) K) : Continuous (fV W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

section shifts

variable {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V) (g : G3K K)
  (ξ : Fin 2 → K) (γ : GL (Fin 2) K)
include hV hW

theorem shiftU_alt_alt (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fU W g ξ γ (y + Pi.single 2 s) = (adelicChar K (𝔞 (γ.val 1 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 2 = y 2 + s := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

theorem shiftU_alt (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fU W g ξ γ (y + Pi.single 1 s) =
      (adelicChar K (𝔞 (γ.val 1 0 - ξ 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_embed_commute_middle γ s (y 0 * s))]
  refine psi_comb ?_ _
  rw [h11, map_sub, map_zero]
  ring

theorem shiftU_c (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fU W g ξ γ (y + Pi.single 0 s) =
      (adelicChar K (𝔞 (γ.val 0 1 / γ.val 1 0 - ξ 0) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dU_c γ h11 s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

theorem shiftV_alt (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fV W g ξ γ (y + Pi.single 2 s) = (adelicChar K (𝔞 ((γ⁻¹).val 1 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[K]) 2 = y 2 + s := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

theorem shiftV_c (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fV W g ξ γ (y + Pi.single 0 s) =
      (adelicChar K (𝔞 ((γ⁻¹).val 0 0 - ξ 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[K]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dV_c γ s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

theorem shiftV_alt_alt (h10 : γ.val 1 0 = 0) (y : Fin 3 → 𝔸[K]) (s : 𝔸[K]) :
    fV W g ξ γ (y + Pi.single 1 s) =
      (adelicChar K (𝔞 (γ.val 0 0 / γ.val 1 1 - ξ 1) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[K]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s (y 0 * s))]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

end shifts

theorem intU {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) (hC : ContW K) {W : G3K K → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → K} (hξ1 : ξ 1 ≠ 0) (g : G3K K) (γ : GL (Fin 2) K) :
    ∫ y in vecDomain K (Fin 3), W (diaK (e1 K γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y
      ∂vecMeasure K (Fin 3) =
      if γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1 then W (diaK (e1 K γ) * g) else 0 := by
  show ∫ y in vecDomain K (Fin 3), fU W g ξ γ y ∂vecMeasure K (Fin 3) = _
  have hc := continuous_fU hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h11, h10, h01⟩ := hs
    have hr : γ.val 0 1 / γ.val 1 0 - ξ 0 = 0 := by
      rw [h01, h10, mul_div_cancel_right₀ _ hξ1, sub_self]
    rw [setIntegral_eq_of_shift]
    · simp [fU, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftU_c hV hW g ξ γ h11, hr, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt hV hW g ξ γ h11, h10, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt_alt hV hW g ξ γ, h11, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h11 : γ.val 1 1 = 0
    · by_cases h10 : γ.val 1 0 = ξ 1
      · have h01 : γ.val 0 1 ≠ ξ 0 * ξ 1 := fun h => hs ⟨h11, h10, h⟩
        refine setIntegral_eq_zero_of_shift hc 0 ?_ (shiftU_c hV hW g ξ γ h11)
        rw [h10, sub_ne_zero, Ne, div_eq_iff hξ1]
        exact h01
      · exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 h10) (shiftU_alt hV hW g ξ γ h11)
    · exact setIntegral_eq_zero_of_shift hc 2 h11 (shiftU_alt_alt hV hW g ξ γ)

theorem intV {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) (hC : ContW K) {W : G3K K → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → K} (g : G3K K) (γ : GL (Fin 2) K) :
    ∫ y in vecDomain K (Fin 3), W (diaK (e2 K γ * sw K) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) *
      chiH ξ y ∂vecMeasure K (Fin 3) =
      if γ.val 1 0 = 0 ∧ (γ⁻¹).val 0 0 = ξ 0 ∧ γ.val 0 0 / γ.val 1 1 = ξ 1 then
        W (diaK (e2 K γ * sw K) * g) else 0 := by
  show ∫ y in vecDomain K (Fin 3), fV W g ξ γ y ∂vecMeasure K (Fin 3) = _
  have hc := continuous_fV hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h10, hN, hd⟩ := hs
    have hN10 := (inv_upper γ h10).1
    rw [setIntegral_eq_of_shift]
    · simp [fV, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftV_c hV hW g ξ γ, hN, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt_alt hV hW g ξ γ h10, hd, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt hV hW g ξ γ, hN10, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h10 : γ.val 1 0 = 0
    · by_cases hN : (γ⁻¹).val 0 0 = ξ 0
      · have hd : γ.val 0 0 / γ.val 1 1 ≠ ξ 1 := fun h => hs ⟨h10, hN, h⟩
        exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 hd) (shiftV_alt_alt hV hW g ξ γ h10)
      · exact setIntegral_eq_zero_of_shift hc 0 (sub_ne_zero.2 hN) (shiftV_c hV hW g ξ γ)
    · exact setIntegral_eq_zero_of_shift hc 2 (inverse_lower_left_ne_zero γ h10) (shiftV_alt hV hW g ξ γ)

section reps

variable {ξ : Fin 2 → K} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0)

def gU : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, ξ 0 * ξ 1; ξ 1, 0] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

def gV : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ξ 0)⁻¹, 0; 0, (ξ 0 * ξ 1)⁻¹] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])








end reps

theorem final_eq {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → K} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0) (γ δ : GL (Fin 2) K)
    (hγ : γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1)
    (hδ : δ.val 1 0 = 0 ∧ δ.val 0 0 = (ξ 0)⁻¹ ∧ δ.val 1 1 = (ξ 0 * ξ 1)⁻¹) (g : G3K K) :
    W (diaK (e1 K γ) * g) = W (diaK (e2 K δ * sw K) * g) := by
  obtain ⟨g11, g10, g01⟩ := hγ
  obtain ⟨d10, d00, d11⟩ := hδ
  set s : Kˣ := Units.mk0 (ξ 0 * ξ 1) (mul_ne_zero hξ0 hξ1) with hs
  set a : K := γ.val 0 0 / ξ 1 with ha
  set z : K := -(ξ 0 * ξ 1 * δ.val 0 1) with hz
  set b : K := -(a * (ξ 0 * ξ 1) * δ.val 0 1) with hb
  have hQ : e1 K γ = uni a b z * (dg s s s * (e2 K δ * sw K)) := by
    apply Units.ext
    simp only [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e1, e2, b1M, b2M, sw, uni, dg, s, a, b, z, Matrix.mul_apply, Fin.sum_univ_three, g11,
        g10, g01, d10, d00, d11] <;>
      first | ring1 | (field_simp; ring1) | field_simp
  set S : (𝔸[K])ˣ := Units.map (algebraMap K 𝔸[K]).toMonoidHom s with hS
  have hdu : ∀ a b z : K, diaK (uni a b z) = uni (𝔞 a) (𝔞 b) (𝔞 z) := by
    intro a b z
    apply Units.ext
    rw [val_uni]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni]
  have hdd : diaK (dg s s s) = dg S S S := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, S]
  have key : diaK (e1 K γ) * g = uni (𝔞 a) (𝔞 b) (𝔞 z) * (dg S S S * (diaK (e2 K δ * sw K) * g)) := by
    have hm : diaK (uni a b z * (dg s s s * (e2 K δ * sw K))) =
        diaK (uni a b z) * (diaK (dg s s s) * diaK (e2 K δ * sw K)) := by
      simp only [diaK, map_mul]
    rw [hQ, hm, hdu, hdd]
    simp only [mul_assoc]
  rw [key, hV.psi W hW, hV.cen W hW, ← map_add, psi_rat, one_mul]


end Ad3.K.GA.CtvP

namespace Ad3.K.GA

variable {K : Type} [Field K] [NumberField K]



end Ad3.K.GA
end
end
