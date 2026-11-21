import ReciprocityTheory.SemistableReduction.SemiDegW
import Lemmata.GeneralBFactSecondAlt.Imports
import ReciprocityTheory.SemistableReduction.SemiDegSt
import ReciprocityTheory.SemistableReduction.SemiDegB
import ReciprocityTheory.SemistableReduction.SemiDegC

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem half_not_integral {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral ℤ ((2 : K)⁻¹) := by
    rw [← hz]
    exact NumberField.RingOfIntegers.isIntegral_coe z
  have e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm' : (m : ℚ) = 2⁻¹ := by simpa using hm
  have h2 : ((m * 2 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hm']
    norm_num
  have h3 : m * 2 = 1 := by exact_mod_cast h2
  omega

theorem no_line {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) (x : Fin r → K) (hx : x ≠ 0) (hline : ∀ t : K, t • x ∈ L) : False := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun v => Finset.univ.image v)
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    have : b = 0 := by exact_mod_cast h0
    exact nonZeroDivisors.ne_zero hb this
  have hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j) := by
    intro v hv j
    obtain ⟨z, hz⟩ := hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    refine ⟨z, ?_⟩
    show algebraMap (𝓞 K) K z = _
    rw [hz, Algebra.smul_def]
  have hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j) := by
    intro w hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => intro j; exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      intro j
      obtain ⟨z1, hz1⟩ := hv j
      obtain ⟨z2, hz2⟩ := hw j
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [Pi.add_apply, mul_add]
      exact congrArg₂ (· + ·) hz1 hz2
    | smul a v _ hv =>
      intro j
      obtain ⟨z, hz⟩ := hv j
      refine ⟨a * z, ?_⟩
      push_cast
      rw [Pi.smul_apply, Algebra.smul_def]
      calc (a : K) * (z : K) = (a : K) * ((b : K) * v j) := congrArg (fun q => (a : K) * q) hz
        _ = (b : K) * (algebraMap (𝓞 K) K a * v j) := by
          show (a : K) * ((b : K) * v j) = (b : K) * ((a : K) * v j)
          ring
  have h1 := hall _ (hline ((2 * (b : K) * x i)⁻¹)) i
  apply half_not_integral (K := K)
  convert h1 using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (t : K) (x y : Fin r → K) : S.h (t • x) y = S.c t * S.h x y := by
  rw [HermForm.h, HermForm.h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem detG_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by
  intro hdet
  have hdetT : S.Gᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hw0 : (fun a => S.c (v a)) ≠ 0 := by
    intro h
    apply hv0
    funext a
    have h1 := congrArg S.c (congrFun h a)
    simpa [S.c_invol] using h1
  have hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0 := by
    intro y
    simp only [HermForm.h, S.c_invol]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have hb := congrFun hv b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb
    rw [← Finset.sum_mul]
    have h2 : ∑ a, v a * S.G a b = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [h2, zero_mul]
  apply no_line L hL.1 _ hw0
  intro t
  apply hSD.2
  intro y _
  rw [hermForm_smul_left, hzero, mul_zero]
  exact ⟨0, by simp⟩

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem det_map_hom {K L : Type} [Field K] [Field L] {r : ℕ} (f : K →+* L)
    (A : Matrix (Fin r) (Fin r) K) : (A.map f).det = f A.det := (RingHom.map_det f A).symm

theorem gram_det_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (M : Majorant S) (hG : S.G.det ≠ 0) (σ : K →+* ℂ) (b : Fin r → Fin r → K) :
    (gramC (M.H σ) σ b).det.re = ‖σ (hGram S b).det‖ := by
  have hσG : (S.G.map σ).det ≠ 0 := by
    rw [det_map_hom]
    exact fun h => hG (σ.injective (by rw [h, map_zero]))
  have hdet2 : (M.H σ).det * (M.H σ).det = (S.G.map σ).det * (S.G.map σ).det := by
    have h1 := congr_arg Matrix.det (M.major σ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h1
    field_simp at h1
    linear_combination h1
  have hpos := (M.posDef σ).det_pos
  rw [Complex.lt_def] at hpos
  set x : ℝ := (M.H σ).det.re with hx
  have hxH : (M.H σ).det = (x : ℂ) := by
    apply Complex.ext
    · simp [hx]
    · simp [← hpos.2]
  have hx0 : 0 < x := by simpa using hpos.1
  have hxn : x = ‖(S.G.map σ).det‖ := by
    have h1 := congr_arg (‖·‖) hdet2
    simp only [norm_mul, hxH, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at h1
    nlinarith [norm_nonneg (S.G.map σ).det]
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hxH, hGram_eq,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hE : embMat σ b = (colMat b).map σ := rfl
  rw [det_map_hom, hE, det_map_hom, map_mul, map_mul, S.c_emb]
  rw [det_map_hom] at hxn
  set z := σ (colMat b).det
  rw [Complex.star_def, norm_mul, norm_mul, Complex.norm_conj]
  rw [show (starRingEnd ℂ) z * (x : ℂ) * z = (x : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hxn]
  ring

theorem latDeg_L_nonneg (hS : SelfDualIndexStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (M : Majorant S) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : IsLattice L) (hSD : IsSelfDual S L) (hG : S.G.det ≠ 0) (b : Fin r → Fin r → K)
    (hb : IsKBasisIn L b) : 0 ≤ latDeg M.H L b := by
  unfold latDeg
  rw [Finset.sum_congr rfl fun σ _ => by rw [gram_det_majorant S M hG σ b], sum_log_norm_emb]
  have h1 := hS K r S L b hL hSD hb
  have hone : 1 ≤ (spanIdx L b : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero L b hL.1 hb))
  have hlog1 := Real.log_nonneg hone
  by_cases hN0 : |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| = 0
  · rw [hN0, Real.log_zero]
    unfold spanIdx at hlog1
    linarith
  · have h2 := Real.log_le_log (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hN0)) h1
    rw [Real.log_pow] at h2
    unfold spanIdx at h2
    push_cast at h2
    linarith

theorem clear_denom {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)

theorem kBasis_card {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (b : Fin k → Fin r → K)
    (hb : IsKBasisIn L b) : k = r := by
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hL.2, Submodule.span_le]
    intro x hx
    exact hb.2.2 x hx
  have h := finrank_span_eq_card hb.2.1
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h
  exact h.symm

theorem g_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0) :
    ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0 := by
  classical
  intro i h1 h2 hg
  have ht := haniso (Pi.single i 1) (fun j hj => by
    have : j ≠ i := fun e => by rw [e] at hj; omega
    simp [this]) (by
    rw [Finset.sum_eq_single i]
    · simp [hg]
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h)
  have := congr_fun ht i
  simp at this

theorem semiPoint_of (hW : WittBasisStatement) (hB : LatDegBasisStatement)
    (hN : IntegralIndexStatement) (hS : SelfDualIndexStatement) (hE : GradedExtStatement)
    (hA : AbsDetStatement) : SemiPointStatement := by
  intro K _ _ r S L hL hSD
  have hG := detG_ne_zero S L hL hSD
  obtain ⟨P, m, g, hP, h2m, hJ, haniso⟩ := hW K r S hG
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  set Q := P⁻¹ with hQdef
  have hQ : Q.det ≠ 0 := by
    rw [hQdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hP
  set Lp := L.map (matLin Q) with hLpdef
  have hLp : Lp.FG := hL.1.map _
  have hfix := g_fix S P m g hJ
  have hg0 := g_ne_zero S m g haniso
  have hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp := by
    intro v
    obtain ⟨a, ha, hav⟩ := clear_denom L (P *ᵥ v) (by rw [hL.2]; exact Submodule.mem_top)
    refine ⟨a, ha, ⟨a • (P *ᵥ v), hav, ?_⟩⟩
    rw [map_smul, matLin_apply, Matrix.mulVec_mulVec, hQdef, Matrix.nonsing_inv_mul P hPu,
      Matrix.one_mulVec]
  have hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← hJ, formM_change, matLin_apply, matLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hQdef, Matrix.mul_nonsing_inv P hPu, Matrix.one_mulVec,
      Matrix.one_mulVec]
    exact hSD.1 x hx y hy
  obtain ⟨dd, hdd, hsemi⟩ :=
    adapted_semistable hB hN hA hE S m g h2m hfix hg0 haniso Lp hLp hsp hint
  obtain ⟨M, hM⟩ := exists_adapted_majorant S P m g dd hP h2m hJ hdd hg0
  have hHeq : M.H = fun σ : K →+* ℂ => (Q.map σ)ᴴ * diagMet (adMet r m g dd) σ * Q.map σ :=
    funext hM
  have hsemiL : ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L → ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg M.H B b ≤ 0 := by
    intro B hB k b hb
    rw [hHeq, latDeg_transport _ Q hQ B b]
    exact hsemi _ (Submodule.map_mono hB) k _ (kBasisIn_map Q hQ B b hb)
  refine ⟨M, ?_, hsemiL⟩
  intro k b hb
  obtain rfl : k = r := kBasis_card L hL b hb
  exact le_antisymm (hsemiL L le_rfl k b hb) (latDeg_L_nonneg hS S M L hL hSD hG b hb)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

def waR {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x : Fin r → K) :
    (Fin r → K) →ₗ[K] K where
  toFun y := S.h x y
  map_add' y z := by
    simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem waR_apply {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : waR S x y = S.h x y := rfl

theorem wa_symm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by
  unfold HermForm.h
  simp only [map_sum, map_mul, S.c_invol, S.G_herm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  simp only [HermForm.h, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem wa_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [HermForm.h]

theorem wa_sub_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by
  simp only [HermForm.h, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem wa_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sum_right {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by
  rw [← waR_apply S x, map_sum]
  simp only [map_smul, smul_eq_mul, waR_apply]

theorem wa_sum_left {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by
  rw [wa_symm S y, wa_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wa_symm S y (b i)]

theorem wa_finrank_inf_ker {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (f v / f z) • z + (v - (f v / f z) • z) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hz) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz, sub_self]
  have hker : finrank K (LinearMap.ker f) + 1 = finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    have hr : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / f z) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top] at h
  omega

theorem wa_diag {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, S.h x x = 0 → x = 0) →
      ∃ b : Fin n → Fin r → K, (∀ i, b i ∈ W) ∧ (∀ i, b i ≠ 0) ∧
        ∀ i j, i ≠ j → S.h (b i) (b j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W hW han
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW
      omega
    obtain ⟨z, hzW, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzz : S.h z z ≠ 0 := fun h => hz0 (han z hzW h)
    have hW' : finrank K ↥(W ⊓ LinearMap.ker (waR S z)) = n := by
      have h := wa_finrank_inf_ker W (waR S z) z hzW (by rw [waR_apply]; exact hzz)
      omega
    obtain ⟨b, hbW, hb0, hbo⟩ := ih (W ⊓ LinearMap.ker (waR S z)) hW' (fun x hx hxx => han x hx.1 hxx)
    have hk : ∀ k, S.h z (b k) = 0 := fun k => (hbW k).2
    refine ⟨Fin.cons z b, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hzW
      | succ i => simpa using (hbW i).1
    · cases i using Fin.cases with
      | zero => simpa using hz0
      | succ i => simpa using hb0 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hk j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [wa_symm S z (b i), hk i, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hbo i j fun h => hij (by rw [h])

theorem wa_hyp {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x : Fin r → K) (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : S.h x x = 0) :
    ∃ y ∈ W, S.h x y = 1 ∧ S.h y y = 0 := by
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, S.h x w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (hnd x hxW hc)
  obtain ⟨u, hu⟩ : ∃ u, u = (S.h x w)⁻¹ • w := ⟨_, rfl⟩
  have huW : u ∈ W := hu ▸ W.smul_mem _ hwW
  have hxu : S.h x u = 1 := by rw [hu, wa_smul_right, inv_mul_cancel₀ hw]
  have hux : S.h u x = 1 := by rw [wa_symm S x u, hxu, map_one]
  have hcuu : S.c (S.h u u) = S.h u u := (wa_symm S u u).symm
  obtain ⟨t, ht⟩ : ∃ t, t = S.h u u / 2 := ⟨_, rfl⟩
  have hct : S.c t = t := by rw [ht, map_div₀, hcuu, map_ofNat]
  refine ⟨u - t • x, W.sub_mem huW (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [wa_sub_right, hxu, wa_smul_right, hxx, mul_zero, sub_zero]
  · simp only [wa_sub_left, wa_sub_right, wa_smul_left, wa_smul_right, hux, hxu, hxx, hct]
    rw [ht]
    ring

theorem wa_perp_nondeg {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by
  intro z hz hzo
  obtain ⟨⟨hzW, hzx⟩, hzy⟩ := hz
  have hzx : S.h x z = 0 := hzx
  have hzy : S.h y z = 0 := hzy
  apply hnd z hzW
  intro w hwW
  have hyx : S.h y x = 1 := by rw [wa_symm S x y, hxy, map_one]
  have hw' : w - S.h y w • x - S.h x w • y ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y) := by
    refine ⟨⟨W.sub_mem (W.sub_mem hwW (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
    · show S.h x _ = 0
      simp only [wa_sub_right, wa_smul_right, hxx, hxy]
      ring
    · show S.h y _ = 0
      simp only [wa_sub_right, wa_smul_right, hyx, hyy]
      ring
  have h1 := hzo _ hw'
  have hzx' : S.h z x = 0 := by rw [wa_symm S x z, hzx, map_zero]
  have hzy' : S.h z y = 0 := by rw [wa_symm S y z, hzy, map_zero]
  simp only [wa_sub_right, wa_smul_right, hzx', hzy', mul_zero, sub_zero] at h1
  exact h1

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩

def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)

@[simp] theorem waExt_zero {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f 0 = x := by
  simp [waExt]

@[simp] theorem waExt_last {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

@[simp] theorem waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]

theorem wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]

theorem wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_witt_ker {K : Type} [Field K] (r m : ℕ) (g : Fin r → K)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0) (v : Fin r → K)
    (hv : ∀ p : Fin r, ∑ i, v i * wittMat r m g p i = 0) : v = 0 := by
  funext j
  have hj := j.isLt
  by_cases hmid : m ≤ (j : ℕ) ∧ (j : ℕ) + m < r
  · have h := hv j
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      rw [if_neg (by omega), if_pos ⟨trivial, hmid.1, hmid.2⟩] at h
      exact (mul_eq_zero.1 h).resolve_right (hg j hmid.1 hmid.2)
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨h1, -⟩
        exact hij h1.symm
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  · set p : Fin r := ⟨r - 1 - j, by omega⟩ with hp
    have hpv : (p : ℕ) = r - 1 - j := rfl
    have h := hv p
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      have hc : (p : ℕ) + j + 1 = r ∧ ((p : ℕ) < m ∨ (j : ℕ) < m) := by
        rw [hpv]
        omega
      rw [if_pos hc, mul_one] at h
      exact h
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨-, h2, h3⟩
        rw [hpv] at h2 h3
        omega
      · rintro ⟨h1, -⟩
        apply hij
        ext
        rw [hpv] at h1
        omega
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem wittBasis_holds : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem sdd_quad_conj {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin m → ℂ) :
    star w ⬝ᵥ ((Pᴴ * Q * P) *ᵥ w) = star (P *ᵥ w) ⬝ᵥ (Q *ᵥ (P *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem sdd_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, A = Bᴴ * B ∧ IsUnit B.det := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)
  refine ⟨B, hB, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hp := hA.det_pos
  rw [hB, star_eq_conjTranspose, det_mul, h0, mul_zero] at hp
  exact lt_irrefl _ hp

theorem sdd_star_self_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (⇑(hD.eigenvectorBasis i)) = 1 := by
  have h := orthonormal_iff_ite.mp hD.eigenvectorBasis.orthonormal i i
  rw [if_pos rfl, PiLp.inner_apply] at h
  rw [← h]
  simp only [dotProduct, Pi.star_apply, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.star_def, mul_comm]

theorem sdd_quad_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (D *ᵥ ⇑(hD.eigenvectorBasis i)) = (hD.eigenvalues i : ℂ) := by
  rw [hD.mulVec_eigenvectorBasis, dotProduct_smul, sdd_star_self_eig hD i]
  simp

theorem sdd_det_abs_le_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, ‖star w ⬝ᵥ (D *ᵥ w)‖ ≤ (star w ⬝ᵥ w).re) : ‖D.det‖ ≤ 1 := by
  rw [hD.det_eq_prod_eigenvalues, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  have hi := h (hD.eigenvectorBasis i)
  rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re] at hi

theorem sdd_det_ge_one {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (D *ᵥ w)).re) :
    D.det = ((D.det.re : ℝ) : ℂ) ∧ 1 ≤ D.det.re := by
  have hev : ∀ i, 1 ≤ hD.eigenvalues i := by
    intro i
    have hi := h (hD.eigenvectorBasis i)
    rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re, Complex.ofReal_re] at hi
  have hdet : D.det = ((∏ i, hD.eigenvalues i : ℝ) : ℂ) := by
    rw [hD.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl
  rw [hdet, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)

theorem sdd_congr {n : ℕ} (B X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) :
    X = Bᴴ * ((B⁻¹)ᴴ * X * B⁻¹) * B ∧
    ∀ w : Fin n → ℂ, star w ⬝ᵥ (((B⁻¹)ᴴ * X * B⁻¹) *ᵥ w) =
      star (B⁻¹ *ᵥ w) ⬝ᵥ (X *ᵥ (B⁻¹ *ᵥ w)) := by
  refine ⟨?_, fun w => sdd_quad_conj B⁻¹ X w⟩
  have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have h2 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  calc X = (Bᴴ * (B⁻¹)ᴴ) * X * (B⁻¹ * B) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sdd_quad_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) (w : Fin n → ℂ) :
    star w ⬝ᵥ w = star (B⁻¹ *ᵥ w) ⬝ᵥ ((Bᴴ * B) *ᵥ (B⁻¹ *ᵥ w)) := by
  have hw : B *ᵥ (B⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have e := sdd_quad_conj B 1 (B⁻¹ *ᵥ w)
  rw [Matrix.mul_one, hw, Matrix.one_mulVec] at e
  exact e.symm

theorem sdd_norm_det_sq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem sdd_det_congr {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * D * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) * D.det := by
  rw [det_mul, det_mul, ← sdd_norm_det_sq B, det_mul]
  ring

theorem sdd_absDet {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.IsHermitian)
    (h : ∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    ‖C.det‖ ≤ A.det.re := by
  obtain ⟨B, hAB, hu⟩ := sdd_factor hA
  obtain ⟨hCe, hq⟩ := sdd_congr B C hu
  have hDh : ((B⁻¹)ᴴ * C * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]
  have hD1 : ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ 1 := by
    apply sdd_det_abs_le_one hDh
    intro w
    rw [hq w, sdd_quad_self B hu w, ← hAB]
    exact h _
  have hdetA : A.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hAB, sdd_norm_det_sq]
  rw [hCe, sdd_det_congr, hdetA, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖B.det‖ ^ 2 * ‖((B⁻¹)ᴴ * C * B⁻¹).det‖ ≤ ‖B.det‖ ^ 2 * 1 := by gcongr
    _ = _ := mul_one _

theorem sdd_det_mono {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).re ≤ (star v ⬝ᵥ (Y *ᵥ v)).re) :
    0 < X.det.re ∧ X.det.re ≤ Y.det.re := by
  obtain ⟨B, hXB, hu⟩ := sdd_factor hX
  obtain ⟨hYe, hq⟩ := sdd_congr B Y hu
  have hDh : ((B⁻¹)ᴴ * Y * B⁻¹).IsHermitian := by
    simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]
  obtain ⟨hDr, hD1⟩ := sdd_det_ge_one hDh (fun w => by
    rw [hq w, sdd_quad_self B hu w, ← hXB]
    exact h _)
  have hdetX : X.det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) := by rw [hXB, sdd_norm_det_sq]
  have hBpos : 0 < ‖B.det‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu.ne_zero) 2
  rw [hdetX, hYe, sdd_det_congr, hDr, Complex.ofReal_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact ⟨hBpos, le_mul_of_one_le_right hBpos.le hD1⟩

def embM {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l i => σ (b i l)

theorem sdd_gramX_eq {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embM σ b)ᴴ * H * embM σ c := by
  ext i j
  simp only [gramX, embM, embVec, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sdd_gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embM σ b)ᴴ * H * embM σ b := sdd_gramX_eq H σ b b

theorem sdd_embM_inj {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) : Function.Injective (embM σ b).mulVec := by
  classical
  let M : Matrix (Fin r) (Fin k) K := Matrix.of fun l i => b i l
  have hM : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hs : ∑ i, x i • b i = M.mulVecLin x := by
      ext l
      simp [M, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
    rw [hx] at hs
    exact funext (Fintype.linearIndependent_iff.mp hb x hs)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.mpr hM)
  have hLM : LinearMap.toMatrix' g * M = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hg x
  have hE : embM σ b = M.map σ := rfl
  intro x y hxy
  have e := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simp only [hE, Matrix.mulVec_mulVec, ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.one_mulVec] at e
  exact e

theorem sdd_diag_quad {r : ℕ} (d : Fin r → ℝ) (x : Fin r → ℂ) :
    (star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x)).re = ∑ l, d l * ‖x l‖ ^ 2 := by
  have e : star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x) = ∑ l, ((d l * ‖x l‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, ← mul_assoc, mul_comm ((starRingEnd ℂ) (x l)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem sdd_cut_quad {r k : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℕ)
    (E B1 : Matrix (Fin r) (Fin k) ℂ) (hB1 : ∀ l j, B1 l j = if e ≤ (l : ℕ) then E l j else 0)
    (v : Fin k → ℂ) :
    (star v ⬝ᵥ ((B1ᴴ * diagonal (fun l => (d l : ℂ)) * B1) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * diagonal (fun l => (d l : ℂ)) * E) *ᵥ v)).re := by
  rw [sdd_quad_conj, sdd_quad_conj, sdd_diag_quad, sdd_diag_quad]
  refine Finset.sum_le_sum fun l _ => ?_
  have hrow : (B1 *ᵥ v) l = if e ≤ (l : ℕ) then (E *ᵥ v) l else 0 := by
    by_cases hc : e ≤ (l : ℕ) <;> simp [Matrix.mulVec, dotProduct, hB1, hc]
  rw [hrow]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    nlinarith [hd l, sq_nonneg ‖(E *ᵥ v) l‖]

theorem sdd_schur {r k₀ k₁ : ℕ} (B : Matrix (Fin r) (Fin k₀) ℂ) (C : Matrix (Fin r) (Fin k₁) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : Hᴴ = H) (hG : (Bᴴ * H * B).IsHermitian)
    (hu : IsUnit (Bᴴ * H * B).det) :
    Cᴴ * H * C - (Cᴴ * H * B) * (Bᴴ * H * B)⁻¹ * (Bᴴ * H * C) =
      (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C)))ᴴ * H *
        (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C))) := by
  set G := Bᴴ * H * B with hGdef
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hGinvH : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG.eq]
  have hYH : (Bᴴ * H * C)ᴴ = Cᴴ * H * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have hXh : (G⁻¹ * (Bᴴ * H * C))ᴴ = (Cᴴ * H * B) * G⁻¹ := by
    rw [conjTranspose_mul, hYH, hGinvH]
  have hcanc : ∀ Z : Matrix (Fin k₀) (Fin k₁) ℂ, G⁻¹ * (Bᴴ * (H * (B * Z))) = Z := by
    intro Z
    have hz : Bᴴ * (H * (B * Z)) = G * Z := by simp only [hGdef, Matrix.mul_assoc]
    rw [hz, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  rw [conjTranspose_sub, conjTranspose_mul, hXh]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hcanc]
  abel

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

def cutProjK (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

variable {K : Type} [Field K] [NumberField K] {r e : ℕ}

theorem sdd_cutProjK_eq (x : Fin r → K) : cutProjK K r e x = projGe K r e x := rfl

theorem sdd_proj_eq_zero_iff (x : Fin r → K) : projGe K r e x = 0 ↔ x ∈ cutSub K r e := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [projGe, hi] using this
  · intro h
    funext i
    by_cases hi : e ≤ (i : ℕ)
    · simp [projGe, hi, h i hi]
    · simp [projGe, hi]

theorem sdd_satSub_eq {k₀ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) : satSub B b₀ = B ⊓ cutSub K r e := by
  have hle : Submodule.span K (Set.range b₀) ≤ LinearMap.ker (cutProjK K r e) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (sdd_proj_eq_zero_iff _).mpr (hb₀.1 i).2
  ext x
  simp only [satSub, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨hx, (sdd_proj_eq_zero_iff x).mp (hle hs)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, hb₀.2.2 x ⟨hx, hc⟩⟩

theorem sdd_append_li {k₀ k₁ : ℕ} (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    LinearIndependent K (Fin.append b₀ c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have hc' : ∀ j, cutProjK K r e (c j) = b₁ j := hcb
  have hb' : ∀ i, cutProjK K r e (b₀ i) = 0 := fun i => (sdd_proj_eq_zero_iff _).mpr (hb₀cut i)
  have h1 : ∑ j, g (Fin.natAdd k₀ j) • b₁ j = 0 := by
    have := congrArg (cutProjK K r e) hg
    simpa [map_add, map_sum, map_smul, hb', hc'] using this
  have h1' := Fintype.linearIndependent_iff.mp hb₁li _ h1
  have h0 : ∑ i, g (Fin.castAdd k₁ i) • b₀ i = 0 := by simpa [h1'] using hg
  have h0' := Fintype.linearIndependent_iff.mp hb₀li _ h0
  intro i
  exact Fin.addCases (fun i => h0' i) (fun j => h1' j) i

theorem sdd_append_span {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁ : IsKBasisIn (B.map (projGe K r e)) b₁) :
    ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
  intro x hx
  have hfx : projGe K r e x ∈ Submodule.span K (Set.range b₁) :=
    hb₁.2.2 _ (Submodule.mem_map_of_mem hx)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hfx
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) β
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hd
  choose β' hβ' using hd
  set dK : K := algebraMap (𝓞 K) K d with hdK
  have hd0 : dK ≠ 0 := by
    rw [hdK]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  set y : Fin r → K := dK • x - ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j with hy
  have hyB : y ∈ B := by
    refine B.sub_mem ?_ (B.sum_mem fun j _ => ?_)
    · rw [hdK, algebraMap_smul]
      exact B.smul_mem _ hx
    · rw [algebraMap_smul]
      exact B.smul_mem _ (hcB j)
  have hycut : y ∈ cutSub K r e := by
    rw [← sdd_proj_eq_zero_iff, ← sdd_cutProjK_eq, hy, map_sub, map_smul, map_sum]
    simp only [map_smul, sdd_cutProjK_eq, hcb, ← hβ, Finset.smul_sum, smul_smul, hβ']
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def (d : 𝓞 K) (β j)]
  have hys : y ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
    refine Submodule.span_mono ?_ (hb₀.2.2 y ⟨hyB, hycut⟩)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd k₁ i, Fin.append_left b₀ c i⟩
  have hcs : ∀ j, c j ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := fun j =>
    Submodule.subset_span ⟨Fin.natAdd k₀ j, Fin.append_right b₀ c j⟩
  have hx' : x = dK⁻¹ • (y + ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j) := by
    rw [hy, sub_add_cancel, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hys
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs j)))

theorem sdd_card_eq {k k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K)
    (a : Fin (k₀ + k₁) → Fin r → K) (hb : IsKBasisIn B b) (haB : ∀ i, a i ∈ B)
    (hali : LinearIndependent K a) (has : ∀ x ∈ B, x ∈ Submodule.span K (Set.range a)) :
    k = k₀ + k₁ := by
  have hsp : Submodule.span K (Set.range b) = Submodule.span K (Set.range a) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact has _ (hb.1 i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb.2.2 _ (haB i)
  have h1 := finrank_span_eq_card hb.2.1
  have h2 := finrank_span_eq_card hali
  rw [hsp, h2] at h1
  simpa using h1.symm

theorem sdd_index {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hsat : satSub B b₀ = B ⊓ cutSub K r e) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) :
    (satSub B b₀ ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex B.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b₁)).toAddSubgroup.relIndex
        (B.map (projGe K r e)).toAddSubgroup := by
  have hspan : Submodule.span (𝓞 K) (Set.range b₁) =
      (Submodule.span (𝓞 K) (Set.range c)).map (projGe K r e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (hcb j).symm
  have hcle : Submodule.span (𝓞 K) (Set.range c) ≤ B := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcB j
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right, eq_comm, ← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, hsat,
    hspan]
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have hxy' : projGe K r e y = projGe K r e x := hxy
    have hyB := hcle hy
    refine ⟨?_, hx⟩
    have hs : x - y ∈ B ⊓ cutSub K r e :=
      ⟨B.sub_mem hx hyB, (sdd_proj_eq_zero_iff _).mp (by rw [map_sub, hxy', sub_self])⟩
    have := Submodule.add_mem_sup hs hy
    rwa [sub_add_cancel] at this
  · rintro ⟨hsup, hx⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hsup
    refine ⟨⟨t, ht, ?_⟩, hx⟩
    show projGe K r e t = projGe K r e (s + t)
    rw [map_add, (sdd_proj_eq_zero_iff s).mpr hs.2, zero_add]

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l

theorem sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle

theorem gradedExt_holds (hB : LatDegBasisStatement) (hD : DegAddStatement) :
    GradedExtStatement := by
  unfold GradedExtStatement
  unfold LatDegBasisStatement at hB
  unfold DegAddStatement at hD
  intro K _ _ r e k k₀ k₁ δ B b b₀ b₁ hδ hFG hb hb₀ hb₁

  have hlift : ∀ j, ∃ y ∈ B, projGe K r e y = b₁ j := fun j => Submodule.mem_map.mp (hb₁.1 j)
  choose c hcB hcb using hlift
  have hb₀B : ∀ i, b₀ i ∈ B := fun i => (hb₀.1 i).1
  have hb₀cut : ∀ i, b₀ i ∈ cutSub K r e := fun i => (hb₀.1 i).2
  have hli : LinearIndependent K (Fin.append b₀ c) :=
    sdd_append_li b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
  have hsp : ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) :=
    sdd_append_span B b₀ c b₁ hb₀ hcB hcb hb₁
  have hmem : ∀ i, Fin.append b₀ c i ∈ B := by
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hb₀B, hcB]
  have hk : k = k₀ + k₁ := sdd_card_eq B b (Fin.append b₀ c) hb hmem hli hsp
  subst hk
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ => by
    simp only [diagMet]
    exact posDef_diagonal_ofReal_of_pos (δ σ) (hδ σ)
  have h1 : latDeg (diagMet δ) B b = latDeg (diagMet δ) B (Fin.append b₀ c) :=
    hB K r (k₀ + k₁) (diagMet δ) B b (Fin.append b₀ c) hpd hFG hb ⟨hmem, hli, hsp⟩
  have h2 := hD K r k₀ k₁ (diagMet δ) B b₀ c hpd hFG hb₀B hcB hli hsp
  have hsat : satSub B b₀ = B ⊓ cutSub K r e := sdd_satSub_eq B b₀ hb₀
  rw [hsat] at h2
  have h3 : quotDeg (diagMet δ) B b₀ c ≤ latDeg (diagMet δ) (B.map (projGe K r e)) b₁ := by
    unfold quotDeg latDeg
    rw [sdd_index B b₀ c b₁ hsat hcB hcb]
    have hs : ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ b₁).det.re ≤
        ∑ σ : K →+* ℂ, Real.log (quotGramC (diagMet δ σ) σ b₀ c).det.re :=
      Finset.sum_le_sum fun σ _ =>
        sdd_gram_step σ (δ σ) (hδ σ) b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
    linarith
  linarith [h1, h2, h3]

theorem absDet_holds : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h

end ReciprocityTheory.MultiplicativeHeights
end
end

section
namespace ReciprocityTheory.MultiplicativeHeights

theorem semiDeg_holds (hD : DegAddStatement) : SemiPointStatement :=
  SemiPt.semiPoint_of wittBasis_holds latDegBasis_holds integralIndex_holds selfDualIndex_holds
    (gradedExt_holds latDegBasis_holds hD) absDet_holds

end ReciprocityTheory.MultiplicativeHeights
end
