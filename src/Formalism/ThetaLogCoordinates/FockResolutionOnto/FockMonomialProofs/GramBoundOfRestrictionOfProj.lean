import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementA
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersHolds

section
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M MvPolynomial Finset

theorem partner_determinant_holds : PartnerDet := by
  intro p _ Vs _ _ _ _ be k g D hli hpart
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG
  obtain ⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩ := Formalism.GM.TM.smith_qp smith_form_p_adic_integers G
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  let U' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨U x y, hU x y⟩
  let V' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨V x y, hV x y⟩
  have hU'map : U'.map φ = U := by ext x y; rfl
  have hU'det : IsUnit U'.det := by
    rw [PadicInt.isUnit_iff]
    have : ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det := by
      rw [← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]; rfl
    rw [PadicInt.norm_def, this, hUd]
  set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW
  have hWU : W * U' = 1 := Matrix.nonsing_inv_mul _ hU'det
  have hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x := fun a x => by
    rw [← PadicInt.algebraMap_apply, algebraMap_smul]

  have hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖ := by
    intro i
    set u : Vs := ∑ a, W i a • g a with hu
    have huL : u ∈ Submodule.span ℤ_[p] (Set.range g) :=
      Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩
    have hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a := by
      intro a x hx hux
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx
      have h0 : ∑ b, (W i b - a * c b) • g b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [← hu, hux, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0
      have h2 : (W * U') i i = a * ∑ b, c b * U' b i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sub_eq_zero.mp (h1 b)]; ring
      rw [hWU, Matrix.one_apply_eq] at h2
      exact IsUnit.of_mul_eq_one _ h2.symm
    obtain ⟨u', hu'L, hu'⟩ := hpart u huL hprim
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L
    have hWG : ∀ b, be u (g b) = dg i * V i b := by
      intro b
      have e1 : be u (g b) = ((W.map φ) * G) i b := by
        rw [Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
      have e2 : (W.map φ) * U = 1 := by
        rw [← hU'map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      rw [e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]
    have hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p]) := by
      rw [map_sum, PadicInt.coe_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]
      show _ = dg i * ((c b : ℚ_[p]) * V i b)
      ring
    rw [hval, norm_mul] at hu'
    refine hu'.trans ?_
    calc ‖dg i‖ * ‖((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])‖ ≤ ‖dg i‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖dg i‖ := mul_one _
  rw [hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one,
    norm_prod]
  calc (p : ℝ) ^ (-(D * k)) = ∏ _i : Fin k, (p : ℝ) ^ (-D) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]
        congr 1; ring
    _ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i

section Gr
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem grLat_le_int (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ IntPol p (Fin (K + 1) × Fin r) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ IntPol p (Fin (K + 1) × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2
  refine Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_
  rw [Formalism.GM.MeanGammaLemmas.coeff_initPart]
  split_ifs
  · exact Formalism.CountingSumsFrames.intPol_norm f hfI m
  · simp

theorem grLat_le_pol (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfM : f ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hfP : f ∈ Pol p r LLw :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1
  show initPart v e f ∈ Pol p r LLw
  unfold Pol at hfP ⊢
  rw [mem_restrictSupport_iff] at hfP ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart] at hm
  refine hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
  intro h0
  apply hm
  rw [h0, ite_self]

end Gr

theorem graded_piece_bound_holds : GradedPieceBound := by
  intro p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Pr, hPr⟩ := hProj
  have key := partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli
    ?_
  · exact key
  intro u hu hprim
  rw [hspan] at hu hprim
  set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr
  set XX := grSpan p LLw J M ρ w e with hXX
  have hGX : ∀ x ∈ Gr, x ∈ XX := fun x hx => Submodule.subset_span hx
  have hu0 : u ≠ 0 := by
    intro h0
    have := hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])
    exact not_isUnit_zero this
  have huI : u ∈ IntPol p (Fin (K + 1) × Fin r) := grLat_le_int LLw J M ρ w _ e hu
  have huP : u ∈ Pol p r LLw := grLat_le_pol LLw J M ρ w _ e hu
  have hne : u.support.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image u.support (fun m => ‖coeff m u‖) hne
  set a := coeff m u with ha
  have ha0 : a ≠ 0 := mem_support_iff.mp hm
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hmD : MultiDeg LLw m := by
    unfold Pol at huP
    rw [mem_restrictSupport_iff] at huP
    exact huP (Finset.mem_coe.mpr hm)
  set u0 := a⁻¹ • u with hu0def
  have hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_
    rw [hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]
    by_cases hm' : m' ∈ u.support
    · exact hmax m' hm'
    · rw [notMem_support_iff.mp hm', norm_zero]; exact han.le
  have hu0X : u0 ∈ XX := XX.smul_mem _ (hGX u hu)
  have hu0c : ‖coeff m u0‖ = 1 := by
    rw [hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]
  have huu0 : u = a • u0 := by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr := hSat u0 hu0X hu0I
  have hpc : ((p : ℚ_[p]) ^ c) ≠ 0 := pow_ne_zero _ hpQ
  have hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]
  have hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]

  have hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1 := by
      rw [norm_div, hnpc, div_inv_eq_mul]
      have hpc' : (0 : ℝ) < (p : ℝ) ^ c := by positivity
      calc ‖a‖ * (p : ℝ) ^ c < ((p : ℝ) ^ c)⁻¹ * (p : ℝ) ^ c := mul_lt_mul_of_pos_right hlt hpc'
        _ = 1 := inv_mul_cancel₀ hpc'.ne'
    let b : ℤ_[p] := ⟨a / (p : ℚ_[p]) ^ c, hb.le⟩
    have hub : u = b • (((p : ℚ_[p]) ^ c) • u0) := by
      rw [← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]
      show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0
      rw [div_mul_cancel₀ _ hpc]; exact huu0
    have hunit := hprim b _ hy hub
    rw [PadicInt.isUnit_iff] at hunit
    have : ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖ := rfl
    linarith
  obtain ⟨hP1, hP2, hP3⟩ := hPr m hmD
  refine ⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩
  · rw [hspan]
    exact hSat _ (XX.smul_mem _ hP1) hP2
  · rw [Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']
    have e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1) := by
      unfold fockN
      rw [hP3 u (hGX u hu)]
      conv_lhs => rw [huu0]
      rw [Formalism.GM.TM.fock_smul_left, mul_div_assoc]
    have e2 := Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c
    rw [e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]
    have hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹ := by positivity
    have hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹ := by positivity
    have h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    gcongr

end Formalism.InvariantFactorPaths.L4
end

section
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section EProj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def LowIm (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c), Submodule.map (glAct p LL j c d) ⊤

def IsEProj (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  PE ∘ₗ PE = PE ∧ LinearMap.range PE = HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w ∧
    LinearMap.ker PE ⊓ WtSpC p LL j univ w = LowIm p LL j ρ ⊓ WtSpC p LL j univ w

theorem hypE_eproj (LL : Letters N) (ρ : Fin r) (e1 : ℕ) (hE : HypE p LL ρ e1) (j : ℕ) (hj : j ≤ N) (w : Fin r → ℤ) :
    ∃ PE, IsEProj p LL j ρ w PE ∧
      (∀ F G, F ∈ WtSpC p LL j univ w → G ∈ WtSpC p LL j univ w → fock p (PE F) G = fock p F (PE G)) ∧
      ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ w → ((p : ℚ_[p]) ^ e1) • PE F ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨PE, h1, h2, h3, h4, h5⟩ := hE j hj w
  exact ⟨PE, ⟨h1, h2, h3⟩, h4, h5⟩

theorem wtsp_mono (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ) :
    WtSpC p LL j univ w ≤ WtSpC p LL j Cs w := by
  intro x hx
  simp only [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  intro m hm
  have hm' := hx hm
  simp only [Set.mem_setOf_eq] at hm' ⊢
  intro c _
  exact hm' c (Finset.mem_univ c)

theorem eproj_mem (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    PE x ∈ HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w := by
  obtain ⟨_, hr, _⟩ := hPE
  rw [← hr]
  exact LinearMap.mem_range_self PE x

theorem eproj_fix (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ x ∈ HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w, PE x = x := by
  intro x hx
  obtain ⟨hi, hr, _⟩ := hPE
  rw [← hr] at hx
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun hi y

theorem lowIm_keep (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ LowIm p LL j ρ, Q x ∈ LowIm p LL j ρ := by
  intro x hx
  have key : LowIm p LL j ρ ≤ (LowIm p LL j ρ).comap Q := by
    unfold LowIm
    refine iSup_le fun c => iSup_le fun d => iSup_le fun h => ?_
    intro y hy
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.mem_comap, hQ c h.1 d h.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem Submodule.mem_top)))
  exact key hx

theorem eproj_comm (LL : Letters N) (j : ℕ) (ρ : Fin r) (w1 w2 : Fin r → ℤ)
    (HeightBoundSetup LogBallEstimates : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : IsEProj p LL j ρ w1 HeightBoundSetup) (h2 : IsEProj p LL j ρ w2 LogBallEstimates)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hW : ∀ x ∈ WtSpC p LL j univ w1, Q x ∈ WtSpC p LL j univ w2) :
    ∀ F ∈ WtSpC p LL j univ w1, LogBallEstimates (Q F) = Q (HeightBoundSetup F) := by
  intro F hF
  obtain ⟨i1, r1, k1⟩ := h1
  obtain ⟨i2, r2, k2⟩ := h2
  have hP1 : HeightBoundSetup F ∈ HWC p LL j (univ.erase ρ) w1 ⊓ WtSpC p LL j univ w1 := by
    rw [← r1]; exact LinearMap.mem_range_self HeightBoundSetup F
  have hfix1 : HeightBoundSetup (HeightBoundSetup F) = HeightBoundSetup F := LinearMap.congr_fun i1 F
  have hK : F - HeightBoundSetup F ∈ LinearMap.ker HeightBoundSetup ⊓ WtSpC p LL j univ w1 := by
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.sub_mem _ hF (Submodule.mem_inf.mp hP1).2⟩
    rw [LinearMap.mem_ker, map_sub, hfix1, sub_self]
  rw [k1] at hK
  obtain ⟨hKL, hKW⟩ := Submodule.mem_inf.mp hK
  have hQK : Q (F - HeightBoundSetup F) ∈ LinearMap.ker LogBallEstimates ⊓ WtSpC p LL j univ w2 := by
    rw [k2]
    exact Submodule.mem_inf.mpr ⟨lowIm_keep LL j ρ Q hQ _ hKL, hW _ hKW⟩
  have hQH : Q (HeightBoundSetup F) ∈ HWC p LL j (univ.erase ρ) w2 ⊓ WtSpC p LL j univ w2 := by
    obtain ⟨hH, hWW⟩ := Submodule.mem_inf.mp hP1
    have hQW := hW _ hWW
    refine Submodule.mem_inf.mpr ⟨?_, hQW⟩
    simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    refine ⟨wtsp_mono LL j _ w2 hQW, fun c d hcd => ?_⟩
    rw [← hQ c hcd.1 d hcd.2.1, hH.2 c d hcd, map_zero]
  have e2 : LogBallEstimates (Q (HeightBoundSetup F)) = Q (HeightBoundSetup F) := eproj_fix LL j ρ w2 LogBallEstimates ⟨i2, r2, k2⟩ _ hQH
  have e3 : LogBallEstimates (Q (F - HeightBoundSetup F)) = 0 := (Submodule.mem_inf.mp hQK).1
  have hsplit : Q F = Q (HeightBoundSetup F) + Q (F - HeightBoundSetup F) := by
    rw [← map_add]; simp
  rw [hsplit, map_add, e2, e3, add_zero]

private theorem coeff_filt_lemma {σ R : Type*} [CommSemiring R] [DecidableEq σ] (P : (σ →₀ ℕ) → Prop)
    (dec : ∀ m, Decidable (P m)) (x : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (∑ m ∈ x.support, @ite _ (P m) (dec m) (monomial m (coeff m x)) 0) =
      @ite _ (P n) (dec n) (coeff n x) 0 := by
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (coeff n), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  by_cases hn : n ∈ x.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hn h
  · have h0 : coeff n x = 0 := by simpa using hn
    rw [h0, ite_self]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := fun h => hn (h ▸ hb)
    simp [hbn]

private theorem glAct_slice_lemma_2 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (Q : Set ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
  have hmono : ∀ (a b : Fin r), a ≠ ρ → b ≠ ρ → ∀ (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N),
      n (i, ρ) ∈ Q →
      X (i', a) * pderiv (i', b) (monomial n t) ∈ MvPolynomial.restrictSupport ℚ_[p] {n | n (i, ρ) ∈ Q} := by
    intro a b ha hb n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
    rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have h1 : (i', a) ≠ (i, ρ) := fun h => ha (Prod.mk.inj h).2
    have h2 : (i', b) ≠ (i, ρ) := fun h => hb (Prod.mk.inj h).2
    simpa [Finsupp.single_apply, h1, h2] using hn
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnQ : n (i, ρ) ∈ Q := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d hc hd n _ i' hnQ
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c hd hc n _ i' hnQ)
  · exact Submodule.zero_mem _

private theorem resL_keep_lemma_4 (v : Fin N × Fin r) (e : ℕ) (S : Set (Fin N × Fin r →₀ ℕ))
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] S) :
    resL p v e y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hy (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _

private theorem resL_glAct_lemma_3 (LL : Letters N) (j : ℕ) (ρ c d : Fin r) (hc : c ≠ ρ) (hd : d ≠ ρ) (i : Fin N)
    (e : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p (i, ρ) e (glAct p LL j c d x) = glAct p LL j c d (resL p (i, ρ) e x) := by
  have hres : ∀ (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (n : Fin N × Fin r →₀ ℕ),
      coeff n (resL p (i, ρ) e y) = if n (i, ρ) = e then coeff n y else 0 := by
    intro y n
    simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
    unfold initPart
    exact coeff_filt_lemma (fun m => m (i, ρ) = e) _ y n
  have hmem : resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_contra h
    exact hn (if_neg h)
  have hrest : x - resL p (i, ρ) e x ∈
      MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)} := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hres] at hn
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e} : Set ℕ)},
      resL p (i, ρ) e y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h (hy (Finset.mem_coe.mpr hn))
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n : Fin N × Fin r →₀ ℕ | n (i, ρ) ∈ ({e}ᶜ : Set ℕ)},
      resL p (i, ρ) e y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hres, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => hy (Finset.mem_coe.mpr hn) h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hsplit : x = resL p (i, ρ) e x + (x - resL p (i, ρ) e x) := by abel
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, hid _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hmem),
    hzero _ (glAct_slice_lemma_2 LL j ρ c d hc hd i _ _ hrest), add_zero]

theorem eproj_res (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (i : Fin N) (e : ℕ) :
    ∀ F ∈ WtSpC p LL j univ w, PE (resL p (i, ρ) e F) = resL p (i, ρ) e (PE F) := by
  intro F hF
  exact eproj_comm LL j ρ w w PE PE hPE hPE (resL p (i, ρ) e)
    (fun c hc d hd x => resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hc) (Finset.ne_of_mem_erase hd) i e x)
    (fun x hx => resL_keep_lemma_4 (i, ρ) e _ x hx) F hF

private theorem glAct_md_lemma_5 (LL : Letters N) (j : ℕ) (c d : Fin r) (B : Prop)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)}) :
    glAct p LL j c d y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
  have hs : ∀ (i' : Fin N) (a' : Fin r) (i'' : Fin N),
      ∑ c', (Finsupp.single (i', a') 1 : Fin N × Fin r →₀ ℕ) (i'', c') = if i'' = i' then 1 else 0 := by
    intro i' a' i''
    by_cases h : i'' = i'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hmono : ∀ (a b : Fin r) (n : Fin N × Fin r →₀ ℕ) (t : ℚ_[p]) (i' : Fin N), (MultiDeg LL n ↔ B) →
      X (i', a) * pderiv (i', b) (monomial n t) ∈
        MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ B)} := by
    intro a b n t i' hn
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : n (i', b) = 0
    · rw [h0]
      simp
    · have hle : Finsupp.single (i', b) 1 ≤ n := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have hX : (X (i', a) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = monomial (Finsupp.single (i', a) 1) 1 := rfl
      rw [hX, MvPolynomial.monomial_mul, MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
      have hsum : ∀ i'', ∑ c', ((Finsupp.single (i', a) 1 + (n - Finsupp.single (i', b) 1) : Fin N × Fin r →₀ ℕ)) (i'', c') =
          ∑ c', n (i'', c') := by
        intro i''
        have hn' : n = (n - Finsupp.single (i', b) 1) + Finsupp.single (i', b) 1 :=
          (tsub_add_cancel_of_le hle).symm
        conv_rhs => rw [hn']
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hs]
        ring
      show MultiDeg LL _ ↔ B
      rw [← hn]
      unfold MultiDeg
      simp only [hsum]
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  rw [← MvPolynomial.support_sum_monomial_coeff y, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnB : (MultiDeg LL n ↔ B) := hy (Finset.mem_coe.mpr hn)
  simp only [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i' _ => ?_
  split_ifs
  · exact hmono c d n _ i' hnB
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hmono d c n _ i' hnB)
  · exact Submodule.zero_mem _

theorem eproj_pol (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) :
    ∀ F ∈ Pol p r LL, F ∈ WtSpC p LL j univ w → PE F ∈ Pol p r LL := by
  classical
  intro F hFP hFW
  let Pm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    { toFun := fun x => ∑ m ∈ x.support, if MultiDeg LL m then monomial m (coeff m x) else 0
      map_add' := fun x y => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_add, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _, coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp
      map_smul' := fun t x => by
        ext n
        beta_reduce
        rw [MvPolynomial.coeff_smul, coeff_filt_lemma (fun m => MultiDeg LL m) _,
          coeff_filt_lemma (fun m => MultiDeg LL m) _]
        split_ifs <;> simp }
  have hπ : ∀ y n, coeff n (Pm y) = if MultiDeg LL n then coeff n y else 0 :=
    fun y n => coeff_filt_lemma (fun m => MultiDeg LL m) _ y n
  have hsupp : ∀ (S : Set (Fin N × Fin r →₀ ℕ)) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      y ∈ MvPolynomial.restrictSupport ℚ_[p] S → Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] S := by
    intro S y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    apply hy
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
    intro h0
    exact hn (by rw [h0, ite_self])
  have hmemT : ∀ y, Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_true]
    by_contra h
    exact hn (if_neg h)
  have hrest : ∀ y, y - Pm y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)} := by
    intro y
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, hπ] at hn
    simp only [Set.mem_setOf_eq, iff_false]
    intro h
    exact hn (by rw [if_pos h, sub_self])
  have hid : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ True)}, Pm y = y := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ]
    split_ifs with h
    · rfl
    · have hn : n ∉ y.support := fun hn => h ((hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ True).mpr trivial)
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn.symm
  have hzero : ∀ y ∈ MvPolynomial.restrictSupport ℚ_[p] {n | (MultiDeg LL n ↔ False)}, Pm y = 0 := by
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff] at hy
    ext n
    rw [hπ, MvPolynomial.coeff_zero]
    split_ifs with h
    · have hn : n ∉ y.support := fun hn => (hy (Finset.mem_coe.mpr hn) : MultiDeg LL n ↔ False).mp h
      rw [MvPolynomial.mem_support_iff, not_not] at hn
      exact hn
    · rfl
  have hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      Pm (glAct p LL j c d x) = glAct p LL j c d (Pm x) := by
    intro c _ d _ x
    have hsplit : x = Pm x + (x - Pm x) := by abel
    conv_lhs => rw [hsplit]
    rw [map_add, map_add, hid _ (glAct_md_lemma_5 LL j c d True _ (hmemT x)),
      hzero _ (glAct_md_lemma_5 LL j c d False _ (hrest x)), add_zero]
  have key := eproj_comm LL j ρ w w PE PE hPE hPE Pm hQ (fun x hx => hsupp _ x hx) F hFW
  have hF : Pm F = F := hid F (by
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hFP
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    simpa using hFP hn)
  rw [hF] at key
  rw [key]
  have hT := hmemT (PE F)
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  rw [MvPolynomial.mem_restrictSupport_iff] at hT
  intro n hn
  simpa using hT hn

theorem typeProj_wtsp_later (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, P x ∈ WtSpC p LL j univ w :=
  comm_wtsp LL j P (fun c x => typeProj_comm_later LL j' j hjj T P hP c c x) w

theorem eproj_typeProj (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ T P) :
    ∀ F ∈ WtSpC p LL j univ w, PE (P F) = P (PE F) :=
  eproj_comm LL j ρ w w PE PE hPE hPE P
    (fun c _ d _ x => typeProj_comm_later LL j' j hjj T P hP c d x) (typeProj_wtsp_later LL j' j hjj T P hP w)

theorem eproj_ycond [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL j ρ w PE) (Mt : WithTop ℤ)
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j' univ {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ h ∈ YCond p LL j' Mt ⊓ Pol p r LL, h ∈ WtSpC p LL j univ w → PE h ∈ YCond p LL j' Mt := by
  intro h hh hW
  have h1 : P h = h := ycond_fix LL j' _ Mt P hP (fun la hla => hla) h hh
  have h2 := eproj_typeProj LL j' j hjj ρ w PE hPE _ P hP h hW
  rw [h1] at h2
  rw [h2]
  exact typeProj_range_le_ycond LL j' _ Mt P hP (fun la hla => hla) _

theorem eproj_Y [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 : ℕ) (hHP : HypP p LL ρ e1)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hPE : IsEProj p LL N ρ w PE) :
    ∀ h ∈ Y p LL J M, h ∈ WtSpC p LL N univ w → PE h ∈ MMw p LL J M ρ w := by
  intro h hh hW
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp (eproj_mem LL N ρ w PE hPE h)
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
    ⟨eproj_pol LL N ρ w PE hPE h hhP hW, ?_⟩, hA⟩, hB⟩
  rw [Submodule.mem_iInf]
  intro k
  obtain ⟨P, hP, -, -⟩ := hHP.1 (min (J k) N) (min_le_right _ _) univ (Or.inl rfl)
    {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)
      rw [hl 0 (Finset.mem_univ 0)])
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact eproj_ycond LL _ N (min_le_right _ _) ρ w PE hPE (M k) P hP h (Submodule.mem_inf.mpr ⟨hk, hhP⟩) hW

end EProj

section WtComp
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def wtComp (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (w : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  compP (fun m => ∀ c, wt LL j c m = w c) x

theorem wtComp_mem (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wtComp p LL j w x ∈ WtSpC p LL j univ w := by
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m _ => ?_
  split_ifs with h
  · rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    simp only [Set.mem_setOf_eq]
    intro c _
    exact h c
  · exact Submodule.zero_mem _

theorem wtComp_fix (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ w, wtComp p LL j w x = x := by
  intro x hx
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : ∀ c ∈ univ, wt LL j c m = w c := hx (Finset.mem_coe.mpr hm)
  split_ifs with h
  · rfl
  · exact absurd (fun c => hm' c (Finset.mem_univ c)) h

theorem wtComp_int (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) :
    ∀ x ∈ IntPol p (Fin N × Fin r), wtComp p LL j w x ∈ IntPol p (Fin N × Fin r) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m _ => ?_
  split_ifs
  · exact ⟨monomial m (coeff m y), by simp [MvPolynomial.coeff_map]⟩
  · exact Submodule.zero_mem _

theorem wtComp_keep_supp (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (Q : Set (Fin N × Fin r →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, wtComp p LL j w x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  unfold wtComp compP
  refine Submodule.sum_mem _ fun m hm => ?_
  split_ifs
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')]
    exact hx (Finset.mem_coe.mpr hm)
  · exact Submodule.zero_mem _

theorem wtComp_res (LL : Letters N) (j : ℕ) (w : Fin r → ℤ) (v : Fin N × Fin r) (e : ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (wtComp p LL j w x) = wtComp p LL j w (resL p v e x) := by
  ext n
  simp only [resL, LinearMap.coe_mk, AddHom.coe_mk]
  unfold initPart wtComp compP
  beta_reduce
  rw [coeff_filt_lemma (fun m => m v = e) _]
  erw [coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _, coeff_filt_lemma (fun m => ∀ c, wt LL j c m = w c) _]
  rw [coeff_filt_lemma (fun m => m v = e) _]
  split_ifs <;> rfl

theorem cartan_ycond [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j' Mt, glAct p LL j c c x ∈ YCond p LL j' Mt := by
  intro x hx
  rw [glAct_split LL j' j c c, LinearMap.add_apply]
  refine Submodule.add_mem _ (ycond_glStable LL j' Mt c c x hx) ?_
  refine ycond_keep LL j' Mt (glRest p LL j' j c c) (fun a b y => glRest_comm LL j' j hjj c c a b y)
    (fun y hy => ops_keep_supp {v : Fin N × Fin r | j' ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_)
      (glRest_mem LL j' j hjj c c) y hy) x hx
  have : wt LL j' 0 m = wt LL j' 0 m' :=
    wt_congr LL j' 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [← this]; exact hm

theorem wtComp_Y [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (w : Fin r → ℤ) :
    ∀ h ∈ Y p LL J M, wtComp p LL N w h ∈ Y p LL J M := by
  intro h hh
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  refine Submodule.mem_inf.mpr ⟨wtComp_keep_supp LL N w _ h hhP, ?_⟩
  rw [Submodule.mem_iInf]
  intro k
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact wcomp_mem LL N _ (fun c x hx => cartan_ycond LL _ N (min_le_right _ _) (M k) c x hx) w h hk

end WtComp

section MulX
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

end MulX

theorem res_hw {p : ℕ} [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ) (i : Fin N)
    (e : ℕ) : ∀ x ∈ HWC p LL j (univ.erase ρ) w, resL p (i, ρ) e x ∈ HWC p LL j (univ.erase ρ) w := by
  intro x hx
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  refine ⟨resL_keep_lemma_4 (i, ρ) e _ x hx.1, fun c d hcd => ?_⟩
  rw [← resL_glAct_lemma_3 LL j ρ c d (Finset.ne_of_mem_erase hcd.1) (Finset.ne_of_mem_erase hcd.2.1) i e x,
    hx.2 c d hcd, map_zero]

theorem restriction_min_max_holds : ResMM := by
  intro p _ K r _ LL q J M ρ w e1 hr hρ hv hHP hHE hOnto x
  constructor
  · intro hx
    obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
    obtain ⟨h0, hh0, hres⟩ := hOnto x hxX
    obtain ⟨PE, hPE, -, -⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
    refine ⟨PE (wtComp p LL (K + 1) w h0), eproj_Y LL J M ρ w e1 hHP PE hPE _ (wtComp_Y LL J M w h0 hh0)
      (wtComp_mem LL (K + 1) w h0), ?_⟩
    change resL p (Fin.last K, ρ) 0 (PE (wtComp p LL (K + 1) w h0)) = x
    change resL p (Fin.last K, ρ) 0 h0 = x at hres
    rw [← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ (wtComp_mem LL (K + 1) w h0), wtComp_res, hres,
      wtComp_fix LL (K + 1) w x hxW]
    exact eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩)
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh1, hhW⟩ := Submodule.mem_inf.mp hh
    obtain ⟨hhY, hhH⟩ := Submodule.mem_inf.mp hh1
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨restriction_into_holds p K r LL J M ρ e1 hr hρ hv hHP h hhY,
      res_hw LL (K + 1) ρ w (Fin.last K) 0 h hhH⟩, resL_keep_supp (Fin.last K, ρ) 0 _ h hhW⟩


end Formalism.InvariantFactorPaths.L4
end

section
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {σ : Type}

private theorem coeff_initPart_eq_ite (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (n : σ →₀ ℕ) :
    coeff n (initPart v e f) = if n v = e then coeff n f else 0 := by
  classical
  unfold initPart
  rw [coeff_sum]
  simp only [apply_ite (coeff n), coeff_monomial, coeff_zero]
  rw [Finset.sum_eq_single n]
  · by_cases h : n v = e <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro hn
    have h0 : coeff n f = 0 := by simpa [mem_support_iff] using hn
    simp [h0]

theorem p_pow_ne_zero (n : ℕ) : ((p : ℚ_[p]) ^ n) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

noncomputable def strip (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun f := (initPart v e f).divMonomial (Finsupp.single v e)
  map_add' x y := by
    rw [initPart_add]; ext m; simp only [coeff_divMonomial, coeff_add]
  map_smul' a x := by
    rw [initPart_smul]; ext m; simp only [coeff_divMonomial, coeff_smul, RingHom.id_apply]

theorem coeff_strip (v : σ) (e : ℕ) (n : σ →₀ ℕ) (f : MvPolynomial σ ℚ_[p]) :
    coeff n (strip p v e f) = if n v = 0 then coeff (Finsupp.single v e + n) f else 0 := by
  classical
  show coeff n ((initPart v e f).divMonomial (Finsupp.single v e)) = _
  rw [coeff_divMonomial, coeff_initPart_eq_ite]
  by_cases h : n v = 0 <;> simp [h]

theorem strip_monomial_ne (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v ≠ e) :
    strip p v e (monomial m 1) = 0 := by
  classical
  ext n
  rw [coeff_strip, coeff_zero]
  split_ifs with h
  · rw [coeff_monomial, if_neg]
    rintro rfl
    apply hm
    simp [h]
  · rfl

theorem strip_monomial_eq (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    strip p v e (monomial (Finsupp.single v e + m) 1) = monomial m 1 := by
  classical
  ext n
  rw [coeff_strip, coeff_monomial, coeff_monomial]
  by_cases h1 : n v = 0
  · rw [if_pos h1]
    by_cases h2 : m = n
    · subst h2
      simp
    · rw [if_neg h2, if_neg]
      intro h3
      exact h2 (add_left_cancel h3)
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 hm

theorem monomial_single_add (v : σ) (e : ℕ) (m : σ →₀ ℕ) :
    (monomial (Finsupp.single v e + m) 1 : MvPolynomial σ ℚ_[p]) = X v ^ e * monomial m 1 := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

private theorem prod_factorial_single_add_eq_mul (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    ((Finsupp.single v e + m).prod fun _ k => (k.factorial : ℚ_[p])) =
      (e.factorial : ℚ_[p]) * m.prod fun _ k => (k.factorial : ℚ_[p]) := by
  classical
  have hdisj : Disjoint (Finsupp.single v e).support m.support := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' := Finsupp.support_single_subset ha
    rw [Finset.mem_singleton] at ha'
    subst ha'
    exact (Finsupp.mem_support_iff.mp hb) hm
  rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]

private theorem fock_eq_sum_coeff_mul_factorial (F G : MvPolynomial σ ℚ_[p]) (S : Finset (σ →₀ ℕ)) (hS : F.support ⊆ S) :
    fock p F G = ∑ m ∈ S, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  unfold fock
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa [mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fock_eq_zero_of (F G : MvPolynomial σ ℚ_[p]) (h : ∀ m, coeff m F = 0 ∨ coeff m G = 0) : fock p F G = 0 := by
  unfold fock
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases h m with h1 | h1 <;> simp [h1]

theorem coeff_pow_mul_ne (v : σ) (e : ℕ) (y : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) (m : σ →₀ ℕ)
    (hm : m v ≠ e) : coeff m (X v ^ e * y) = 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [one_mul]
    by_contra hc
    have hmem : (m - Finsupp.single v e) ∈ y.support := mem_support_iff.mpr hc
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    have h0 : (m - Finsupp.single v e) v = 0 := hy (Finset.mem_coe.mpr hmem)
    have hle : Finsupp.single v e v ≤ m v := (Finsupp.le_def.1 h) v
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at h0 hle
    omega
  · rfl

theorem fock_pow_mul (v : σ) (e : ℕ) (y z : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) :
    fock p (X v ^ e * y) (X v ^ e * z) = (e.factorial : ℚ_[p]) * fock p y z := by
  classical
  have hy' : ∀ m ∈ y.support, m v = 0 := by
    intro m hm
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    exact hy (Finset.mem_coe.mpr hm)
  have hcoeff : ∀ (u : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ),
      coeff (Finsupp.single v e + m) (X v ^ e * u) = coeff m u := by
    intro u m
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
  have hsub : (X v ^ e * y).support ⊆ y.support.image (fun m => Finsupp.single v e + m) := by
    intro m hm
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
    split_ifs at hm with h
    · rw [Finset.mem_image]
      refine ⟨m - Finsupp.single v e, mem_support_iff.mpr (by simpa using hm), ?_⟩
      exact add_tsub_cancel_of_le h
    · exact absurd rfl hm
  rw [fock_eq_sum_coeff_mul_factorial _ _ _ hsub, Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hcoeff, hcoeff, prod_factorial_single_add_eq_mul v e m (hy' m hm)]
  ring

end Gen

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem xH_le_free (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hy : y ∈ XH p LL J M ρ w) :
    y ∈ FreeOf p (Fin.last K, ρ) := by
  unfold XH XSp at hy
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1).1).2



theorem grSpan_eq (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ grSpan p LLw J M ρ w e ↔
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * y := by
  have hMM := restriction_min_max_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hr hρ hv hP hE hO
  have hGr := graded_eq_holds p K r LLw J M ρ w e hv he
  constructor
  · intro hx
    have hle : grSpan p LLw J M ρ w e ≤
        (XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
          (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
      unfold grSpan
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨h, hh, rfl⟩ := (hGr z).mp hz
      refine Submodule.mem_map.mpr ⟨initPart (Fin.last K, ρ) 0 h, (hMM _).mpr ⟨h, ?_, rfl⟩, rfl⟩
      exact (Submodule.mem_inf.mp hh).1
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hle hx)
    exact ⟨y, hy, hyx.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := (hMM y).mp hy
    obtain ⟨n, hn⟩ := exists_pow_smul_intPol h
    have h1 : ((p : ℚ_[p]) ^ n) • h ∈
        MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ hh, hn⟩
    have h2 : X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ n) • h) ∈
        grSpan p LLw J M ρ w e := Submodule.subset_span ((hGr _).mpr ⟨_, h1, rfl⟩)
    have h3 := (grSpan p LLw J M ρ w e).smul_mem (((p : ℚ_[p]) ^ n)⁻¹) h2
    rwa [initPart_smul, mul_smul_comm, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul] at h3

end Last


theorem projAtOf_of (hX : ProjX) : ProjAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 h1 h2 h3 h5 h6
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  have hgr := grSpan_eq LLw J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  have hfree : ∀ g ∈ grSpan p LLw J M ρ w e,
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        y ∈ FreeOf p (Fin.last K, ρ) ∧ g = X (Fin.last K, ρ) ^ e * y := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hgr g).mp hg
    exact ⟨y, hy, xH_le_free _ J _ ρ _ y hy, rfl⟩
  by_cases hme : m (Fin.last K, ρ) = e
  · have hle : Finsupp.single (Fin.last K, ρ) e ≤ m := by
      rw [Finsupp.single_le_iff]
      exact hme.ge
    obtain ⟨m', hm'v, hmm⟩ : ∃ m' : Fin (K + 1) × Fin r →₀ ℕ, m' (Fin.last K, ρ) = 0 ∧
        m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, by simp [hme], (add_tsub_cancel_of_le hle).symm⟩
    subst hmm
    have hMD : MultiDeg (setLast LLw (LLw.deg (Fin.last K) - e)) m' := by
      unfold MultiDeg at hm ⊢
      intro i
      have hi := hm i
      change _ = Function.update LLw.deg (Fin.last K) (LLw.deg (Fin.last K) - e) i
      rw [Function.update_apply]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
        Prod.mk.injEq] at hi
      by_cases hik : i = Fin.last K
      · subst hik
        simp at hi
        rw [if_pos rfl]
        omega
      · have hik' : ¬ Fin.last K = i := fun h => hik h.symm
        simp [hik'] at hi
        rw [if_neg hik]
        exact hi
    obtain ⟨hP1, hP2, hP3⟩ := hPr' m' hMD hm'v
    have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial (Finsupp.single (Fin.last K, ρ) e + m') 1) = X (Fin.last K, ρ) ^ e * Pr' (monomial m' 1) := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, strip_monomial_eq _ _ _ hm'v]
    rw [hPr]
    refine ⟨(hgr _).mpr ⟨_, hP1, rfl⟩, ?_, ?_⟩
    · unfold IntPol at hP2 ⊢
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hP2
      refine LinearMap.mem_range.mpr ⟨X (Fin.last K, ρ) ^ e * z, ?_⟩
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) z = _ at hz
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (X (Fin.last K, ρ) ^ e * z) = _
      rw [map_mul, map_pow, map_X, hz, mul_smul_comm]
    · intro g hg
      obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
      rw [fock_pow_mul _ _ _ _ hyf, hP3 y hy, monomial_single_add, fock_pow_mul _ _ _ _ hyf]
  · have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial m 1) = 0 := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, strip_monomial_ne _ _ _ hme, map_zero, map_zero]
    rw [hPr]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
    rw [fock_eq_zero_of _ _ (fun n => Or.inr (coeff_zero n)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · subst hn
      exact Or.inl (coeff_pow_mul_ne _ _ _ hyf _ hme)
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]


end Formalism.InvariantFactorPaths.L4
end
