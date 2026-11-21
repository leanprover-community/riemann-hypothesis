import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepWN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GramSuppCmpK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_exp (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C : ℂ) (B : d.MF → d.MF), C ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', hC, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', by exact_mod_cast hC.ne',
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e, hfact _ Ψ' hΨ']
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, hmat,
    _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_zero (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) (y : GR d.n) : L y 0 = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  have h0 : IsSw (0 : d.LF) := ⟨0, by ext; simp⟩
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ h0
  have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hT']; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens])
  have e := (hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'
  rw [hΦ0, map_zero, d.T_zero] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ (C s κ : ℂ) (ε : ℤˣ), s ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
      ‖s‖ = 2 ∧ ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, B, -, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C s) B := hW
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 := by
    rw [hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsn
    norm_num at hsn
  have hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
    rw [R.isW_eps w hw₀]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩
    · rw [he, hz]; simp
    · rw [he, hz]; simp [Complex.inv_I]
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨C, s, 1, ε, hs, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_, hsn, hη⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨C, s, κ, ε, hs, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_, hsn, hη⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end
