import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section wirt1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dz (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 - Complex.I • fderiv ℝ f τ Complex.I)

def dzb (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I)

theorem hasFDerivAt_norm1 {τ : ℂ} (hτ : τ ≠ 0) :
    HasFDerivAt (fun σ : ℂ => ‖σ‖) ((1 / (2 * Real.sqrt (‖τ‖ ^ 2))) • (2 • innerSL ℝ τ)) τ := by
  have h2 : HasFDerivAt (fun σ : ℂ => ‖σ‖ ^ 2) (2 • innerSL ℝ τ) τ := (hasStrictFDerivAt_norm_sq τ).hasFDerivAt
  have h1 := h2.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hτ))
  have e : (fun σ : ℂ => Real.sqrt (‖σ‖ ^ 2)) = fun σ => ‖σ‖ := funext fun σ => Real.sqrt_sq (norm_nonneg σ)
  rw [e] at h1
  exact h1

theorem fderiv_norm_apply {τ : ℂ} (hτ : τ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖) τ v = ‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im) := by
  rw [(hasFDerivAt_norm1 hτ).fderiv]
  have hs : Real.sqrt (‖τ‖ ^ 2) = ‖τ‖ := Real.sqrt_sq (norm_nonneg τ)
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, hs, smul_eq_mul, Complex.inner, nsmul_eq_mul]
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re]
  field_simp
  ring

theorem normPow_deriv_apply {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ v =
      (n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im)) := by
  rw [((hasFDerivAt_norm1 hτ).pow n).fderiv]
  rw [← (hasFDerivAt_norm1 hτ).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, fderiv_norm_apply hτ]

theorem gauge_scalar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) -
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : τ * ((τ.re : ℂ) - Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) -
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (τ * ((τ.re : ℂ) - Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dz_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    τ • dz (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (τ • dz f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dz
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

theorem gauge_scalar_bar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    conj τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) +
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : conj τ * ((τ.re : ℂ) + Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq, mul_comm] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : conj τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) +
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (conj τ * ((τ.re : ℂ) + Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dzb_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    conj τ • dzb (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (conj τ • dzb f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dzb
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar_bar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

end wirt1

section read0

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pt0 {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) : Fin n → ℂ := fun l => PBH.consC τ c (Fin.cast hn.symm l)

def Lz {n : ℕ} : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun l : Fin n => if l.val = 0 then ContinuousLinearMap.id ℝ ℂ else 0

theorem Lz_apply {n : ℕ} (h0 : 0 < n) (v : ℂ) : (Lz (n := n)) v = Pi.single ⟨0, h0⟩ v := by
  funext l
  by_cases hl : l.val = 0
  · have : l = ⟨0, h0⟩ := Fin.ext hl
    subst this
    simp [Lz]
  · have : l ≠ ⟨0, h0⟩ := fun h => hl (by rw [h])
    simp [Lz, hl, this]

theorem hasFDerivAt_base_point {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    HasFDerivAt (pt0 hn c) (Lz (n := n)) τ := by
  have e : pt0 hn c = fun σ => Lz (n := n) σ + pt0 hn c 0 := by
    funext σ l
    show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)
    by_cases hl : l.val = 0
    · simp [PBH.consC, Lz, hl]
    · simp [PBH.consC, Lz, hl]
  rw [e]
  exact (Lz (n := n)).hasFDerivAt.add_const _

theorem base_point_zero_coord {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    pt0 hn c τ ⟨0, by omega⟩ = τ := by
  simp [pt0, PBH.consC]

theorem pointWithZeroSecondCoord_mem_chart_of_restricted {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0) :
    pt0 hn c τ ∈ OmX n := by
  subst hn
  have e : pt0 rfl c τ = PBH.consC τ c := funext fun l => by simp [pt0]
  rw [e]
  exact (PBH.omX_consC hτ c).2 hc

theorem operators_at_base_point {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0)
    (f : (Fin n → ℂ) → E) (hf : DifferentiableAt ℝ f (pt0 hn c τ)) :
    opL (⟨0, by omega⟩ : Fin n) 0 f (pt0 hn c τ) = τ • dz (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 1 f (pt0 hn c τ) = τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 2 f (pt0 hn c τ) = τ⁻¹ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 3 f (pt0 hn c τ) = conj τ • dzb (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 4 f (pt0 hn c τ) = conj τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 5 f (pt0 hn c τ) = (conj τ)⁻¹ • f (pt0 hn c τ) := by
  have hmem := pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ
  have h0 := base_point_zero_coord hn c τ
  have hd : ∀ v, fderiv ℝ (fun σ => f (pt0 hn c σ)) τ v = fderiv ℝ f (pt0 hn c τ) (Pi.single ⟨0, by omega⟩ v) := by
    intro v
    have h := (hf.hasFDerivAt.comp τ (hasFDerivAt_base_point hn c τ)).fderiv
    change fderiv ℝ (f ∘ pt0 hn c) τ v = _
    rw [h, ContinuousLinearMap.comp_apply, Lz_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pOp _ f _ = _
    unfold pOp
    rw [if_pos hmem, h0]
    unfold wirt dz
    rw [hd, hd]
  · show cOp _ f _ = _
    simp only [cOp, h0]
  · show ciOp _ f _ = _
    simp only [ciOp, h0]
  · show pbOp _ f _ = _
    unfold pbOp
    rw [if_pos hmem, h0]
    unfold wirtBar dzb
    rw [hd, hd]
    rfl
  · show cbOp _ f _ = _
    simp only [cbOp, h0]
    rfl
  · show cbiOp _ f _ = _
    simp only [cbiOp, h0]
    rfl

end read0

end Formalism.FourierDecayAlt.P.PBP
end
end

section
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def V1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ (ℂ → E) where
  carrier := {f | ContDiffOn ℝ ∞ f {τ | τ ≠ 0}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change ContDiffOn ℝ ∞ (fun τ => c • f τ) _
    exact hf.const_smul c

theorem isOpen_ne_zero_complex : IsOpen {τ : ℂ | τ ≠ 0} := isOpen_ne

theorem differentiableAt_of_punctured_smooth {f : ℂ → E} (hf : f ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) : DifferentiableAt ℝ f τ :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_ne_zero_complex.mem_nhds hτ)

theorem contDiffOn_fderiv_punctured {f : ℂ → E} (hf : f ∈ V1 E) (v : ℂ) : ContDiffOn ℝ ∞ (fun τ => fderiv ℝ f τ v) {τ | τ ≠ 0} :=
  (hf.fderiv_of_isOpen isOpen_ne_zero_complex (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_wirtinger_dz {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dz f) {τ | τ ≠ 0} := by
  unfold PBP.dz
  exact ((contDiffOn_fderiv_punctured hf 1).sub ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem contDiffOn_wirtinger_dzbar {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dzb f) {τ | τ ≠ 0} := by
  unfold PBP.dzb
  exact ((contDiffOn_fderiv_punctured hf 1).add ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem dz_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (f + g) τ = PBP.dz f τ + PBP.dz g τ := by
  unfold PBP.dz
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add, smul_sub]
  abel

theorem dzb_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (f + g) τ = PBP.dzb f τ + PBP.dzb g τ := by
  unfold PBP.dzb
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

theorem dz_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (c • f) τ = c • PBP.dz f τ := by
  unfold PBP.dz
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

theorem dzb_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (c • f) τ = c • PBP.dzb f τ := by
  unfold PBP.dzb
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

def off0 (f : ℂ → E) : ℂ → E := fun τ => if τ = 0 then 0 else f τ

theorem off_zero_mem_punctured_smooth {f : ℂ → E} (hf : ContDiffOn ℝ ∞ f {τ | τ ≠ 0}) : off0 f ∈ V1 E :=
  hf.congr fun τ hτ => by simp [off0, show τ ≠ 0 from hτ]

theorem cd_id : ContDiffOn ℝ ∞ (fun τ : ℂ => τ) {τ | τ ≠ 0} := contDiffOn_id
theorem cd_conj : ContDiffOn ℝ ∞ (fun τ : ℂ => conj τ) {τ | τ ≠ 0} := Complex.conjCLE.contDiff.contDiffOn
theorem cd_inv : ContDiffOn ℝ ∞ (fun τ : ℂ => τ⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  exact (contDiffAt_inv ℂ (show τ ≠ 0 from hτ)).restrict_scalars ℝ |>.contDiffWithinAt
theorem cd_conjinv : ContDiffOn ℝ ∞ (fun τ : ℂ => (conj τ)⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fun τ : ℂ => conj τ) τ := Complex.conjCLE.contDiff.contDiffAt
  have h2 : conj τ ≠ 0 := by simpa using (show τ ≠ 0 from hτ)
  exact (((contDiffAt_inv ℂ h2).restrict_scalars ℝ).comp τ h1).contDiffWithinAt

def opP (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => τ • PBP.dz f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_id.smul (contDiffOn_wirtinger_dz f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dz_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dz_smul f.2 c hτ]
      simp only [smul_add, smul_comm τ c, smul_comm κ c]

def opPb (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => conj τ • PBP.dzb f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_conj.smul (contDiffOn_wirtinger_dzbar f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dzb_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dzb_smul f.2 c hτ]
      simp only [smul_add, smul_comm (conj τ) c, smul_comm κ c]

def opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : Module.End ℂ (V1 E) where
  toFun f := ⟨fun τ => m τ • f.1 τ, hm.smul f.2⟩
  map_add' f g := by ext τ; simp [smul_add]
  map_smul' c f := by ext τ; simp [smul_comm (m τ) c]

def site1 (κ : ℂ) : Wd.Site (Q.Pr (V1 E)) :=
  ⟨Q.mkP (opP κ) (-(opPb κ)), Q.mkP (opM (fun τ => τ) cd_id) (opM (fun τ => conj τ) cd_conj),
    Q.mkP (opM (fun τ => τ⁻¹) cd_inv) (opM (fun τ => (conj τ)⁻¹) cd_conjinv)⟩

def act1 {S : Type} [Fintype S] [DecidableEq S] (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) : Wd.Ix S → V1 E :=
  fun a => ∑ b, (M a b).1 (x b)

def oneBT {S : Type} [Fintype S] [DecidableEq S] (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    Wd.Ix S → V1 E :=
  act1 (Wd.bT (site1 κ) w) x

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end
