import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondence
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.TorusExt

open ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem value_indep (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ)
    (hF : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y)
    {y y' b b' : Frame X.Ψ r} (hy : IsUnitFr X y) (hy' : IsUnitFr X y') (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul y b = rmul y' b') : bchar la b * F y = bchar la b' * F y' := by
  have hi := ExtFPf.invF_mem X hb'
  have hc := ExtFPf.mul_mem X hb hi
  have e : rmul y (rmul b (ExtFPf.invF X b')) = y' := by
    rw [← ExtFPf.rmul_assoc, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb', ExtFPf.rmul_oneF]
  have h1 := hF y hy _ hc (by rw [e]; exact hy')
  rw [e, ExtFPf.bchar_mul X la hb hi] at h1
  have h2 : bchar la b' * bchar la (ExtFPf.invF X b') = 1 := by
    rw [← ExtFPf.bchar_mul X la hb' hi, ExtFPf.rmul_invF X hb', ExtFPf.bchar_oneF]
  rw [h1]
  linear_combination (-(bchar la b * F y)) * h2

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  intro E _ _ _ r X la F hF
  obtain ⟨-, hex, huniq, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames E r X
  have hF' : ∀ y, IsUnitFr X y → ∀ c ∈ Bor X.Ψ r, IsUnitFr X (rmul y c) → F (rmul y c) = bchar la c * F y := by
    intro y hy c hc hyc
    obtain ⟨t, rfl⟩ := huniq y hy c hc hyc
    exact hF y hy t
  let D : Frame X.Ψ r → Prop := fun x => ∃ p : Frame X.Ψ r × Frame X.Ψ r,
    IsUnitFr X p.1 ∧ p.2 ∈ Bor X.Ψ r ∧ x = rmul p.1 p.2
  let Q : Frame X.Ψ r → ℂ := fun x => if h : D x then bchar la h.choose.2 * F h.choose.1 else 0
  have hQ : ∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * F y := by
    intro y hy b hb
    have hD : D (rmul y b) := ⟨(y, b), hy, hb, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hD.choose_spec
    show (if h : D (rmul y b) then bchar la h.choose.2 * F h.choose.1 else 0) = _
    rw [dif_pos hD]
    exact (value_indep X la F hF' hy h1 hb h2 h3).symm
  refine ⟨Q, fun y hy => ?_, fun x hx b hb => ?_⟩
  · have := hQ y hy _ (ExtFPf.oneF_mem X)
    rwa [ExtFPf.rmul_oneF, ExtFPf.bchar_oneF, one_mul] at this
  · obtain ⟨y, hy, c, hc, rfl⟩ := hex x hx
    rw [ExtFPf.rmul_assoc, hQ y hy _ (ExtFPf.mul_mem X hc hb), hQ y hy c hc, ExtFPf.bchar_mul X la hc hb]
    ring

end GlobalTheory.HolRead.TorusExt
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  atlas_forward_decl GlobalTheory.HolRead.TorusExt.exists_extension
end

section
section
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HolRead Filter
open scoped Topology Classical

namespace GlobalTheory.HolRead.Holo

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem differentiableAt_of_chart (Φ : V → V) (G F : V → ℂ) (M : V →L[ℝ] ℂ)
    (hΦ : HasStrictFDerivAt Φ (ContinuousLinearMap.id ℝ V) 0) (hF : HasFDerivAt F M 0)
    (hGF : ∀ᶠ w in 𝓝 (0 : V), G (Φ w) = F w) (hM : ∀ v, M (Complex.I • v) = Complex.I * M v) :
    DifferentiableAt ℂ G (Φ 0) := by
  have hΦ' : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0 := hΦ
  set g := hΦ'.localInverse Φ _ 0 with hg
  have hg0 : g (Φ 0) = 0 := hΦ'.localInverse_apply_image
  have hgd : HasStrictFDerivAt g (((ContinuousLinearEquiv.refl ℝ V).symm : V ≃L[ℝ] V) : V →L[ℝ] V) (Φ 0) :=
    hΦ'.to_localInverse
  have hri : ∀ᶠ w in 𝓝 (Φ 0), Φ (g w) = w := hΦ'.eventually_right_inverse
  have ht : Tendsto g (𝓝 (Φ 0)) (𝓝 0) := by
    have := hgd.continuousAt.tendsto
    rwa [hg0] at this
  have heq : G =ᶠ[𝓝 (Φ 0)] fun w => F (g w) := by
    filter_upwards [hri, ht.eventually hGF] with w h1 h2
    rw [← h2, h1]
  have hF' : HasFDerivAt F M (g (Φ 0)) := by rw [hg0]; exact hF
  have h1 : HasFDerivAt G M (Φ 0) := by
    have := (hF'.comp (Φ 0) hgd.hasFDerivAt).congr_of_eventuallyEq heq
    simpa using this
  let M' : V →L[ℂ] ℂ :=
    { toFun := M
      map_add' := M.map_add
      map_smul' := fun c v => by
        have h : c • v = c.re • v + c.im • (Complex.I • v) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul]; simp
        rw [h, map_add, map_smul, map_smul, hM]
        simp only [Complex.real_smul, RingHom.id_apply, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring
      cont := M.cont }
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := M') h1 rfl).differentiableAt

end General

variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}

def oneFr (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_apply (x y : Frame Ψ r) (τ : Ψ) (a c : Fin r) : rmul x y τ a c = ∑ k, x τ a k * y τ k c := rfl

theorem rmul_assoc (x y z : Frame Ψ r) : rmul (rmul x y) z = rmul x (rmul y z) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat y τ) (mat z τ)

theorem rmul_one (x : Frame Ψ r) : rmul x (oneFr Ψ r) = x := by
  funext τ
  exact Matrix.mul_one (mat x τ)

theorem one_rmul (x : Frame Ψ r) : rmul (oneFr Ψ r) x = x := by
  funext τ
  exact Matrix.one_mul (mat x τ)

theorem expFr_zero : expFr (0 : Frame Ψ r) = oneFr Ψ r := by
  funext τ
  exact (NormedSpace.exp_zero : NormedSpace.exp (0 : Matrix (Fin r) (Fin r) ℂ) = 1)

def mulL (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r →L[ℝ] Frame Ψ r →L[ℝ] Frame Ψ r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Frame Ψ r →ₗ[ℝ] Frame Ψ r) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ rmul
        (fun x x' y => by funext τ a c; simp [rmul_apply, add_mul, Finset.sum_add_distrib])
        (fun t x y => by funext τ a c; simp [rmul_apply, Finset.mul_sum, mul_assoc])
        (fun x y y' => by funext τ a c; simp [rmul_apply, mul_add, Finset.sum_add_distrib])
        (fun t x y => by funext τ a c; simp [rmul_apply, Finset.mul_sum, mul_left_comm]))

theorem mulL_apply (x y : Frame Ψ r) : mulL Ψ r x y = rmul x y := rfl

open scoped Matrix.Norms.Operator in
theorem hasStrict_exp_entry (a c : Fin r) :
    HasStrictFDerivAt (fun Z : Fin r → Fin r → ℂ => (NormedSpace.exp (Matrix.of Z) : Matrix (Fin r) (Fin r) ℂ) a c)
      ((ContinuousLinearMap.proj c : (Fin r → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin r → Fin r → ℂ) →L[ℝ] (Fin r → ℂ))) 0 := by
  let i : (Fin r → Fin r → ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  let p : Matrix (Fin r) (Fin r) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)
  have h0 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin r) (Fin r) ℂ → _) (1 : _ →L[ℝ] _) (i 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have h := p.hasStrictFDerivAt.comp 0 (h0.comp 0 i.hasStrictFDerivAt)
  exact h

theorem hasStrict_expFr : HasStrictFDerivAt (expFr : Frame Ψ r → Frame Ψ r) (ContinuousLinearMap.id ℝ _) 0 := by
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun a => hasStrictFDerivAt_pi'.2 fun c => ?_
  have h := (hasStrict_exp_entry a c).comp (0 : Frame Ψ r)
    (ContinuousLinearMap.proj τ : Frame Ψ r →L[ℝ] (Fin r → Fin r → ℂ)).hasStrictFDerivAt
  exact h

def projU (Ψ : Finset (E →+* ℂ)) (r p : ℕ) : Frame Ψ r →L[ℝ] Frame Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W τ a b => if b < a then W τ a b else
        if a < b then -((sgn p a : ℝ) : ℂ) * ((sgn p b : ℝ) : ℂ) * (starRingEnd ℂ) (W τ b a) else 0
      map_add' := fun W W' => by
        funext τ a b
        simp only [Pi.add_apply, map_add]
        split_ifs <;> ring
      map_smul' := fun t W => by
        funext τ a b
        simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        split_ifs <;> ring }

theorem projU_apply (p : ℕ) (W : Frame Ψ r) (τ : Ψ) (a b : Fin r) : projU Ψ r p W τ a b =
    if b < a then W τ a b else
      if a < b then -((sgn p a : ℝ) : ℂ) * ((sgn p b : ℝ) : ℂ) * (starRingEnd ℂ) (W τ b a) else 0 := rfl

theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> simp

theorem projU_mem [NumberField E] [IsCMField E] (X : Data E r) (W : Frame X.Ψ r) :
    projU X.Ψ r X.p0 W ∈ unitLie X := by
  intro τ
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, mat,
    Matrix.of_apply, projU_apply, Matrix.zero_apply]
  have ha := sgn_mul_self X.p0 a
  have hb := sgn_mul_self X.p0 b
  rcases lt_trichotomy a b with h | h | h
  · simp only [h, h.not_gt, if_true, if_false, RCLike.star_def]
    linear_combination (-(sgn X.p0 b : ℂ) * (starRingEnd ℂ) (W τ b a)) * ha
  · subst h; simp
  · simp only [h, h.not_gt, if_true, if_false, RCLike.star_def, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_conj]
    linear_combination (-(sgn X.p0 a : ℂ) * W τ a b) * hb

theorem smul_mem_unitLie [NumberField E] [IsCMField E] (X : Data E r) (t : ℝ) {Z : Frame X.Ψ r} (hZ : Z ∈ unitLie X) :
    t • Z ∈ unitLie X := by
  intro τ
  have h := congrArg (fun M => t • M) (hZ τ)
  have : mat (t • Z) τ = t • mat Z τ := rfl
  rw [this, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
  simpa using h

theorem frame_eq_sum (W : Frame Ψ r) : W = ∑ τ, ∑ a, ∑ b, W τ a b • unitFr τ a b := by
  funext τ' a' b'
  simp [Finset.sum_apply, unitFr, ite_and]

theorem ell_projU_I [NumberField E] [IsCMField E] (X : Data E r) (ℓ : Frame X.Ψ r →L[ℝ] ℂ)
    (h : ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
      Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) (W : Frame X.Ψ r) :
    ℓ (projU X.Ψ r X.p0 (Complex.I • W)) = Complex.I * ℓ (projU X.Ψ r X.p0 W) := by
  set P := projU X.Ψ r X.p0 with hP
  have key : ∀ (τ : X.Ψ) (a b : Fin r), ℓ (P (Complex.I • unitFr τ a b)) = Complex.I * ℓ (P (unitFr τ a b)) := by
    intro τ a b
    by_cases hab : b < a
    · have ha := sgn_mul_self X.p0 a
      have hb := sgn_mul_self X.p0 b
      set t : ℝ := -(sgn X.p0 a * sgn X.p0 b) / 2 with ht
      have h1 := h τ b a hab _ (smul_mem_unitLie X t (projU_mem X (unitFr τ a b))) _
        (smul_mem_unitLie X t (projU_mem X (Complex.I • unitFr τ a b))) (by
          funext τ' c d
          simp only [Pi.add_apply, Pi.smul_apply, projU_apply, unitFr, smul_eq_mul, Complex.real_smul, map_mul,
            Complex.conj_I]
          rcases lt_trichotomy c d with hcd | hcd | hcd
          · simp only [hcd, hcd.not_gt, if_true, if_false]
            by_cases hc : τ' = τ ∧ c = b ∧ d = a
            · obtain ⟨rfl, rfl, rfl⟩ := hc
              simp only [and_self, if_true, map_one, ht]
              push_cast
              linear_combination (-((sgn X.p0 c : ℂ) ^ 2 * (sgn X.p0 d : ℂ) ^ 2) / 2) * Complex.I_mul_I +
                ((sgn X.p0 c : ℂ) * (sgn X.p0 c : ℂ)) * ha + hb
            · have hc' : ¬ (τ' = τ ∧ d = a ∧ c = b) := fun h' => hc ⟨h'.1, h'.2.2, h'.2.1⟩
              simp [hc, hc']
          · subst hcd
            have hc : ¬ (τ' = τ ∧ c = b ∧ c = a) := fun h' => hab.ne (h'.2.1.symm.trans h'.2.2)
            simp [hc]
          · have hc : ¬ (τ' = τ ∧ c = b ∧ d = a) := fun h' => by
              obtain ⟨-, rfl, rfl⟩ := h'
              exact hab.not_gt hcd
            simp only [hcd, if_true, hc, if_false]
            linear_combination ((t : ℂ) * if τ' = τ ∧ c = a ∧ d = b then 1 else 0) * Complex.I_mul_I)
      rw [map_smul, map_smul, Complex.real_smul, Complex.real_smul] at h1
      have htt : (t : ℂ) * (-2 * ((sgn X.p0 a : ℂ) * (sgn X.p0 b : ℂ))) = 1 := by
        rw [ht]; push_cast
        linear_combination ((sgn X.p0 b : ℂ) * (sgn X.p0 b : ℂ)) * ha + hb
      have ht0 : (t : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one htt
      refine mul_left_cancel₀ ht0 ?_
      linear_combination (-Complex.I) * h1 + ((t : ℂ) * ℓ (P (Complex.I • unitFr τ a b))) * Complex.I_mul_I
    · have h0 : ∀ z : ℂ, P (z • unitFr τ a b) = 0 := by
        intro z
        funext τ' c d
        simp only [hP, projU_apply, unitFr, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rcases lt_trichotomy c d with hcd | hcd | hcd
        · have hc : ¬ (τ' = τ ∧ d = a ∧ c = b) := fun h' => by
            obtain ⟨-, rfl, rfl⟩ := h'
            exact hab hcd
          simp [hcd.not_gt, hc]
        · simp [hcd]
        · have hc : ¬ (τ' = τ ∧ c = a ∧ d = b) := fun h' => by
            obtain ⟨-, rfl, rfl⟩ := h'
            exact hab hcd
          simp [hcd, hc]
      have h1 := h0 1
      rw [one_smul] at h1
      rw [h0, h1]; simp
  have key2 : ∀ (z : ℂ) (τ : X.Ψ) (a b : Fin r),
      ℓ (P (z • unitFr τ a b)) = z * ℓ (P (unitFr τ a b)) := by
    intro z τ a b
    have h : z • unitFr τ a b = z.re • unitFr τ a b + z.im • (Complex.I • unitFr τ a b) := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [add_smul, mul_smul]; simp
    rw [h]
    simp only [map_add, map_smul, key, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im z]
    ring
  conv_lhs => rw [frame_eq_sum W]
  conv_rhs => rw [frame_eq_sum W]
  simp only [Finset.smul_sum, smul_smul, map_sum, key2, Finset.mul_sum, mul_assoc]

theorem differentiableAt_bchar (la : Wt Ψ r) :
    DifferentiableAt ℂ (fun W : Frame Ψ r => bchar la (oneFr Ψ r + W)) 0 := by
  unfold bchar
  have hp : ∀ {ι : Type} (u : Finset ι) (f : ι → Frame Ψ r → ℂ), (∀ i ∈ u, DifferentiableAt ℂ (f i) 0) →
      DifferentiableAt ℂ (fun W => ∏ i ∈ u, f i W) 0 := fun u f hf =>
    (HasFDerivAt.finset_prod fun i hi => (hf i hi).hasFDerivAt).differentiableAt
  refine hp _ _ fun τ _ => hp _ _ fun i _ => ?_
  refine DifferentiableAt.zpow ?_ (Or.inl ?_)
  · simp only [Pi.add_apply]
    fun_prop
  · show (1 : Matrix (Fin r) (Fin r) ℂ) i i + 0 ≠ 0
    simp

theorem differentiableAt_unit [NumberField E] [IsCMField E] (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hQ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (y : Frame X.Ψ r)
    (hy : ∀ Z ∈ unitLie X, rmul y (expFr Z) ∈ X.dom) (ℓ : Frame X.Ψ r →L[ℝ] ℂ)
    (hℓ : HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0)
    (h : ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
      Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) :
    DifferentiableAt ℂ (fun w => Q (rmul y w)) (oneFr X.Ψ r) := by
  set P := projU X.Ψ r X.p0 with hP
  have hP0 : P 0 = 0 := map_zero P
  let Φ : Frame X.Ψ r → Frame X.Ψ r := fun W => rmul (expFr (P W)) (oneFr X.Ψ r + (W - P W))
  have hΦ0 : Φ 0 = oneFr X.Ψ r := by
    simp only [Φ, hP0, expFr_zero, one_rmul, sub_zero, add_zero]
  have hΦ : HasStrictFDerivAt Φ (ContinuousLinearMap.id ℝ _) 0 := by
    have h1 : HasStrictFDerivAt (fun W => expFr (P W)) ((ContinuousLinearMap.id ℝ _).comp P) 0 :=
      HasStrictFDerivAt.comp (g := expFr) 0 (by rw [hP0]; exact hasStrict_expFr) P.hasStrictFDerivAt
    have h2 : HasStrictFDerivAt (fun W => oneFr X.Ψ r + (W - P W)) (ContinuousLinearMap.id ℝ _ - P) 0 :=
      ((hasStrictFDerivAt_id (0 : Frame X.Ψ r)).sub P.hasStrictFDerivAt).const_add _
    have h3 := (mulL X.Ψ r).hasStrictFDerivAt_of_bilinear h1 h2
    refine h3.congr_fderiv ?_
    ext1 W
    simp [mulL_apply, hP0, expFr_zero, one_rmul, rmul_one]
  obtain ⟨χ', hχ⟩ := differentiableAt_bchar (Ψ := X.Ψ) (r := r) la
  have hq : HasFDerivAt (fun W => Q (rmul y (expFr (P W)))) (ℓ.comp P) 0 := by
    have h1 : HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) (P 0) := by
      rw [hP0]; exact hℓ
    exact h1.comp_hasFDerivAt 0 P.hasFDerivAt (Eventually.of_forall fun W => projU_mem X W)
  have hF := (hχ.restrictScalars ℝ).mul hq
  have hdet : ∀ᶠ W in 𝓝 (0 : Frame X.Ψ r), ∀ τ, (mat (oneFr X.Ψ r + (W - P W)) τ).det ≠ 0 := by
    refine eventually_all.2 fun τ => ?_
    have hc : Continuous fun W : Frame X.Ψ r => (mat (oneFr X.Ψ r + (W - P W)) τ).det :=
      Continuous.matrix_det (A := fun W : Frame X.Ψ r => mat (oneFr X.Ψ r + (W - P W)) τ)
        ((continuous_apply τ).comp (continuous_const.add (continuous_id.sub P.continuous)))
    refine hc.continuousAt.eventually_ne ?_
    rw [hP0, sub_zero, add_zero]
    exact (Matrix.det_one.trans_ne one_ne_zero : (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0)
  rw [← hΦ0]
  refine differentiableAt_of_chart Φ _ _ _ hΦ hF ?_ ?_
  · filter_upwards [hdet] with W hW
    have hb : oneFr X.Ψ r + (W - P W) ∈ Bor X.Ψ r := fun τ => ⟨hW τ, fun a c hca => by
      show (1 : Matrix (Fin r) (Fin r) ℂ) a c + (W τ a c - projU X.Ψ r X.p0 W τ a c) = 0
      simp [projU_apply, hca, Matrix.one_apply_ne hca.ne']⟩
    have hχ2 : bchar la (oneFr X.Ψ r + (W - P W)) = bchar la (oneFr X.Ψ r + W) := by
      simp [bchar, hP, projU_apply]
    simp only [Φ, Pi.mul_apply]
    rw [← rmul_assoc, hQ _ (hy _ (projU_mem X W)) _ hb, hχ2]
  · intro v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, hP, ell_projU_I X ℓ h]
    ring

def invFr (x : Frame Ψ r) : Frame Ψ r := fun τ => ((mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_invFr {x : Frame Ψ r} (hx : ∀ τ, (mat x τ).det ≠ 0) : rmul x (invFr x) = oneFr Ψ r := by
  funext τ
  exact Matrix.mul_nonsing_inv (mat x τ) (hx τ).isUnit

theorem invFr_rmul {x : Frame Ψ r} (hx : ∀ τ, (mat x τ).det ≠ 0) : rmul (invFr x) x = oneFr Ψ r := by
  funext τ
  exact Matrix.nonsing_inv_mul (mat x τ) (hx τ).isUnit

theorem invFr_mem_Bor {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : invFr b ∈ Bor Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := (hb τ).1.isUnit
  refine ⟨(Matrix.isUnit_nonsing_inv_det (mat b τ) hu).ne_zero, fun a c hca => ?_⟩
  letI := Matrix.invertibleOfIsUnitDet _ hu
  have hT : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
  exact Matrix.blockTriangular_inv_of_blockTriangular hT hca

theorem differentiableOn_of_killed (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hQ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x)
    (hk : ∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ,
      HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧
      ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X,
        Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) :
    DifferentiableOn ℂ Q X.dom := by
  obtain ⟨g1, g2, -, g4, -, g6, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames E r X
  intro x hx
  obtain ⟨y, hy, b, hb, rfl⟩ := g2 x hx
  obtain ⟨ℓ, hℓ, h⟩ := hk y hy
  have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (g1 y hy τ).1
  have hbd : ∀ τ, (mat b τ).det ≠ 0 := fun τ => (hb τ).1
  have hG := differentiableAt_unit X la Q hQ y (fun Z hZ => g1 _ (g6 y hy Z hZ)) ℓ hℓ h
  let A : Frame X.Ψ r → Frame X.Ψ r := fun x => rmul (invFr y) (rmul x (invFr b))
  have hA : Differentiable ℂ A := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [A, rmul_apply]
    fun_prop
  have hA0 : A (rmul y b) = oneFr X.Ψ r := by
    simp only [A]
    rw [rmul_assoc, rmul_invFr hbd, rmul_one, invFr_rmul hyd]
  have hcomp : DifferentiableAt ℂ (fun x => bchar la b * Q (rmul y (A x))) (rmul y b) :=
    (DifferentiableAt.comp (g := fun w => Q (rmul y w)) _ (by rw [hA0]; exact hG) (hA _)).const_mul _
  have key : ∀ x ∈ X.dom, Q x = bchar la b * Q (rmul y (A x)) := by
    intro x hx
    simp only [A]
    rw [← rmul_assoc, rmul_invFr hyd, one_rmul, ← hQ _ (g4 x hx _ (invFr_mem_Bor hb)) b hb, rmul_assoc,
      invFr_rmul hbd, rmul_one]
  exact hcomp.differentiableWithinAt.congr key (key _ hx)

end GlobalTheory.HolRead.Holo
end
end

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ), (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → (∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ, HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧ ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X, Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) → DifferentiableOn ℂ Q X.dom := by
  atlas_forward_decl GlobalTheory.HolRead.Holo.differentiableOn_of_killed
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AdExt

section Mat
variable {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ}

theorem conj_form (hx : IsUnit x.det) (h : xᴴ * G * x = S) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (x * A * x⁻¹)ᴴ * G * (x * B * x⁻¹) = x⁻¹ᴴ * (Aᴴ * S * B) * x⁻¹ := by
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem isUnit_det_of_sign {q : ℕ} (h : xᴴ * G * x = diagonal fun c : Fin n => if (c : ℕ) < q then (-1 : ℂ) else 1) :
    IsUnit x.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det h
  rw [det_mul, h0, mul_zero, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  split_ifs <;> simp

theorem conj_mem_lie (hx : IsUnit x.det) (h : xᴴ * G * x = S) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * S + S * Z = 0) : (x * Z * x⁻¹)ᴴ * G + G * (x * Z * x⁻¹) = 0 := by
  have h1 := conj_form hx h Z 1
  have h2 := conj_form hx h 1 Z
  rw [Matrix.mul_one, mul_nonsing_inv _ hx] at h1 h2
  rw [Matrix.mul_one] at h1
  rw [conjTranspose_one, Matrix.one_mul] at h2
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]
  simp

theorem conj_mem_unitary (hx : IsUnit x.det) (h : xᴴ * G * x = S) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * S * A = S) : (x * A * x⁻¹)ᴴ * G * (x * A * x⁻¹) = G := by
  have h2 := conj_form hx h 1 1
  rw [Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one] at h2
  rw [conj_form hx h, hA, ← h2]

theorem diag_unitary (s : Fin n → ℂ) (t : Fin n → ℝ) :
    (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I))ᴴ * diagonal s *
      (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I)) = diagonal s := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext c
  have : star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Pi.star_apply]
  linear_combination s c * this

theorem half_mem_lie (hG : Gᴴ = G) (hd : IsUnit G.det) (W : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G))) = 0 := by
  have e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hd, Matrix.mul_one]
  have e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

theorem conj_eq_of_mem_lie (hd : IsUnit G.det) {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * G + G * W = 0) :
    -(G⁻¹ * Wᴴ * G) = W := by
  rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]

end Mat

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem atTau_spec (R : RealPoints θ V) (ρ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V ρ * g = gramAt D V ρ) : IsAtTau θ V ρ g (atTau θ V ρ g) := by
  have h : ∃ k, IsAtTau θ V ρ g k := by
    obtain ⟨k, hk, h⟩ := R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by
      change _ᴴ * _ * _ = _
      split_ifs with c
      · subst c; exact hg
      · simp
    exact ⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩
  rw [atTau, dif_pos h]
  exact h.choose_spec

theorem exists_torus (R : RealPoints θ V) {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hx : NegFirst V q x) {w : D.what₂.Tau → Fin V.rank → ℤ} {φ : GA D V → ℂ} (hφ : IsHolFor θ V x w φ)
    (t : D.what₂.Tau → Fin V.rank → ℝ) (s : Finset D.what₂.Tau) :
    ∃ k ∈ GinfC V, (∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) k = if ρ ∈ s then
      x ρ * diagonal (fun c => Complex.exp ((t ρ c : ℂ) * Complex.I)) * (x ρ)⁻¹ else 1) ∧
      ∀ h, φ (h * k) = (∏ ρ ∈ s, Complex.exp (((∑ c, (w ρ c : ℝ) * t ρ c : ℝ) : ℂ) * Complex.I)) * φ h := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun ρ => by simpa using R.2.2.2.2.1 1 (one_mem _) ρ, by simp⟩
  | insert ρ s hρ ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have ha := atTau_spec R ρ (conj_mem_unitary (isUnit_det_of_sign (hx ρ)) (hx ρ) (diag_unitary _ (t ρ)))
    refine ⟨k * _, mul_mem hk ha.1, fun τ => ?_, fun h => ?_⟩
    · rw [R.2.2.2.1, h1]
      by_cases c : τ = ρ
      · subst c
        rw [ha.2.1]; simp [hρ]
      · rw [ha.2.2 _ c]; simp [c]
    · rw [← mul_assoc, hφ.2.2, h2, Finset.prod_insert hρ, mul_assoc]

def toLie (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) : Frame Ψ V.rank →ₗ[ℝ] LieN V where
  toFun Z := fun ρ => ⟨(1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)),
    half_mem_lie (R.1 ρ).1 (R.1 ρ).2 _⟩
  map_add' Z Z' := funext fun ρ => Subtype.ext (by
    have : mat (Z + Z') (σ ρ) = mat Z (σ ρ) + mat Z' (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) • _ + (1 / 2 : ℂ) • _
    simp only [this, conjAt, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]
    module)
  map_smul' c Z := funext fun ρ => Subtype.ext (by
    have : mat (c • Z) (σ ρ) = c • mat Z (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = c • (1 / 2 : ℂ) • _
    simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, star_trivial]
    module)

theorem toLie_val (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ Z ρ).1 =
    (1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := rfl

theorem toLie_I (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ (Complex.I • Z) ρ).1 =
    (Complex.I / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ - conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := by
  have : mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ) := rfl
  rw [toLie_val]
  simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  module

theorem conjAt_unitLie (R : RealPoints θ V) {X : Data D.host.E V.rank}
    {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : NegFirst V X.p0 x) (σ : D.what₂.Tau → X.Ψ)
    {Z : Frame X.Ψ V.rank} (hZ : Z ∈ unitLie X) (ρ : D.what₂.Tau) :
    conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹) = x ρ * mat Z (σ ρ) * (x ρ)⁻¹ := by
  refine conj_eq_of_mem_lie (R.1 ρ).2 (conj_mem_lie (isUnit_det_of_sign (hx ρ)) (hx ρ) ?_)
  have e : (diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1) =
      -diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
    rw [diagonal_neg]
    congr 1
    funext c
    unfold sgn
    split_ifs <;> simp
  rw [e, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, hZ (σ ρ), neg_zero]

theorem fderiv_atPlace (R : RealPoints θ V) {φ : GA D V → ℂ} (g : GA D V)
    (hf : DifferentiableAt ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0) (ρ : D.what₂.Tau) (Y : LieAt V ρ) :
    fderiv ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0 (atPlace V ρ Y : LieN V) = Rder θ V ρ Y.1 φ g := by
  rw [Rder_eq R]
  have h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0 := fun Y' => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y'
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm
  exact h2.deriv.symm

theorem archM_eq (ρ : D.what₂.Tau) (u : GA D V) : archM V (θ ρ) u = infMat D.sp.cm.sig V.gram (θ ρ) u :=
  (RealPts.infMat_eq ..).symm

theorem mat_unitFr {Ψ : Finset (D.host.E →+* ℂ)} {r : ℕ} (τ τ' : Ψ) (c d : Fin r) :
    mat (unitFr τ c d) τ' = if τ' = τ then Matrix.single c d 1 else 0 := by
  ext a b
  by_cases h : τ' = τ
  · simp [mat, unitFr, h, Matrix.single, eq_comm]
  · simp [mat, unitFr, h]

theorem exists_extension (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r)
    (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (φ : GA D V → ℂ) (hθ : IsInfFam θ) (hM : ModelOf V hr X)
    (hx : NegFirst V X.p0 x)
    (hw : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la τ (Fin.cast hr c) = w ρ c)
    (hφ : IsHolFor θ V x w φ) (g : GA D V) :
    ∃ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom ∧
      (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * Q y) ∧
      ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → Q y = φ (g * u) := by
  obtain ⟨U1, U2, -, -, U5⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr X x hθ hM hx
  subst hr
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  let σ : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩
  have σinj : Function.Injective σ := fun a b h => RealPts.tauE_injective D (congrArg Subtype.val h)
  have σsurj : Function.Surjective σ := fun τ => by
    obtain ⟨ρ, h⟩ := (hM.1 τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext h.symm⟩
  have hxu : ∀ ρ, IsUnit (x ρ).det := fun ρ => isUnit_det_of_sign (hx ρ)
  have frIs : ∀ u y, FrIs θ V rfl X x u y ↔ ∀ ρ, mat y (σ ρ) = infMat D.sp.cm.sig V.gram (θ ρ) u * x ρ := by
    intro u y
    constructor
    · intro h ρ
      rw [h ρ (σ ρ) rfl, archM_eq]; rfl
    · intro h ρ τ e
      obtain rfl : τ = σ ρ := Subtype.ext e
      rw [h ρ, archM_eq]; rfl
  have frMul : ∀ u y k b, FrIs θ V rfl X x u y →
      (∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) k = x ρ * mat b (σ ρ) * (x ρ)⁻¹) →
      FrIs θ V rfl X x (u * k) (rmul y b) := by
    intro u y k b h hk
    rw [frIs] at h ⊢
    intro ρ
    change mat y (σ ρ) * mat b (σ ρ) = _
    rw [h, R.2.2.2.1, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ (hxu ρ), Matrix.mul_one]
  let F : Frame X.Ψ V.rank → ℂ := fun y => if h : IsUnitFr X y then φ (g * (U2 y h).choose) else 0
  have hF : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → F y = φ (g * u) := by
    intro u hu y h
    have hy := U1 u y h
    simp only [F, dif_pos hy]
    rw [U5 _ (U2 y hy).choose_spec.1 u hu y (U2 y hy).choose_spec.2 h]
  obtain ⟨Q, Q1, Q2⟩ := GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ X la F (by
    intro y hy t
    obtain ⟨u, hu, h⟩ := U2 y hy
    obtain ⟨k, hk, k1, k2⟩ := exists_torus R hx hφ (fun ρ => t (σ ρ)) Finset.univ
    refine (hF (u * k) (mul_mem hu hk) _ (frMul u y k _ h fun ρ => ?_)).trans ?_
    · rw [k1, if_pos (Finset.mem_univ _)]; rfl
    rw [hF u hu y h, ← mul_assoc, k2]
    congr 1
    unfold bchar
    refine Fintype.prod_bijective σ ⟨σinj, σsurj⟩ _ _ fun ρ => ?_
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [diagonal_apply_eq, ← hw ρ (σ ρ) rfl c, mul_assoc, Complex.exp_int_mul]
    rfl)
  have hQ : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → Q y = φ (g * u) := fun u hu y h => by
    rw [Q1 y (U1 u y h), hF u hu y h]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ X la Q Q2 fun y hy => ?_, Q2, hQ⟩
  obtain ⟨u, hu, h⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0 :=
    (((isSmoothInf_iff φ).1 ((smooth_iff R φ).1 hφ.1) (g * u)).differentiable (by simp)) 0
  let L : Frame X.Ψ V.rank →L[ℝ] LieN V := LinearMap.toContinuousLinearMap (toLie R x σ)
  have hL : ∀ Z, L Z = toLie R x σ Z := fun _ => rfl
  have hv : ∀ Z ∈ unitLie X, ∀ ρ, (toLie R x σ Z ρ).1 = x ρ * mat Z (σ ρ) * (x ρ)⁻¹ := fun Z hZ ρ => by
    rw [toLie_val, conjAt_unitLie R hx σ hZ]
    module
  have hI : ∀ Z ∈ unitLie X, toLie R x σ (Complex.I • Z) = 0 := fun Z hZ => funext fun ρ => Subtype.ext (by
    rw [toLie_I, conjAt_unitLie R hx σ hZ, sub_self, smul_zero]; rfl)
  have key : ∀ Z ∈ unitLie X, Q (rmul y (expFr Z)) = φ (g * u * expInf θ V (L Z)) := by
    intro Z hZ
    have he := isExpFam_expInf R (toLie R x σ Z)
    rw [mul_assoc]
    refine hQ _ (mul_mem hu he.1) _ (frMul u y _ _ h fun ρ => (he.2 ρ).trans ?_)
    refine (congrArg NormedSpace.exp (hv Z hZ ρ)).trans ?_
    rw [Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (hxu ρ))]
    rfl
  have h0 : (0 : Frame X.Ψ V.rank) ∈ unitLie X := fun τ => by
    have : mat (0 : Frame X.Ψ V.rank) τ = 0 := rfl
    simp [this]
  refine ⟨(fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0).comp L, ?_, ?_⟩
  · have hs' : HasFDerivAt (fun Y : LieN V => φ (g * u * expInf θ V Y))
        (fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0) (L 0) := by
      rw [map_zero]; exact hs.hasFDerivAt
    have h1 := hs'.comp (0 : Frame X.Ψ V.rank) L.hasFDerivAt
    exact h1.hasFDerivWithinAt.congr key (key 0 h0)
  · intro τ c d hcd Z hZ Z' hZ' e
    obtain ⟨ρ, rfl⟩ := σsurj τ
    have e1 : toLie R x σ Z = toLie R x σ (unitFr (σ ρ) c d) := by rw [← e, map_add, hI Z' hZ', add_zero]
    have e2 : toLie R x σ Z' = -toLie R x σ (Complex.I • unitFr (σ ρ) c d) := by
      rw [← e, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, map_add, hI Z hZ, map_neg, zero_add, neg_neg]
    have at1 : ∀ Y : LieN V, (∀ ρ', ρ' ≠ ρ → (Y ρ').1 = 0) → Y = atPlace V ρ ⟨(Y ρ).1, (Y ρ).2⟩ := by
      intro Y hY
      funext ρ'
      by_cases cc : ρ' = ρ
      · subst cc; simp only [atPlace, Pi.single_eq_same]; rfl
      · simp only [atPlace, Pi.single_eq_of_ne cc]; exact Subtype.ext (hY ρ' cc)
    have z : ∀ ρ', ρ' ≠ ρ → mat (unitFr (σ ρ) c d) (σ ρ') = 0 := fun ρ' cc => by
      rw [mat_unitFr, if_neg fun e => cc (σinj e)]
    have z' : mat (unitFr (σ ρ) c d) (σ ρ) = Matrix.single c d 1 := by rw [mat_unitFr, if_pos rfl]
    have hneg : ∀ (Y : LieN V) ρ', ((-Y) ρ').1 = -(Y ρ').1 := fun _ _ => rfl
    have a1 := at1 (toLie R x σ Z) fun ρ' cc => by rw [e1, toLie_val, z ρ' cc]; simp [conjAt]
    have a2 := at1 (toLie R x σ Z') fun ρ' cc => by rw [e2, hneg, toLie_I, z ρ' cc]; simp [conjAt]
    have hk := congrFun (hφ.2.1 ρ c d hcd) (g * u)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hL, hL, a1, a2, fderiv_atPlace R _ hs,
      fderiv_atPlace R _ hs]
    have v1 : (toLie R x σ Z ρ).1 = (1 / 2 : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ +
        conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹)) := by rw [e1, toLie_val, z']
    have v2 : (toLie R x σ Z' ρ).1 = (1 / (2 * Complex.I) : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ -
        conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹)) := by
      rw [e2, hneg, toLie_I, z', ← neg_smul]
      congr 1
      field_simp
      simp
    change Rder θ V ρ (toLie R x σ Z ρ).1 φ _ + _ * Rder θ V ρ (toLie R x σ Z' ρ).1 φ _ = 0
    rw [v1, v2]
    exact hk

end GlobalTheory.HolRead.AdExt
end
end
