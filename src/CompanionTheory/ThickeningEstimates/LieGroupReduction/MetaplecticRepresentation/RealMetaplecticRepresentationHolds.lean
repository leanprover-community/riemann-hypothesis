import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MpFOne

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpA

theorem dense_sch : DenseRange (schwartzToL2 l) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

def ext (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  (ContinuousLinearEquiv.unitsEquiv ℂ (Sch l) V).toLinearEquiv.extendOfIsometry
    (schwartzToL2 l).toLinearMap (schwartzToL2 l).toLinearMap dense_sch dense_sch fun f => hn f

theorem ext_sch (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

theorem G_ext {g h : G l} (h1 : pr g = pr h) (h2 : om g = om h) (h3 : omS g = omS h) : g = h :=
  Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))

theorem continuous_to {X : Type} [TopologicalSpace X] {F : X → G l} (h1 : Continuous fun x => pr (F x))
    (h2 : ∀ f, Continuous fun x => om (F x) f) : Continuous F :=
  continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))

theorem sp_mul {X : Type} [TopologicalSpace X] {a b : X → Sp l} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))

theorem sp_inv {X : Type} [TopologicalSpace X] {a : X → Sp l} (ha : Continuous a) :
    Continuous fun x => (a x)⁻¹ := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun x => -Matrix.J l ℝ * ((a x : Mat l))ᵀ * Matrix.J l ℝ
  exact (continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const

theorem om_cont2 : Continuous fun p : G l × L2 l => om p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Continuous fun p : G l × L2 l => ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ :=
    (continuous_snd.sub continuous_const).norm.add (((continuous_om q.2).comp continuous_fst).sub continuous_const).norm
  have h2 := h1.tendsto q
  simp only [sub_self, norm_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2
  calc ‖om p.1 p.2 - om q.1 q.2‖ = ‖(om p.1 p.2 - om p.1 q.2) + (om p.1 q.2 - om q.1 q.2)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖om p.1 p.2 - om p.1 q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := norm_add_le _ _
    _ = ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem om_mul (g h : G l) (f : L2 l) : om (g * h) f = om g (om h f) := by
  rw [map_mul]; rfl

abbrev gs (l : Type) [Fintype l] : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)

theorem fderiv_gs (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(gs l)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * gs l x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(gs l) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem ann_gs : Ann (1 : Sp l).1 (gs l) := fun j => by
  have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec]
  ext x
  rw [SchwartzMap.smul_apply, dRho_single_inr, dRho_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  linear_combination fderiv_gs j x - (2 * π * (x j : ℂ) * gs l x) * I_sq

theorem gs_zero : gs l 0 = 1 := by simp

theorem dd_one : dd (1 : Mat l) = 1 := by
  have h : upperParabolic (1 : Mat l) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]
  rw [dd, h, det_one]

theorem eps_mem : Mem ((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l) :=
  ⟨fun f => by simp, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩

def eps : G l := ⟨((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l), eps_mem⟩

theorem om_eps (f : L2 l) : om (eps : G l) f = -f := rfl

theorem omS_eps (f : Sch l) : omS (eps : G l) f = -f := by
  show (((-1 : (Sch l →L[ℂ] Sch l)ˣ) : Sch l →L[ℂ] Sch l)) f = -f
  simp

theorem pr_eps : pr (eps : G l) = 1 := rfl

theorem eps_ne : (eps : G l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : omS (eps : G l) φ = omS (1 : G l) φ := by rw [h]
  rw [omS_eps, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : Sch l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)

theorem om_of_omS {g : G l} {c : ℂ} (hc : ∀ f, omS g f = c • f) (F : L2 l) : om g F = c • F := by
  refine dense_sch.induction_on (p := fun F => om g F = c • F) F
    (isClosed_eq (om g).continuous (continuous_const_smul c)) fun f => ?_
  rw [om_sch, hc, map_smul]

end MpA

open MpA

theorem mkElt : MkElt l := by
  intro s U hU hI hN
  obtain ⟨V, rfl⟩ := hU
  have hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖ := fun f => hI.norm f
  have hsurj : Function.Surjective ⇑(V : Sch l →L[ℂ] Sch l) := fun f => ⟨V⁻¹.1 f, by
    show (V.1 * V⁻¹.1) f = f
    rw [V.mul_inv]; rfl⟩
  have hI' : Impl (⇑(Matrix.mulVecLin s.1)) (V : Sch l →L[ℂ] Sch l).toLinearMap := hI
  have hd : ∀ w f, V.1 (dRho w f) = dRho (s.1 *ᵥ w) (V.1 f) := fun w f => hI'.dRho hsurj w f
  set u := ext V hn with hu
  have hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := fun f => ext_sch V hn f
  have hrho : ∀ w F, u (rho w F) = rho (s.1 *ᵥ w) (u F) := fun w F => by
    refine dense_sch.induction_on (p := fun F => u (rho w F) = rho (s.1 *ᵥ w) (u F)) F
      (isClosed_eq (u.continuous.comp (rho w).continuous) ((rho _).continuous.comp u.continuous)) fun f => ?_
    obtain ⟨g, hg⟩ := exists_rho w f
    have hg' := hI.impl w f g hg
    calc u (rho w (schwartzToL2 l f)) = u (schwartzToL2 l g) := by rw [schwartzToL2_apply, schwartzToL2_apply, toLp_rho hg]
      _ = schwartzToL2 l (V.1 g) := hc g
      _ = rho (s.1 *ᵥ w) (schwartzToL2 l (V.1 f)) := by
        rw [schwartzToL2_apply, schwartzToL2_apply]; exact toLp_rho hg'
      _ = rho (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]
  have hm : Mem ((s, u, V) : Amb l) := ⟨hc, hrho, hd, hN⟩
  exact ⟨(⟨((s, u, V) : Amb l), hm⟩ : sub l), rfl, rfl⟩

theorem topG : TopG l := by
  have hm : ContinuousMul (G l) := ⟨continuous_to (by
      simp only [map_mul]
      exact sp_mul (continuous_pr.comp continuous_fst) (continuous_pr.comp continuous_snd)) fun f => by
      simp only [om_mul]
      exact om_cont2.comp (continuous_fst.prodMk ((continuous_om f).comp continuous_snd))⟩
  have hi : ContinuousInv (G l) := ⟨continuous_to (by
      simp only [map_inv]
      exact sp_inv continuous_pr) fun f => by
      refine continuous_iff_continuousAt.2 fun g0 => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨v, hv⟩ : ∃ v, om g0⁻¹ f = v := ⟨_, rfl⟩
      have hv0 : om g0 v = f := by
        rw [← hv, ← om_mul, mul_inv_cancel, map_one]; rfl
      have key : ∀ g : G l, ‖f - om g v‖ = ‖om g⁻¹ f - v‖ := fun g => by
        rw [← LinearIsometryEquiv.norm_map (om g) (om g⁻¹ f - v), map_sub, ← om_mul, mul_inv_cancel, map_one]
        rfl
      have hc : Continuous fun g : G l => ‖f - om g v‖ := (continuous_const.sub (continuous_om v)).norm
      have h0 := hc.tendsto g0
      rw [hv0, sub_self, norm_zero] at h0
      rw [hv]
      exact h0.congr key⟩
  exact { toContinuousMul := hm, toContinuousInv := hi }

theorem ker : Ker l := by
  refine ⟨eps, eps_ne, fun g => ⟨fun hg => ?_, ?_⟩, om_eps⟩
  · have hsurj : Function.Surjective (omS g) := fun f => ⟨omS g⁻¹ f, by
      show (omS g * omS g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl⟩
    have hpg : ((pr g : Sp l) : Mat l) = 1 := by rw [hg]; rfl
    have hI : Impl id (omS g).toLinearMap := by
      refine ⟨fun f => ?_, fun w f k hk => ?_⟩
      · show ‖schwartzToL2 l (omS g f)‖ = ‖schwartzToL2 l f‖
        rw [← om_sch, LinearIsometryEquiv.norm_map]
      · obtain ⟨k', hk'⟩ := exists_rho w (omS g f)
        have e : omS g k = k' := by
          apply injective_toLp 2 volume
          calc (omS g k).toLp 2 volume = om g (k.toLp 2 volume) := (om_sch g k).symm
            _ = om g (rho w (f.toLp 2 volume)) := by rw [toLp_rho hk]
            _ = rho w (om g (f.toLp 2 volume)) := by rw [om_rho, hpg, one_mulVec]
            _ = rho w ((omS g f).toLp 2 volume) := by rw [← schwartzToL2_apply, om_sch]; rfl
            _ = k'.toLp 2 volume := (toLp_rho hk').symm
        show ⇑(omS g k) = rhoFun w (omS g f)
        rw [e, hk']
    obtain ⟨c, hc⟩ := hI.scalar hsurj
    have hc' : ∀ f, omS g f = c • f := hc
    have hn := omS_nrm g 1 (gs l) ann_gs
    have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
    rw [hpg, e1, Matrix.one_mul, dd_one, hc', SchwartzMap.smul_apply, gs_zero] at hn
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hn
    rcases mul_eq_zero.1 hc2 with h | h
    · left
      have hc1 : c = 1 := sub_eq_zero.1 h
      refine G_ext (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, one_smul, map_one]; rfl
      · rw [hc', hc1, one_smul, map_one]; rfl
    · right
      have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
      refine G_ext (by rw [hg, pr_eps]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, om_eps, neg_one_smul]
      · rw [hc', hc1, omS_eps, neg_one_smul]
  · rintro (rfl | rfl)
    · exact map_one _
    · exact pr_eps

end CompanionTheory.ThKR.Mp

end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

theorem J_mul_transpose_inl (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inl a) j = -s j (.inr a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_mul_transpose_inr (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inr a) j = s j (.inl a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem sp_rel (s : Sp l) (i j : l ⊕ l) :
    ∑ a, (s.1 i (.inr a) * s.1 j (.inl a) - s.1 i (.inl a) * s.1 j (.inr a)) = Matrix.J l ℝ i j := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 s.2) i) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [J_mul_transpose_inl, J_mul_transpose_inr] at h
  rw [← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem ddNe : DdNe l := by
  intro s
  let N : Matrix l (l ⊕ l) ℝ := Matrix.of fun a k => s.1 (.inl a) k
  let K : Matrix (l ⊕ l) l ℝ := Matrix.of fun k b =>
    Sum.elim (fun c => s.1 (.inr b) (.inr c)) (fun c => -s.1 (.inr b) (.inl c)) k
  have hNK : N * K = 1 := by
    ext a b
    have h := sp_rel s (.inl a) (.inr b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [N, K, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    calc _ = -∑ c, (s.1 (.inl a) (.inr c) * s.1 (.inr b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inr b) (.inr c)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [h]; simp [Matrix.J, Matrix.one_apply]
  have hM : (N * Nᵀ).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have h1 : (v ᵥ* N) ⬝ᵥ (v ᵥ* N) = 0 := by
      have : (v ᵥ* (N * Nᵀ)) ⬝ᵥ v = 0 := by rw [hvM, zero_dotProduct]
      rwa [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at this
    have h2 : v ᵥ* N = 0 := dotProduct_self_eq_zero.1 h1
    apply hv
    calc v = v ᵥ* (N * K) := by rw [hNK, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h2, Matrix.zero_vecMul]
  let W : Matrix l l ℂ := Matrix.of fun c b => (s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)
  have hPW : upperParabolic s.1 * W = (N * Nᵀ).map ofReal := by
    ext a b
    have hs := sp_rel s (.inl a) (.inl b)
    simp only [Matrix.J, fromBlocks_apply₁₁, Matrix.zero_apply] at hs
    have e : ∀ c, ((s.1 (.inl a) (.inl c) : ℂ) - I * s.1 (.inl a) (.inr c)) *
        ((s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)) =
        ((s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inl c) + s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) -
        I * ((s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) :=
      fun c => by
        push_cast
        linear_combination (-((s.1 (.inl a) (.inr c) : ℂ) * (s.1 (.inl b) (.inr c) : ℂ))) * I_sq
    simp only [Matrix.mul_apply, upperParabolic, W, Matrix.of_apply, Matrix.map_apply, N, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ofReal_sum, ← ofReal_sum, hs]
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  have e : ((N * Nᵀ).map ofReal).det = ((N * Nᵀ).det : ℂ) := by
    rw [show (N * Nᵀ).map ofReal = ofRealHom.mapMatrix (N * Nᵀ) from rfl, ← RingHom.map_det]
    rfl
  intro h0
  have := congrArg Matrix.det hPW
  rw [Matrix.det_mul, e] at this
  unfold dd at h0
  rw [h0, zero_mul] at this
  exact hM (ofReal_eq_zero.1 this.symm)

def nn (S : Matrix l l ℝ) (t : ℝ) : Mat l := fromBlocks 1 (t • S) 0 1

theorem nn_mem {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) : nn S t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, nn, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS.eq]

theorem upperPart_unipotent_mul (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) :
    upperParabolic (nn S t * s) = upperParabolic s + (t : ℂ) • (S.map ofReal * loQ s) := by
  ext a b
  simp only [upperParabolic, loQ, nn, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ofReal_add, ofReal_sum, ofReal_mul]
  have e : ∀ u v : l → ℝ, ∑ c, (t : ℂ) * (S a c : ℂ) * (u c : ℂ) - I * ∑ c, (t : ℂ) * (S a c : ℂ) * (v c : ℂ) =
      (t : ℂ) * ∑ c, (S a c : ℂ) * ((u c : ℂ) - I * (v c : ℂ)) := fun u v => by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← e]
  ring

theorem loQ_nn (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) : loQ (nn S t * s) = loQ s := by
  ext a b
  simp [loQ, nn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem tc_apply (M : Matrix l l ℝ) (x : Eu l) (a : l) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) M x a = ∑ b, M a b * x b := rfl

theorem metaplectic_unipotent_block_first_diag (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inl Sum.inl (nn S t) = 1 := by
  ext x a
  simp [bl_apply, nn, Matrix.one_apply]

theorem metaplectic_unipotent_block_upper (S : Matrix l l ℝ) (t : ℝ) :
    bl Sum.inl Sum.inr (nn S t) = t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S := by
  ext x a
  simp [bl_apply, nn, tc_apply, Finset.mul_sum, mul_assoc]

theorem metaplectic_unipotent_block_lower (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inr Sum.inl (nn S t) = 0 := by
  ext x a
  simp [bl_apply, nn]

theorem metaplectic_unipotent_block_second_diag (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inr Sum.inr (nn S t) = 1 := by
  ext x a
  simp [bl_apply, nn, Matrix.one_apply]

def UU (S : Matrix l l ℝ) (t : ℝ) : Sch l →L[ℂ] Sch l :=
  fou l * (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) * fouInv l)

theorem inner_sym {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (x y : Eu l) :
    ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) y⟫ =
      ⟪y, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ := by
  have hS' : ∀ a b, S a b = S b a := fun a b => by
    simpa using (congrFun (congrFun hS.eq b) a)
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]
  congr 2
  simp only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hS']
  ring

theorem intw_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : Eu l) :
    Intw (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by
  have h := (intw_fou _ _).mul ((intw_ph (inner_sym hS t) _ _).mul (intw_fouInv p q))
  rw [show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q =
    -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by
      rw [ContinuousLinearMap.neg_apply, neg_add, neg_neg, neg_neg]]
  exact h

theorem impl_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) :
    Impl (fun w => nn S t *ᵥ w) (UU S t).toLinearMap :=
  ⟨fun f => (iso_fou.mul ((iso_ph _).mul iso_fouInv)) f, fun w f g hg => by
    have := intw_UU hS t (pPart w) (qPart w) f g hg
    rw [rhoFun_eq, pPart_mulVec, qPart_mulVec, metaplectic_unipotent_block_first_diag,
      metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metaplectic_unipotent_block_second_diag]
    simpa using this⟩

theorem isUnit_UU (S : Matrix l l ℝ) (t : ℝ) : IsUnit (UU S t) :=
  isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)

theorem UU_dRho {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by
  have hs : Function.Surjective (UU S t).toLinearMap := fun f => ⟨Ring.inverse (UU S t) f, by
    show (UU S t * Ring.inverse (UU S t)) f = f
    rw [Ring.mul_inverse_cancel _ (isUnit_UU S t), ContinuousLinearMap.one_apply]⟩
  exact Impl.dRho (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f

theorem UU_zero (S : Matrix l l ℝ) : UU S 0 = 1 := by
  simp [UU, ph_zero, fou_mul_fouInv]

theorem fou_zero (h : Sch l) : fou l h 0 = ∫ x, h x := by
  rw [fou_apply, fourier_coe, Real.fourier_eq]
  simp

theorem hasDerivAt_UU (S : Matrix l l ℝ) (f : Sch l) (t₀ : ℝ) :
    HasDerivAt (fun t => UU S t f 0)
      (fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l (UU S t₀ f))) 0) t₀ := by
  have e1 : ∀ t, UU S t f 0 = ∫ x, ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x := fun t => by
    rw [UU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fou_zero]
  have e2 : fouInv l (UU S t₀ f) = ph (-(t₀ • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) := by
    rw [UU, ← ContinuousLinearMap.mul_apply, ← mul_assoc, fouInv_mul_fou, one_mul, ContinuousLinearMap.mul_apply]
  have hq : ∀ x : Eu l, |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2 := fun x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x‖
          ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖) := by
            gcongr
            exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S).le_opNorm x
        _ = _ := by ring)
  have ph_eq : ∀ (t : ℝ) (x : Eu l), ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x =
      exp (((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ) * I) * fouInv l f x := fun t x => by
    have : -π * ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t := by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right,
        real_inner_smul_right]
      ring
    rw [ph_apply, this]
  have mq_eq : ∀ (h : Sch l) (x : Eu l), mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) h x =
      ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) * I * h x := fun h x => by
    have : -π * ⟪x, (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ := by
      simp only [ContinuousLinearMap.neg_apply, inner_neg_right]
      ring
    rw [mq_apply, this]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t x => ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x)
    (F' := fun t x => mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S))
      (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) x)
    (bound := fun x => π * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * (‖x‖ ^ 2 * ‖fouInv l f x‖))
    Filter.univ_mem (.of_forall fun t => (ph _ (fouInv l f)).continuous.aestronglyMeasurable)
    ((ph _ (fouInv l f)).integrable) ((mq _ _).continuous.aestronglyMeasurable)
    (.of_forall fun x t _ => by
      rw [mq_eq, ph_eq, norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
      have h1 := hq x
      have h2 := norm_nonneg (fouInv l f x)
      calc π * |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * 1 * (1 * ‖fouInv l f x‖)
          = π * (|⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * ‖fouInv l f x‖) := by ring
        _ ≤ π * ((‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2) * ‖fouInv l f x‖) := by gcongr
        _ = _ := by ring)
    (((fouInv l f).integrable_pow_mul volume 2).const_mul _)
    (.of_forall fun x t _ => by
      simp only [ph_eq, mq_eq]
      have h1 : HasDerivAt (fun t : ℝ => ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ))
          ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul (π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫)).ofReal_comp
        simpa using this
      exact ((h1.mul_const I).cexp.mul_const (fouInv l f x)).congr_deriv (by ring))
  rw [e2, fou_zero]
  exact key.2.congr_of_eventuallyEq (.of_forall e1)

theorem dRho_eval_zero (w : l ⊕ l → ℝ) (h : Sch l) :
    dRho w h 0 = ∑ a, (w (.inl a) : ℂ) * (∂_{(EuclideanSpace.single a 1 : Eu l)} h) 0 := by
  rw [dRho_eq_sum w]
  simp [Fintype.sum_sum_type, dRho_single_inl, dRho_single_inr]

theorem hess {s : Mat l} {H : Sch l} (hA : Ann s H) (j k : l) :
    ∑ a, upperParabolic s a j * (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} H)) 0 =
      -(2 * π * I) * loQ s k j * H 0 := by
  have comm : ∀ w, dRho (Pi.single (.inl k) 1) (dRho w H) =
      dRho w (∂_{(EuclideanSpace.single k 1 : Eu l)} H) + (2 * π * I * sympl (Pi.single (.inl k) 1) w : ℂ) • H :=
    fun w => by
      have := congrArg (fun T : Sch l →L[ℂ] Sch l => T H) (dRho_comm (Pi.single (.inl k) 1) w)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply] at this
      rw [← dRho_single_inl, ← this]
      abel
  have hsy : ∀ w : l ⊕ l → ℝ, sympl (Pi.single (.inl k) 1) w = w (.inr k) := fun w => by
    simp [sympl, pPart, qPart, PiLp.inner_apply, Pi.single_apply]
  have hcol : ∀ b c, (s *ᵥ Pi.single b 1) c = s c b := fun b c => by
    simp [mulVec, dotProduct, Pi.single_apply]
  have e := congrArg (fun u : Sch l => dRho (Pi.single (.inl k) 1) u 0) (hA j)
  simp only [map_smul, SchwartzMap.smul_apply, smul_eq_mul, comm, SchwartzMap.add_apply, dRho_eval_zero, hsy,
    hcol] at e
  simp only [upperParabolic, loQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination e

theorem trace_eq {P Q : Matrix l l ℂ} (hP : P.det ≠ 0) (S M : Matrix l l ℂ) (c : ℂ)
    (h : ∀ j k, ∑ a, P a j * M a k = c * Q k j) : ∑ j, ∑ k, S j k * M j k = c * (P⁻¹ * (S * Q)).trace := by
  have h1 : Pᵀ * M = c • Qᵀ := by
    ext j k
    simp [Matrix.mul_apply, h]
  have hu : IsUnit Pᵀ.det := by
    rw [det_transpose]
    exact hP.isUnit
  have h2 : M = Pᵀ⁻¹ * (c • Qᵀ) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h3 : ∑ j, ∑ k, S j k * M j k = (S * Mᵀ).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h4 : S * (Pᵀ⁻¹ * (c • Qᵀ))ᵀ = c • (S * Q * P⁻¹) := by
    rw [transpose_mul, transpose_smul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
  rw [h3, h2, h4, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hasDerivAt_det (P K : Matrix l l ℂ) (t₀ : ℝ) (hP : (P + (t₀ : ℂ) • K).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (P + (t : ℂ) • K).det)
      ((P + (t₀ : ℂ) • K).det * ((P + (t₀ : ℂ) • K)⁻¹ * K).trace) t₀ := by
  have hu : IsUnit (P + (t₀ : ℂ) • K).det := hP.isUnit
  have e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det *
      (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) +
        (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval
          ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2) := fun t => by
    rw [← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]
    congr 1
    abel
  have hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z +
      (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2)
      ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ) := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add
      ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) •
        ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
    rw [sub_self, ofReal_zero]
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)
  have hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
  have := (hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det
  rw [mul_one] at this
  exact this.congr_of_eventuallyEq (.of_forall e)

theorem nrmUp : NrmUp l := by
  intro S hS s' f hf
  have hPt : ∀ t : ℝ, upperParabolic (nn S t * s'.1) = upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1) := fun t => upperPart_unipotent_mul S t s'.1
  have hdet : ∀ t : ℝ, (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det ≠ 0 := fun t => by
    rw [← hPt]
    exact ddNe ⟨_, mul_mem (nn_mem hS t) s'.2⟩
  have hAnn : ∀ t, Ann (nn S t * s'.1) (UU S t f) := fun t => hf.map (UU_dRho hS t)
  have hF : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0) (-(1 / 2 : ℂ) * UU S t f 0 *
      ((upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1))⁻¹ * (S.map ofReal * loQ s'.1)).trace) t := fun t => by
    have h1 := hasDerivAt_UU S f t
    rw [fou_mq_fouInv] at h1
    simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul] at h1
    have h2 := trace_eq (hdet t) (S.map ofReal)
      (Matrix.of fun a k => (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)}
        (UU S t f))) 0) (-(2 * π * I) * UU S t f 0) (fun j k => by
          have := hess (hAnn t) j k
          rw [hPt, loQ_nn] at this
          simp only [Matrix.of_apply]
          rw [this]
          ring)
    simp only [Matrix.of_apply, Matrix.map_apply] at h2
    rw [h2] at h1
    convert h1 using 1
    have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    ring
  have hh : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0 * UU S t f 0 *
      (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det) 0 t := fun t => by
    exact (((hF t).fun_mul (hF t)).fun_mul (hasDerivAt_det _ _ t (hdet t))).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) 1 0
  have e0 : UU S 0 f = f := by rw [UU_zero]; rfl
  have e1 : UU S 1 f = fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) := by
    simp [UU]
  simp only [e0, e1, ofReal_zero, ofReal_one, zero_smul, add_zero, one_smul] at hc
  rw [sq, sq]
  exact hc

end CompanionTheory.ThKR.Mp
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace C

theorem upperPart_mul (s s' : Mat l) :
    upperParabolic (s * s') = s.toBlocks₁₁.map Complex.ofReal * upperParabolic s' + s.toBlocks₁₂.map Complex.ofReal * loQ s' := by
  ext a b
  have e : ∀ x y : ℂ, x * (I * y) = I * (x * y) := fun x y => mul_left_comm x I y
  simp only [upperParabolic, loQ, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub,
    Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]
  ring

theorem map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

theorem det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

theorem dd_mul_eq (s s' : Mat l) (hd : s.toBlocks₁₁.det ≠ 0) :
    dd (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (upperParabolic s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * loQ s').det := by
  have hu : IsUnit s.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hB : s.toBlocks₁₂.map Complex.ofReal =
      s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal := by
    rw [← map_ofReal_mul, hAS]
  rw [dd, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]

theorem blocks_symm {A B C D : Matrix l l ℝ} (h : fromBlocks A B C D * Matrix.J l ℝ * (fromBlocks A B C D)ᵀ = Matrix.J l ℝ) :
    B * Aᵀ = A * Bᵀ := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h1
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1
  exact add_neg_eq_zero.1 h1

theorem isSymm_inv_mul (s : Sp l) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).IsSymm := by
  have hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ := by
    have h := SymplecticGroup.mem_iff.1 s.2
    rw [← fromBlocks_toBlocks s.1] at h
    exact blocks_symm h
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hut : IsUnit s.1.toBlocks₁₁ᵀ.det := by rw [det_transpose]; exact hu
  show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂
  rw [transpose_mul, transpose_nonsing_inv]
  calc s.1.toBlocks₁₂ᵀ * (s.1.toBlocks₁₁ᵀ)⁻¹
      = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]
    _ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]

theorem sympl_sp (s : Sp l) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem sec_apply_zero (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by
  simp only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply,
    dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]

end C

open C

theorem secEx_of (h1 : MkElt l) (h2 : NrmUp l) : SecEx l := by
  intro s hd
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  let uA : (Eu l →L[ℝ] Eu l)ˣ :=
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹,
      by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩
  have hA : IsUnit (bl Sum.inl Sum.inl s.1) := ⟨uA, rfl⟩
  have hinv : Ring.inverse (bl Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹ :=
    Ring.inverse_unit uA
  have hAiB : Ring.inverse (bl Sum.inl Sum.inl s.1) * bl Sum.inl Sum.inr s.1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by
    rw [hinv, map_mul]
    rfl
  have hdA : (bl Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det := det_bl _ _ _
  have hdet : (Ring.inverse (bl Sum.inl Sum.inl s.1)).det * (bl Sum.inl Sum.inl s.1).det = 1 := by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)
    simpa [ContinuousLinearMap.det] using this
  set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef
  have hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc : c ^ 2 = |(Ring.inverse (bl Sum.inl Sum.inl s.1)).det| := by
    rw [hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'
  obtain ⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧
      (0 < s.1.toBlocks₁₁.det → z = 1) := by
    by_cases hpos : 0 < s.1.toBlocks₁₁.det
    · have e : c ^ 2 * s.1.toBlocks₁₁.det = 1 := by
        rw [hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
      refine ⟨1, by simp, ?_, fun _ => rfl⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e]
      simp
    · have hneg : s.1.toBlocks₁₁.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hd
      have e : c ^ 2 * s.1.toBlocks₁₁.det = -1 := by
        rw [hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      refine ⟨I, by simp, ?_, fun h => absurd h hpos⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e, I_sq]
      push_cast
      ring
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
  have hU : IsUnit (z • sec s.1) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 z hz0).map _).mul (isUnit_big hA.ringInverse _ _ hc0)
  have hiso := iso_big hA.ringInverse (bl Sum.inl Sum.inr s.1) (bl Sum.inr Sum.inl s.1) hc
  have hI : Impl (fun w => s.1 *ᵥ w) (z • sec s.1).toLinearMap := by
    refine ⟨fun f => ?_, fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z⟩
    show ‖schwartzToL2 l ((z • sec s.1) f)‖ = ‖schwartzToL2 l f‖
    rw [ContinuousLinearMap.smul_apply, map_smul, norm_smul, hz1, one_mul]
    exact hiso f
  have hN : Nrm s.1 (z • sec s.1) := by
    intro s' f hf
    have key := h2 _ (isSymm_inv_mul s hd) s' f hf
    have ev : (z • sec s.1) f 0 = z * ((c : ℂ) *
        fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) := by
      rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]
    rw [ev, dd_mul_eq s.1 s'.1 hd, ← key]
    calc _ = (z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ))) *
          ((fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) ^ 2 *
            (upperParabolic s'.1 + (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).map Complex.ofReal * loQ s'.1).det) := by ring
      _ = _ := by rw [hz, one_mul]
  obtain ⟨g, hg1, hg2⟩ := h1 s _ hU hI hN
  exact ⟨g, z, hg1, hg2, hzpos⟩

namespace C

def lo (t : ℝ) : Mat l := fromBlocks 1 0 (t • 1) 1

theorem lo_mem (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem lo_mul (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by
  rw [lo, lo, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_mul_lo (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp

theorem exists_det_ne (s : Mat l) (h : dd s ≠ 0) : ∃ t : ℝ, (s.toBlocks₁₁ + t • s.toBlocks₁₂).det ≠ 0 := by
  let M : Matrix l l (Polynomial ℝ) := Matrix.of fun a b =>
    Polynomial.C (s (.inl a) (.inl b)) + Polynomial.X * Polynomial.C (s (.inl a) (.inr b))
  have hev : ∀ t : ℝ, Polynomial.eval t M.det = (s.toBlocks₁₁ + t • s.toBlocks₁₂).det := fun t => by
    have e : Polynomial.eval t M.det = ((Polynomial.evalRingHom t).mapMatrix M).det :=
      RingHom.map_det (Polynomial.evalRingHom t) M
    rw [e]
    congr 1
    ext a b
    simp [M, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]
    ring
  have hev' : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = dd s := by
    have e : Polynomial.eval₂ Complex.ofRealHom (-I) M.det =
        ((Polynomial.eval₂RingHom Complex.ofRealHom (-I)).mapMatrix M).det :=
      RingHom.map_det (Polynomial.eval₂RingHom Complex.ofRealHom (-I)) M
    rw [e, dd]
    congr 1
    ext a b
    simp [M, upperParabolic]
    ring
  have hP : M.det ≠ 0 := fun h0 => h (by rw [← hev', h0, Polynomial.eval₂_zero])
  by_contra hall
  push Not at hall
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  convert Set.infinite_univ (α := ℝ)
  ext t
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hev, hall, Set.mem_univ]

end C

theorem surj_of (h1 : DdNe l) (h2 : SecEx l) : Surj l := by
  intro s
  obtain ⟨t, ht⟩ := exists_det_ne s.1 (h1 s)
  let n : Sp l := ⟨lo t, lo_mem t⟩
  let m : Sp l := ⟨lo (-t), lo_mem (-t)⟩
  have e1 : (s * n).1.toBlocks₁₁.det ≠ 0 := by
    show (s.1 * lo t).toBlocks₁₁.det ≠ 0
    rw [toBlocks₁₁_mul_lo]
    exact ht
  have e2 : m.1.toBlocks₁₁.det ≠ 0 := by
    show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0
    simp [lo]
  obtain ⟨g1, -, hg1, -⟩ := h2 (s * n) e1
  obtain ⟨g2, -, hg2, -⟩ := h2 m e2
  refine ⟨g1 * g2, ?_⟩
  have hnm : n * m = 1 := Subtype.ext (lo_mul t)
  rw [map_mul, hg1, hg2, mul_assoc, hnm, mul_one]

end CompanionTheory.ThKR.Mp
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp.MpG

theorem hasFDerivAt_of_curves {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (h : ∀ (c : ℝ → E) (v : E), c 0 = x₀ → HasDerivAt c v 0 → HasDerivAt (fun t => Φ (c t)) (L v) 0) :
    HasFDerivAt Φ L x₀ := by
  classical
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  by_contra hf
  obtain ⟨y0, hy0, hb0⟩ := exists_seq_forall_of_frequently (not_eventually.1 hf)
  have hne0 : ∀ n, y0 n ≠ 0 := fun n e => hb0 n (by simp [e])
  obtain ⟨v, -, φ, hφ, hv⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq (x := fun n => ‖y0 n‖⁻¹ • y0 n)
    (fun n => by simp [norm_smul, hne0 n])
  let y : ℕ → E := fun n => y0 (φ n)
  have hne : ∀ n, ‖y n‖ ≠ 0 := fun n => norm_ne_zero_iff.2 (hne0 _)
  let w : ℝ → E := fun t => if e : ∃ n, ‖y n‖ = t then y e.choose else t • v
  have w0 : w 0 = 0 := by
    have : ¬∃ n, ‖y n‖ = 0 := fun ⟨n, e⟩ => hne n e
    simp only [w, dif_neg this, zero_smul]
  have hw : HasDerivAt w v 0 := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hv δ hδ
    have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range N, t ≠ ‖y m‖ :=
      (Finset.eventually_all _).2 fun m _ => eventually_ne_nhds (hne m).symm
    filter_upwards [this] with t ht
    rw [w0, sub_zero, sub_zero]
    by_cases e : ∃ n, ‖y n‖ = t
    · have e1 := e.choose_spec
      have hm : N ≤ e.choose := not_lt.1 fun hlt => ht _ (Finset.mem_range.2 hlt) e1.symm
      have h1 := (hN _ hm).le
      rw [dist_eq_norm] at h1
      have h2 : w t - t • v = t • (‖y e.choose‖⁻¹ • y e.choose - v) := by
        rw [smul_sub, smul_smul, e1, mul_inv_cancel₀ (e1 ▸ hne _), one_smul]
        simp only [w, dif_pos e]
      rw [h2, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · simp only [w, dif_neg e, sub_self, norm_zero]
      positivity
  have h1 := (h (fun t => x₀ + w t) v (by simp [w0]) (hw.const_add x₀)).fun_sub (L.hasFDerivAt.comp_hasDerivAt 0 hw)
  rw [sub_self, hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h1
  have h2 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using (hy0.comp hφ.tendsto_atTop).norm
  obtain ⟨n, hn⟩ := (h2.eventually (h1 hε)).exists
  have e : ∃ m, ‖y m‖ = ‖y n‖ := ⟨n, rfl⟩
  have e2 : w ‖y n‖ = y e.choose := by simp only [w, dif_pos e]
  refine hb0 (φ e.choose) ?_
  simp only [Function.comp, w0, e2, add_zero, map_zero, sub_zero, smul_zero, norm_norm] at hn
  rw [sub_right_comm]
  exact hn.trans_eq (congrArg (ε * ·) e.choose_spec.symm)

variable {l : Type} [Fintype l] [DecidableEq l]

theorem hasDerivAt_det_one {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by
  have hd : DifferentiableAt ℝ (fun N : l → l → ℝ => (Matrix.of N).det) (M 0) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun σ _ => (((contDiff_prod (n := 1) (f := fun i (N : l → l → ℝ) => N (σ i) i)
      fun i _ => contDiff_apply_apply ℝ ℝ (σ i) i).differentiable one_ne_zero) _).const_mul _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt 0 h
  have h2 : HasDerivAt (fun t : ℝ => M 0 + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (M 0)
  have h3 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)
  let p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (Matrix.of X).map Polynomial.C)).divX.divX
  have h4 : HasDerivAt (fun t : ℝ => 1 + (Matrix.of X).trace * t + p.eval t * t ^ 2) (Matrix.of X).trace 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul _).const_add 1).fun_add
      ((p.hasDerivAt 0).fun_mul (hasDerivAt_pow 2 0))).congr_deriv (by simp)
  have h5 := h3.unique (h4.congr_of_eventuallyEq (.of_forall fun t => by
    refine Eq.trans ?_ (Matrix.det_one_add_smul t (Matrix.of X))
    rw [← h0]
    rfl))
  exact h5 ▸ h1

theorem curve {g : ℝ → (l ⊕ l) → (l ⊕ l) → ℝ} {X : (l ⊕ l) → (l ⊕ l) → ℝ} (g0 : Matrix.of (g 0) = 1)
    (hg : HasDerivAt g X 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (sec (Matrix.of (g t)) f)) (schwartzToL2 l (Qd (Matrix.of X) f)) 0 := by
  have hd : ∀ i j : l → l ⊕ l, HasDerivAt (fun t => bl i j (Matrix.of (g t))) (bl i j (Matrix.of X)) 0 := fun i j =>
    (LinearMap.toContinuousLinearMap
      ((bl i j).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)).hasFDerivAt.comp_hasDerivAt 0 hg
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (Matrix.of (g t))
  let c : ℝ → ℝ := fun t => (√|(Matrix.of (g t)).toBlocks₁₁.det|)⁻¹
  have eA : ∀ t, (A t).det = (Matrix.of (g t)).toBlocks₁₁.det := fun t => det_bl _ _ _
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  have hopen : ∀ᶠ u in 𝓝 0, IsUnit (A u) := (hd _ _).continuousAt.eventually (Units.isOpen.mem_nhds h0)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _), eA]
  have d0 : (Matrix.of (g 0)).toBlocks₁₁.det = 1 := by
    rw [← eA, A0]
    simp [ContinuousLinearMap.det]
  have c0 : c 0 = 1 := by simp only [c, d0]; simp
  have hD : HasDerivAt (fun t => (Matrix.of (g t)).toBlocks₁₁.det) (Matrix.of X).toBlocks₁₁.trace 0 :=
    hasDerivAt_det_one (M := fun t a b => g t (.inl a) (.inl b)) (X := fun a b => X (.inl a) (.inl b))
      (hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hasDerivAt_pi.1 (hasDerivAt_pi.1 hg _) _)
      (by
        ext a b
        have := congrFun (congrFun g0 (.inl a)) (.inl b)
        simpa [Matrix.one_apply] using this)
  have hcd : HasDerivAt c (-((Matrix.of X).toBlocks₁₁.trace / 2)) 0 := by
    have hp : 0 < (Matrix.of (g 0)).toBlocks₁₁.det := by rw [d0]; exact one_pos
    have h1 := (hD.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv (by simp only [d0]; simp)
    filter_upwards [hD.continuousAt.eventually (lt_mem_nhds hp)] with t ht
    simp only [c, abs_of_pos ht]
    rfl
  have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl (Matrix.of X)) 0 := by
    have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
      (hd Sum.inl Sum.inl) A0.symm
    exact h2.congr_deriv (by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
        one_mul, mul_one])
  obtain ⟨Q, hQ, hQ'⟩ := ld_big h1 (hd Sum.inl Sum.inr) (hd Sum.inr Sum.inl) hcd
    (hopen.mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [g0, block_inl_inr_one]) (by rw [g0, block_inr_inl_one]) c0 f
  refine (hQ f).congr_deriv (congrArg _ ?_)
  rw [h3, Qd, ofReal_neg, neg_smul, sub_eq_add_neg]

end CompanionTheory.ThKR.Mp.MpG

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

theorem secDer : SecDer l := by
  intro E _ _ m m' x₀ h0 hm f
  let L : ((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] L2 l := LinearMap.toContinuousLinearMap
    ((((schwartzToL2 l).restrictScalars ℝ).toLinearMap.comp (qdLin f)).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)
  have hL : ∀ X, L X = schwartzToL2 l (Qd (Matrix.of X) f) := fun X => rfl
  have h1 : HasFDerivAt (fun g : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of g) f)) L (fun a b => m x₀ a b) :=
    MpG.hasFDerivAt_of_curves fun c v c0 hc => MpG.curve (by rw [c0, h0]; rfl) hc f
  have h2 : HasFDerivAt (fun x => fun a b => m x a b)
      (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => m' a b) x₀ :=
    hasFDerivAt_pi.2 fun a => hasFDerivAt_pi.2 fun b => hm a b
  refine (h1.comp x₀ h2).congr_fderiv ?_
  ext1 v
  rw [ContinuousLinearMap.comp_apply, hL, ← qd_sum]
  simp only [map_sum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact ((schwartzToL2 l).restrictScalars ℝ).map_smul _ _

end CompanionTheory.ThKR.Mp

end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpE

omit [Fintype l] in
theorem toBlocks₁₁_one' : (1 : Mat l).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem sec_one : sec (1 : Mat l) = 1 := by
  rw [sec, block_inl_inl_one, block_inl_inr_one, block_inr_inl_one, toBlocks₁₁_one', Matrix.det_one, abs_one, Real.sqrt_one, inv_one,
    Ring.inverse_one, big_one]

theorem eventually_det_pos : ∀ᶠ s in 𝓝 (1 : Sp l), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Sp l => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Sp l).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Sp l).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Sp l).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2

theorem eventually_det_pos_G : ∀ᶠ g in 𝓝 (1 : G l), 0 < (pr g).1.toBlocks₁₁.det := by
  have h := continuous_pr.tendsto (1 : G l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos

theorem tendsto_sec (hD : SecDer l) (f : Sch l) :
    Tendsto (fun s : Sp l => schwartzToL2 l (sec s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by
  let m' : (l ⊕ l) → (l ⊕ l) → (((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] ℝ) := fun a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => (l ⊕ l) → ℝ) a)
  have h := hD ((l ⊕ l) → (l ⊕ l) → ℝ) (fun x => Matrix.of x) m' (fun a b => (1 : Mat l) a b) rfl
    (fun a b => (m' a b).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)) f
  have h2 : schwartzToL2 l (sec (Matrix.of fun a b => (1 : Mat l) a b) f) = schwartzToL2 l f := by
    rw [show (Matrix.of fun a b => (1 : Mat l) a b) = 1 from rfl, sec_one, ContinuousLinearMap.one_apply]
  have h3 : Tendsto (fun x : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of x) f))
      (𝓝 (fun a b => (1 : Mat l) a b)) (𝓝 (schwartzToL2 l f)) := by
    convert h.continuousAt.tendsto using 2
    exact h2.symm
  have hc : Continuous fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ) :=
    continuous_pi fun a => continuous_pi fun b => continuous_subtype_val.matrix_elem a b
  have h4 : Tendsto (fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ)) (𝓝 1)
      (𝓝 (fun a b => (1 : Mat l) a b)) := hc.tendsto 1
  exact h3.comp h4

theorem exists_sch_ne : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : Sch l).toLp 2 volume by
      rw [← schwartzToL2_apply, ← schwartzToL2_apply, h, map_zero])
  simp [this]

end MpE

open MpE

theorem nearOne_of (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by
  obtain ⟨ε, -, hker, hεom⟩ := hK
  obtain ⟨f, hf⟩ := exists_sch_ne (l := l)
  have hv : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hf
  have hom : ∀ᶠ g in 𝓝 (1 : G l), ‖om g (schwartzToL2 l f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := (continuous_om (schwartzToL2 l f)).tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hv)
  have hsec : ∀ᶠ g in 𝓝 (1 : G l), ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := continuous_pr.tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_sec hD f).comp h)).eventually (gt_mem_nhds hv)
  filter_upwards [eventually_det_pos_G, hom, hsec] with g h1 h2 h3
  obtain ⟨g', c, hg', hU, hc⟩ := hS (pr g) h1.ne'
  rw [hc h1, one_smul] at hU
  have hk : pr (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, hg', mul_inv_cancel]
  rcases (hker _).1 hk with h | h
  · rw [mul_inv_eq_one.1 h, hU, hg']
  · exfalso
    have hg : g = ε * g' := mul_inv_eq_iff_eq_mul.1 h
    have e1 : om g = om ε * om g' := by rw [hg, map_mul]
    have e : om g (schwartzToL2 l f) = -schwartzToL2 l (sec (pr g).1 f) := by
      rw [e1]
      show om ε (om g' (schwartzToL2 l f)) = _
      rw [hεom, om_sch, hU]
    rw [e] at h2
    have h4 : ‖schwartzToL2 l f + schwartzToL2 l f‖ ≤
        ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ + ‖-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ := by
      have := norm_add_le (schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f)
      have e2 : schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f + (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) =
          -(schwartzToL2 l f + schwartzToL2 l f) := by abel
      rwa [e2, norm_neg] at this
    have h5 : ‖schwartzToL2 l f + schwartzToL2 l f‖ = 2 * ‖schwartzToL2 l f‖ := by
      rw [← two_smul ℂ (schwartzToL2 l f), norm_smul]
      norm_num
    linarith

namespace MpE

theorem isInducing_F :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := ⟨rfl⟩

theorem metaplectic_group_t2Space : T2Space (G l) := by
  refine T2Space.of_injective_continuous (f := fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)))
    ?_ isInducing_F.continuous
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have hu : om g = om h := LinearIsometryEquiv.ext fun f => congrFun h2 f
  have hU : omS g = omS h := ContinuousLinearMap.ext fun f => by
    apply injective_toLp 2 volume
    show schwartzToL2 l (omS g f) = schwartzToL2 l (omS h f)
    rw [← om_sch, ← om_sch, hu]
  exact Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext hu (Units.ext hU)))

end MpE

theorem cover_of (hT : TopG l) (hO : Surj l) (hK : Ker l) (hS : SecEx l) (hD : SecDer l) : Cover l := by
  have : IsTopologicalGroup (G l) := hT
  have : T2Space (G l) := metaplectic_group_t2Space
  obtain ⟨ε, -, hker, -⟩ := hK
  have hσ : ∀ s : Sp l, ∃ g : G l, 0 < s.1.toBlocks₁₁.det → pr g = s ∧ omS g = sec s.1 := fun s => by
    by_cases h : 0 < s.1.toBlocks₁₁.det
    · obtain ⟨g, c, h1, h2, h3⟩ := hS s h.ne'
      exact ⟨g, fun _ => ⟨h1, by rw [h2, h3 h, one_smul]⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  have hd : DenseRange (schwartzToL2 l) := by
    have h := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ l) (F := ℂ)
      (μ := (volume : Measure (EuclideanSpace ℝ l))) (p := 2) ENNReal.ofNat_ne_top
    convert h using 1
    funext g
    rfl
  have hv : ∀ v : L2 l, Tendsto (fun s => om (σ s) v) (𝓝 1) (𝓝 v) := fun v => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨φ, hφ⟩ := hd.exists_dist_lt v (show 0 < δ / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.1 (tendsto_sec hD φ)) (δ / 3) (by positivity)
    filter_upwards [h1, eventually_det_pos] with s hs1 hs2
    have e : om (σ s) (schwartzToL2 l φ) = schwartzToL2 l (sec s.1 φ) := by rw [om_sch, (hσ s hs2).2]
    calc dist (om (σ s) v) v ≤ dist (om (σ s) v) (om (σ s) (schwartzToL2 l φ)) +
          dist (om (σ s) (schwartzToL2 l φ)) (schwartzToL2 l φ) + dist (schwartzToL2 l φ) v := dist_triangle4 _ _ _ _
      _ < δ := by
        rw [(om (σ s)).isometry.dist_eq, e, dist_comm (schwartzToL2 l φ) v]
        linarith
  have key : Tendsto σ (𝓝 1) (𝓝 1) := by
    have hpr : Tendsto (fun s => pr (σ s)) (𝓝 (1 : Sp l)) (𝓝 1) :=
      tendsto_id.congr' (eventually_det_pos.mono fun s hs => (hσ s hs).1.symm)
    have h2 : Tendsto (fun s => ((pr (σ s), fun f => om (σ s) f) : Sp l × (L2 l → L2 l))) (𝓝 1)
        (𝓝 ((pr (1 : G l), fun f => om (1 : G l) f))) := by
      rw [map_one, map_one]
      refine hpr.prodMk_nhds (tendsto_pi_nhds.2 fun v => ?_)
      simpa using hv v
    exact isInducing_F.tendsto_nhds_iff.2 h2
  have hopen : IsOpenMap (pr : G l → Sp l) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨g, hg, rfl⟩
    have hc : Tendsto (fun t : Sp l => (pr g)⁻¹ * t) (𝓝 (pr g)) (𝓝 1) := by
      have : Continuous fun t : Sp l => (pr g)⁻¹ * t :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) fun t => ((pr g)⁻¹ * t).2
      simpa using this.tendsto (pr g)
    have h1 : Tendsto (fun t => g * σ ((pr g)⁻¹ * t)) (𝓝 (pr g)) (𝓝 g) := by
      have := ((continuous_const_mul g).tendsto 1).comp (key.comp hc)
      rwa [mul_one] at this
    filter_upwards [h1 (hU.mem_nhds hg), hc.eventually eventually_det_pos] with t ht ht'
    exact ⟨_, ht, by rw [map_mul, (hσ _ ht').1, mul_inv_cancel_left]⟩
  have hker' : ((pr : G l →* Sp l).ker : Set (G l)) = {1, ε} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker g
  have hdisc : IsDiscrete ((pr : G l →* Sp l).ker : Set (G l)) := by
    rw [hker']
    exact ((Set.finite_singleton ε).insert 1).isDiscrete
  have hq : IsQuotientMap (pr : G l → Sp l) := hopen.isQuotientMap continuous_pr hO
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hdisc).isCoveringMap

end CompanionTheory.ThKR.Mp
end
end

section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

def orb {k : ℕ} (γ : (Fin k → ℝ) → G l) (f : Sch l) (t : Fin k → ℝ) : L2 l := om (γ t) (schwartzToL2 l f)

def dm {k : ℕ} (γ : (Fin k → ℝ) → G l) (t : Fin k → ℝ) (a b : l ⊕ l) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ c, ((pr (γ t))⁻¹ : Sp l).1 a c • fderiv ℝ (fun t => (pr (γ t) : Mat l) c b) t

theorem hasFDerivAt_orb (hT : TopG l) (hN : NearOne l) (hD : SecDer l) {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hγ : Continuous γ) (hs : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b) (f : Sch l)
    (t₀ : Fin k → ℝ) :
    HasFDerivAt (orb γ f)
      (∑ a, ∑ b, (dm γ t₀ a b).smulRight (orb γ (Qd (Matrix.single a b 1) f) t₀)) t₀ := by
  have : IsTopologicalGroup (G l) := hT
  have hh : Continuous fun t => (γ t₀)⁻¹ * γ t := continuous_const.mul hγ
  have hev : ∀ᶠ t in 𝓝 t₀, omS ((γ t₀)⁻¹ * γ t) = sec (pr ((γ t₀)⁻¹ * γ t)).1 := by
    have h1 : Tendsto (fun t => (γ t₀)⁻¹ * γ t) (𝓝 t₀) (𝓝 1) := by
      have := hh.tendsto t₀
      rwa [inv_mul_cancel] at this
    exact h1.eventually hN
  let m : (Fin k → ℝ) → Mat l := fun t => (pr ((γ t₀)⁻¹ * γ t)).1
  have hm : ∀ t, m t = ((pr (γ t₀))⁻¹ : Sp l).1 * (pr (γ t)).1 := fun t => by
    show (pr ((γ t₀)⁻¹ * γ t)).1 = _
    rw [map_mul, map_inv]
    rfl
  have hm1 : m t₀ = 1 := by
    show (pr ((γ t₀)⁻¹ * γ t₀)).1 = 1
    rw [inv_mul_cancel, map_one]
    rfl
  have hmd : ∀ a b, HasFDerivAt (fun t => m t a b) (dm γ t₀ a b) t₀ := by
    intro a b
    have e : (fun t => m t a b) = fun t => ∑ c, ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b := by
      funext t
      rw [hm t, Matrix.mul_apply]
    rw [e]
    have := HasFDerivAt.sum (u := Finset.univ) (x := t₀) fun c _ =>
      ((hs c b t₀).hasFDerivAt).const_mul (((pr (γ t₀))⁻¹ : Sp l).1 a c)
    have e2 : (fun t => ∑ c, ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b) =
        ∑ c, fun t => ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b := by
      funext t
      simp [Finset.sum_apply]
    rw [e2]
    exact this
  have hsec := hD (Fin k → ℝ) m (dm γ t₀) t₀ hm1 hmd f
  let L : L2 l →L[ℝ] L2 l :=
    ((om (γ t₀)).toContinuousLinearEquiv.toContinuousLinearMap : L2 l →L[ℂ] L2 l).restrictScalars ℝ
  have hL : ∀ v, L v = om (γ t₀) v := fun v => rfl
  have h2 := L.hasFDerivAt.comp t₀ hsec
  have heq : orb γ f =ᶠ[𝓝 t₀] (⇑L ∘ fun x => schwartzToL2 l (sec (m x) f)) := by
    filter_upwards [hev] with t ht
    calc orb γ f t = om (γ t₀ * ((γ t₀)⁻¹ * γ t)) (schwartzToL2 l f) := by
          rw [mul_inv_cancel_left]; rfl
      _ = om (γ t₀) (om ((γ t₀)⁻¹ * γ t) (schwartzToL2 l f)) := by rw [map_mul]; rfl
      _ = om (γ t₀) (schwartzToL2 l (omS ((γ t₀)⁻¹ * γ t) f)) := by rw [om_sch]
      _ = _ := by rw [ht]; rfl
  have h3 := h2.congr_of_eventuallyEq heq
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  simp only [hL, orb]

theorem contDiff_dm {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by
  have hinv : ∀ a c, ContDiff ℝ ∞ fun t => ((pr (γ t))⁻¹ : Sp l).1 a c := by
    intro a c
    have e : (fun t => ((pr (γ t))⁻¹ : Sp l).1 a c) =
        fun t => ∑ e, (∑ d, (-J l ℝ) a d * (pr (γ t) : Mat l) e d) * J l ℝ e c := by
      funext t
      show ((-J l ℝ) * (pr (γ t) : Mat l)ᵀ * J l ℝ) a c = _
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [e]
    exact ContDiff.sum fun e _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs e d)).mul contDiff_const
  have hn : ((n : WithTop ℕ∞)) ≤ ∞ := by exact_mod_cast le_top
  have hn1 : ((n : WithTop ℕ∞)) + 1 ≤ ∞ := by exact_mod_cast le_top
  unfold dm
  exact ContDiff.sum fun c _ => ((hinv a c).of_le hn).smul ((hs c b).fderiv_right hn1)

theorem smooth_of (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l := by
  intro k γ hγ hs f
  have hd : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b := fun a b =>
    (hs a b).differentiable (by simp)
  suffices H : ∀ n : ℕ, ∀ g : Sch l, ContDiff ℝ n (orb γ g) from contDiff_infty.2 fun n => H n f
  intro n
  induction n with
  | zero =>
    intro g
    have := (contDiff_zero (𝕜 := ℝ) (f := orb γ g)).2 ((continuous_om (schwartzToL2 l g)).comp hγ)
    exact_mod_cast this
  | succ n ih =>
    intro g
    have key := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := orb γ g) (n := n)).2
      ⟨fun t => ∑ a, ∑ b, (dm γ t a b).smulRight (orb γ (Qd (Matrix.single a b 1) g) t),
        ContDiff.sum fun a _ => ContDiff.sum fun b _ => (contDiff_dm γ hs a b n).smulRight (ih _),
        fun t => hasFDerivAt_orb hT hN hD γ hγ hd g t⟩
    exact_mod_cast key

end CompanionTheory.ThKR.Mp
end
end

section
open CompanionTheory.ThKR.Mp in
theorem CompanionTheory.ThKR.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
end
