import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryInjAtPlace

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (x : AE F E) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem compFin_inclR (v : Pl F) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

theorem eq_tensAt_of_at (v : Pl F) (x : AE F E) (hx : At (evFin F v) x) :
    x = tensAt E v (compFin F E v x) := by
  have h0 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h1 := hx _ h0
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  have h2 : tensAt E v 1 = algebraMap (AF F) (AE F E) (atPlace v 1) := by
    rw [Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]
  exact h1

theorem mat_eq_zero_of_at {n : ℕ} (v : Pl F) (z : Matrix (Fin n) (Fin n) (AE F E)) (hz : At (evFin F v) z)
    (h0 : z.map (compFin F E v) = 0) : z = 0 := by
  ext i j
  have hij : At (evFin F v) (z i j) := fun u hu => by
    have := congrFun (congrFun (hz u hu) i) j
    simpa using this
  rw [eq_tensAt_of_at v _ hij]
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, map_zero, Matrix.zero_apply]

theorem unitary_at_components {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F)
    (t : E →ₐ[F] Fv F v) (h : UA σ J) :
    ((mat h).map (piW t))ᵀ * J.map t * (mat h).map (piW (t.comp σ)) = J.map t := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h1 := congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t := by
    ext i j
    simp only [incM, Matrix.map_apply]
    rw [compFin_inclR, splitProj_inclR]
  have e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [compFin_cA, ← splitProj_comp]
    rfl
  have e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ := by
    ext i j
    rfl
  rw [e1, e2] at h1
  rw [← e3]
  exact h1

theorem eq_of_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end GlobalTheory.UnitaryInjAtPlace
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_determined_by_split_image : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  first | exact @GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | exact GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq | (intros; apply GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem mul_mem_UAt {n : ℕ} {Y : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ Y.J}
    (hg : g ∈ UAt σ Y ev) (hh : h ∈ UAt σ Y ev) : g * h ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_mul {n : ℕ} {Y : Spc F E n} (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {Y : Spc F E n} : mat (1 : UA σ Y.J) = 1 := rfl

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem pres (hT : IsTriple B G X om om') (p : UA σ G.V.J × UA σ G.W.J) {Φ : (Fin a × Fin (a + a') → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin a × Fin (a + a'))) : om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
  (IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ

theorem acts_comp (hT : IsTriple B G X om om') {v : Pl F} {h₁ h₂ : UA σ G.W.J}
    {φ φ₂ φ₃ : (Fin a × Fin (a + a') → Fv F v) → ℂ}
    (h2 : Acts (evFin F v) (om (1, h₂)) φ φ₂) (h1 : Acts (evFin F v) (om (1, h₁)) φ₂ φ₃) :
    Acts (evFin F v) (om (1, h₁ * h₂)) φ φ₃ := by
  intro r hr
  have hr2 : Rest (evFin F v) φ₂ r := ⟨hr.1, by rw [← h2 r hr]; exact pres hT _ hr.2⟩
  have e : om (1, h₁ * h₂) = om (1, h₁) * om (1, h₂) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr2]

theorem acts_one {v : Pl F} (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) :
    Acts (evFin F v) (om (1, 1)) φ φ := by
  intro r _
  rw [show ((1, 1) : UA σ G.V.J × UA σ G.W.J) = 1 from rfl, map_one, Module.End.one_apply]

noncomputable section

def cmpGL {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) : GL (Fin n) (Fv F v) :=
  Units.map (piW t).mapMatrix.toMonoidHom h.1

theorem cmpGL_val {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    (cmpGL t h).1 = (mat h).map (piW t) := rfl

def apowHom {v : Pl F} (z : ℂ) : (Fv F v)ˣ →* ℂˣ where
  toFun x := Units.mk0 (GlobalTheory.SplitFlip.apow x z) (GlobalTheory.SplitFlip.apow_ne_zero x z)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [GlobalTheory.SplitFlip.apow_mul])

end

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isUnit_det_cmp {n : ℕ} {Y : Spc F E n} {v : Pl F} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    IsUnit ((mat h).map (piW t)).det := by
  rw [← cmpGL_val]; exact (Matrix.isUnit_iff_isUnit_det _).1 (cmpGL t h).isUnit

theorem two_ne_zero_Fv (v : Pl F) : (2 : Fv F v) ≠ 0 := by
  have := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at this

theorem core (hT : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (hEx : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, h)) φ φ₁)
    (hsurj : ∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1)
    (hinj : ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂)
    (hS : ∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) :
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  classical
  by_cases h0 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ = 0
  · refine ⟨1, fun h _ => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ _ => ?_⟩⟩
    rw [h0 φ₁ hφ₁, h0 φ hφ]
    funext Y
    simp [GlobalTheory.SplitFlip.omA]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 hne
  set P : UA σ G.W.J → ℂ → Prop := fun h c => ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ) with hP
  have uniq : ∀ h ∈ UAt σ G.W (evFin F v), ∀ c c', P h c → P h c' → c = c' := by
    intro h hh c c' hc hc'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hEx h hh φ₀ hφ₀
    set M := (mat h).map (piW t)
    have key : Y₀ * Mᵀ * M⁻¹ᵀ = Y₀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_det_cmp t h),
        Matrix.transpose_one, Matrix.mul_one]
    have e1 := hc φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    have e2 := hc' φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    rw [key] at e1 e2
    exact mul_right_cancel₀ hY₀ (e1.symm.trans e2)
  let c : UA σ G.W.J → ℂ := fun h => if hh : h ∈ UAt σ G.W (evFin F v) then (hS h hh).choose else 0
  have hc : ∀ h (hh : h ∈ UAt σ G.W (evFin F v)), P h (c h) := by
    intro h hh
    simp only [c, dif_pos hh]
    exact (hS h hh).choose_spec
  have P1 : P 1 1 := by
    intro φ hφ φ₁ hφ₁ hA Y
    have : φ₁ = φ := (hEx 1 (one_mem_UAt _ _) φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ, acts_one φ⟩
    subst this
    rw [mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), inv_one, Matrix.transpose_one, Matrix.mul_one,
      one_mul]
  have c1 : c 1 = 1 := uniq 1 (one_mem_UAt _ _) _ _ (hc 1 (one_mem_UAt _ _)) P1
  have Pmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      P (h₁ * h₂) (c h₁ * c h₂) := by
    intro h₁ hh₁ h₂ hh₂ φ hφ φ₁₂ hφ₁₂ hA Y
    obtain ⟨φ₂, ⟨hφ₂, hA2⟩, -⟩ := hEx h₂ hh₂ φ hφ
    obtain ⟨φ₃, ⟨hφ₃, hA3⟩, -⟩ := hEx h₁ hh₁ φ₂ hφ₂
    have : φ₁₂ = φ₃ := (hEx (h₁ * h₂) (mul_mem_UAt hh₁ hh₂) φ hφ).unique ⟨hφ₁₂, hA⟩ ⟨hφ₃, acts_comp hT hA2 hA3⟩
    subst this
    rw [hc h₁ hh₁ φ₂ hφ₂ φ₁₂ hφ₁₂ hA3, hc h₂ hh₂ φ hφ φ₂ hφ₂ hA2, mat_mul, Matrix.map_mul, Matrix.mul_inv_rev,
      Matrix.transpose_mul, Matrix.mul_assoc, mul_assoc]
  have cmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      c (h₁ * h₂) = c h₁ * c h₂ := fun h₁ hh₁ h₂ hh₂ =>
    uniq _ (mul_mem_UAt hh₁ hh₂) _ _ (hc _ (mul_mem_UAt hh₁ hh₂)) (Pmul h₁ hh₁ h₂ hh₂)
  choose sec hsec hsecv using hsurj
  have secmul : ∀ g₁ g₂, sec (g₁ * g₂) = sec g₁ * sec g₂ := fun g₁ g₂ =>
    hinj _ (hsec _) _ (mul_mem_UAt (hsec g₁) (hsec g₂)) (by
      rw [hsecv, mat_mul, Matrix.map_mul, hsecv, hsecv, Units.val_mul])
  have sec1 : sec 1 = 1 := hinj _ (hsec _) _ (one_mem_UAt _ _) (by
      rw [hsecv, mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), Units.val_one])
  let κ : GL (Fin (a + a')) (Fv F v) →* ℂ :=
    { toFun := fun g => c (sec g)
      map_one' := by simp only [sec1, c1]
      map_mul' := fun g₁ g₂ => by simp only [secmul, cmul _ (hsec g₁) _ (hsec g₂)] }
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) κ.toHomUnits
  refine ⟨χ * apowHom ((a : ℂ) / 2), fun h hh => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ hA => ?_⟩⟩
  have hsh : sec (cmpGL t h) = h := hinj _ (hsec _) _ hh (by rw [hsecv, cmpGL_val])
  have hch : c h = (χ (Matrix.GeneralLinearGroup.det (cmpGL t h)) : ℂ) := by
    have := congrArg Units.val (hχ (cmpGL t h))
    rw [MonoidHom.coe_toHomUnits] at this
    rw [← this]
    show c h = c (sec (cmpGL t h))
    rw [hsh]
  funext Y
  rw [hc h hh φ hφ φ₁ hφ₁ hA Y, hch]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.invT_val, map_one, inv_one, Units.val_one, MonoidHom.mul_apply,
    Units.val_mul, Fintype.card_fin, GlobalTheory.SplitFlip.apow_one, one_mul, Matrix.one_mul, Matrix.coe_units_inv, cmpGL_val]
  have hv : ((apowHom (v := v) ((a : ℂ) / 2) (GlobalTheory.SplitFlip.gdet (cmpGL t h)) : ℂˣ) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (cmpGL t h)) (-(a : ℂ) / 2) = 1 := by
    show GlobalTheory.SplitFlip.apow _ _ * GlobalTheory.SplitFlip.apow _ _ = 1
    rw [← GlobalTheory.SplitFlip.apow_add, show (a : ℂ) / 2 + -(a : ℂ) / 2 = 0 by ring, GlobalTheory.SplitFlip.apow_zero]
  rw [mul_one, mul_assoc (χ _ : ℂ), hv, mul_one]

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

theorem linear_weil_functional_character_weight_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) →
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι _ hS
  have hEx := (GlobalTheory.T.theta_action_exists hPr F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 1 (one_mem_UAt _ _)
  exact core hT v t ι hEx (GlobalTheory.T.local_unitary_group_surjects_general_linear_right hPr F E σ B a a' G X om om' hT v hv t)
    (GlobalTheory.T.local_unitary_determined_by_split_image F E σ B a a' G X om om' hT v hv t) hS

end GlobalTheory.LocalUnitSubgroupClosure
end
