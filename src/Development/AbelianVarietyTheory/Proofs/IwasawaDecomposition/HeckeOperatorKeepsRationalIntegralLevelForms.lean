import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Formalism.LocalToGlobal.Columns.CoefModAt

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section LvlCoord

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} {P : Subgroup G₀} {ψ : P →* Kˣ}

theorem lvlForm_eig (x : Fin (S.lvlDim act P ψ) → K) (p : P) :
    act (p : G₀) (lvlForm S act P ψ x) = ((ψ p : Kˣ) : K) • lvlForm S act P ψ x := by
  have h1 : (S.lvlE act P ψ).mulVec x ∈ LinearMap.range (imE (S.gaMat act (lvlIdem P ψ))).mulVecLin := ⟨x, rfl⟩
  rw [(image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).2, level_part_spec K S G₀ act P ψ] at h1
  have hz : (S.actMat act (p : G₀)).mulVec ((S.lvlE act P ψ).mulVec x) =
      ((ψ p : Kˣ) : K) • (S.lvlE act P ψ).mulVec x := h1 p
  have h4 := S.I_actMat act (p : G₀) ((S.lvlE act P ψ).mulVec x)
  rw [hz, map_smul, CSD.I_apply] at h4
  apply Subtype.ext
  show ((act (p : G₀) (S.basis.equivFun.symm ((S.lvlE act P ψ).mulVec x)) : S.Forms) : S.Cl → S.V) = _
  rw [← h4]
  rfl

theorem exists_lvlForm (f : S.Forms) (hf : ∀ p : P, act (p : G₀) f = ((ψ p : Kˣ) : K) • f) :
    ∃ x, lvlForm S act P ψ x = f := by
  have hI : Function.Injective S.I := by
    intro a b h
    rw [CSD.I_apply, CSD.I_apply] at h
    exact S.basis.equivFun.symm.injective (Subtype.ext h)
  have hzf : S.basis.equivFun.symm (S.basis.equivFun f) = f := S.basis.equivFun.symm_apply_apply f
  have hz : ∀ p : P, (S.actMat act (p : G₀)).mulVec (S.basis.equivFun f) =
      ((ψ p : Kˣ) : K) • S.basis.equivFun f := by
    intro p
    apply hI
    rw [S.I_actMat act (p : G₀) _, map_smul, CSD.I_apply, hzf, hf p]
    rfl
  have h1 : S.basis.equivFun f ∈ LinearMap.range (imE (S.gaMat act (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).2, level_part_spec K S G₀ act P ψ]
    exact hz
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, ?_⟩
  have hx' : (S.lvlE act P ψ).mulVec x = S.basis.equivFun f := hx
  show S.basis.equivFun.symm ((S.lvlE act P ψ).mulVec x) = f
  rw [hx', hzf]

def lvlFormL (S : CSD K) (act : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) :
    (Fin (S.lvlDim act P ψ) → K) →ₗ[K] S.Forms :=
  S.basis.equivFun.symm.toLinearMap ∘ₗ (S.lvlE act P ψ).mulVecLin

theorem lvlFormL_apply (x : Fin (S.lvlDim act P ψ) → K) : lvlFormL S act P ψ x = lvlForm S act P ψ x := rfl

theorem lvlForm_eq_sum (x : Fin (S.lvlDim act P ψ) → K) :
    lvlForm S act P ψ x = ∑ i, ((S.lvlE act P ψ).mulVec x) i • S.basis i := by
  simp only [lvlForm, Module.Basis.equivFun_symm_apply]

open Classical in

def lvlAvgF (act : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (f : S.Forms) : S.Forms :=
  ∑ p : P, ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) • act (p : G₀) f

theorem lvlAvgF_eig (f : S.Forms) (q : P) :
    act (q : G₀) (lvlAvgF act P ψ f) = ((ψ q : Kˣ) : K) • lvlAvgF act P ψ f := by
  classical
  unfold lvlAvgF
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, Equiv.coe_mulLeft, smul_smul, Subgroup.coe_mul]
  congr 1
  have hq : ((ψ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  simp only [mul_inv_rev, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem exists_lvlForm_avg (f : S.Forms) : ∃ x, lvlForm S act P ψ x = lvlAvgF act P ψ f :=
  exists_lvlForm _ (lvlAvgF_eig f)

end LvlCoord

section Avg

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]
  {K : Type} [Field K] {G₀ : Type} [Group G₀] [Fintype G₀]

open Classical in

def cutAvgL {Q : Subgroup G} (ch : Q →* ℂˣ) (red : Q →* G₀) (hred : Function.Surjective red) (σ : K →+* ℂ)
    (P : Subgroup G₀) (ψ : P →* Kˣ) (W : Type) [AddCommGroup W] [Module ℂ W] : (G → W) →ₗ[ℂ] (G → W) :=
  ∑ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) * (((ch (hred (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) •
    LinearMap.funLeft ℂ W (fun h : G => h * ((hred (p : G₀)).choose : G))

open Classical in
theorem cutAvgL_apply {Q : Subgroup G} (ch : Q →* ℂˣ) (red : Q →* G₀) (hred : Function.Surjective red)
    (σ : K →+* ℂ) (P : Subgroup G₀) (ψ : P →* Kˣ) (F : G → W) (h : G) :
    cutAvgL ch red hred σ P ψ W F h = ∑ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) *
      (((ch (hred (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) • F (h * ((hred (p : G₀)).choose : G)) := by
  simp only [cutAvgL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    LinearMap.funLeft_apply]

end Avg

end GlobalTheory.MtIn

namespace GlobalTheory.MtIn

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
  [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (pres : Bridge.ClassPres ι S σ ρ J χ) {Q : Subgroup G} {ch : Q →* ℂˣ} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ)

theorem cutAvgL_ext (f : S.Forms) :
    cutAvgL ch tie.red tie.red_surj σ P ψ W (pres.ext f.1) = pres.ext (lvlAvgF act P ψ f).1 := by
  classical
  funext h
  rw [cutAvgL_apply, ← Bridge.ClassPres.extL_apply pres (lvlAvgF act P ψ f)]
  unfold lvlAvgF
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smulₛₗ, Bridge.ClassPres.extL_apply,
    tie.act_eq (p : G₀) _ (tie.red_surj (p : G₀)).choose_spec f, Pi.smul_apply, Bridge.g0Act, mul_smul]

theorem cutAvgL_of_mem {F : G → W}
    (hF : F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ)) :
    cutAvgL ch tie.red tie.red_surj σ P ψ W F = F := by
  classical
  have hF2 := (Submodule.mem_inf.1 hF).2
  have hF2' : ∀ (κ : Q) (hκ : tie.red κ ∈ P) (h : G),
      F (h * κ) = ((ch κ * ((Units.map σ.toMonoidHom).comp ψ) ⟨tie.red κ, hκ⟩ : ℂˣ) : ℂ) • F h := hF2
  funext h
  rw [cutAvgL_apply]
  have key : ∀ p : P, (σ ((Nat.card P : K)⁻¹ * ((ψ p⁻¹ : Kˣ) : K)) *
      (((ch (tie.red_surj (p : G₀)).choose)⁻¹ : ℂˣ) : ℂ)) • F (h * ((tie.red_surj (p : G₀)).choose : G)) =
      ((Nat.card P : ℂ))⁻¹ • F h := by
    intro p
    have hs := (tie.red_surj (p : G₀)).choose_spec
    have hm : tie.red (tie.red_surj (p : G₀)).choose ∈ P := by rw [hs]; exact p.2
    have hp : (⟨tie.red (tie.red_surj (p : G₀)).choose, hm⟩ : P) = p := Subtype.ext hs
    rw [hF2' _ hm h, hp, smul_smul]
    congr 1
    have h1 : ((ch (tie.red_surj (p : G₀)).choose : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : σ ((ψ p : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_mul, map_inv,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_natCast, RingHom.toMonoidHom_eq_coe]
    field_simp
  rw [Finset.sum_congr rfl fun p _ => key p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

theorem ext_lvlForm_mem_span (x : Fin (S.lvlDim act P ψ) → K) :
    pres.ext (lvlForm S act P ψ x).1 ∈
      Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) := by
  have hx : x = ∑ a, x a • (Pi.single a (1 : K) : Fin (S.lvlDim act P ψ) → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e : pres.ext (lvlForm S act P ψ x).1 =
      ∑ a, σ (x a) • pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
    rw [← lvlFormL_apply, ← Bridge.ClassPres.extL_apply, hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, map_smulₛₗ, Bridge.ClassPres.extL_apply, lvlFormL_apply]
    simp [Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem ext_lvlForm_mem_cutSp (x : Fin (S.lvlDim act P ψ) → K) :
    pres.ext (lvlForm S act P ψ x).1 ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) := by
  refine Submodule.mem_inf.2 ⟨Bridge.ClassPres.extMem_holds pres _, ?_⟩
  intro κ hκ h
  have e1 := tie.act_eq (tie.red κ) κ rfl (lvlForm S act P ψ x)
  have e2 : act (tie.red κ) (lvlForm S act P ψ x) = ((ψ ⟨tie.red κ, hκ⟩ : Kˣ) : K) • lvlForm S act P ψ x :=
    lvlForm_eig x ⟨tie.red κ, hκ⟩
  rw [e2, ← Bridge.ClassPres.extL_apply, map_smulₛₗ, Bridge.ClassPres.extL_apply] at e1
  have e3 := congrFun e1 h
  simp only [Pi.smul_apply, Bridge.g0Act] at e3
  have h1 : ((ch κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_mul, RingHom.id_apply,
    RingHom.toMonoidHom_eq_coe]
  rw [mul_smul, e3, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Pres

end GlobalTheory.MtIn

namespace GlobalTheory.MtIn

section Main

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
  [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
  (pres : Bridge.ClassPres ι S σ ρ J χ) {Q : Subgroup G} {ch : Q →* ℂˣ} {G₀ : Type} [Group G₀] [Fintype G₀]
  {act : Representation K G₀ S.Forms} (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ)

theorem ext_lvlForm_single (a : Fin (S.lvlDim act P ψ)) :
    pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 = ∑ i, σ (S.lvlE act P ψ i a) • pres.ext (S.basis i).1 := by
  rw [← Bridge.ClassPres.extL_apply, lvlForm_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, Bridge.ClassPres.extL_apply]
  simp [Matrix.mulVec_single_one]

theorem lvlForm_linInd : LinearIndependent ℂ fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hb := Fintype.linearIndependent_iff.1 (Bridge.ClassPres.linInd pres)
  have hsum : ∑ i, (∑ a, g a * σ (S.lvlE act P ψ i a)) • pres.extL (S.basis i) = 0 := by
    have e : ∑ i, (∑ a, g a * σ (S.lvlE act P ψ i a)) • pres.extL (S.basis i) =
        ∑ a, g a • pres.ext (lvlForm S act P ψ (Pi.single a 1)).1 := by
      simp only [ext_lvlForm_single, Finset.smul_sum, smul_smul, Bridge.ClassPres.extL_apply, Finset.sum_smul]
      exact Finset.sum_comm
    rw [e, hg]
  have hc : ((S.lvlE act P ψ).map σ).mulVec g = 0 := by
    ext i
    have := hb _ hsum i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hinj : Function.Injective (S.lvlE act P ψ).mulVec :=
    (image_idempotent_spec K S.dim (S.gaMat act (lvlIdem P ψ))).1
  obtain ⟨gl, hgl⟩ := LinearMap.exists_leftInverse_of_injective (S.lvlE act P ψ).mulVecLin
    (LinearMap.ker_eq_bot.2 hinj)
  have hLE : LinearMap.toMatrix' gl * S.lvlE act P ψ = 1 := by
    have := congrArg LinearMap.toMatrix' hgl
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLE' : (LinearMap.toMatrix' gl).map σ * (S.lvlE act P ψ).map σ = 1 := by
    rw [← Matrix.map_mul, hLE, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h0 : g = 0 := by
    calc g = ((LinearMap.toMatrix' gl).map σ * (S.lvlE act P ψ).map σ).mulVec g := by
          rw [hLE', Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  intro a
  rw [h0]
  rfl

theorem lvlForm_span :
    Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) =
      cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ext_lvlForm_mem_cutSp pres tie P ψ _
  · intro F hF
    have hFA : F ∈ Submodule.span ℂ (Set.range pres.extL) := by
      rw [Bridge.ClassPres.span_eq]
      exact (Submodule.mem_inf.1 hF).1
    have hle : Submodule.span ℂ (Set.range pres.extL) ≤
        (Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1)).comap
          (cutAvgL ch tie.red tie.red_surj σ P ψ W) := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Bridge.ClassPres.extL_apply, cutAvgL_ext pres tie P ψ f]
      obtain ⟨x, hx⟩ := exists_lvlForm_avg (act := act) (P := P) (ψ := ψ) f
      rw [← hx]
      exact ext_lvlForm_mem_span pres P ψ x
    have := hle hFA
    rwa [Submodule.mem_comap, cutAvgL_of_mem pres tie P ψ hF] at this

theorem lvlForm_of_mem {F : G → W}
    (hF : F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ))
    (hv : ∀ c, F (pres.y c) ∈ Set.range pres.coef) : ∃ x, F = pres.ext (lvlForm S act P ψ x).1 := by
  choose f0 hf0 using hv
  have hA := (Submodule.mem_inf.1 hF).1
  have hfix : ∀ c (g : S.Gam c), S.ρ c g (f0 c) = f0 c := by
    intro c g
    have e : pres.coef (S.ρ c g (f0 c) - f0 c) = 0 := by
      rw [map_sub, pres.coef_act, hf0, Bridge.ClassPres.adForms_fixed pres hA c g, sub_self]
    exact sub_eq_zero.1 (Bridge.ClassPres.coef_inj pres e)
  let f : S.Forms := ⟨f0, hfix⟩
  have hFf : F = pres.ext f.1 := by
    refine Bridge.ClassPres.adForms_ext pres hA (Bridge.ClassPres.extMem_holds pres f) fun c => ?_
    rw [Bridge.ClassPres.ext_rep]
    exact (hf0 c).symm
  obtain ⟨x, hx⟩ := exists_lvlForm_avg (act := act) (P := P) (ψ := ψ) f
  refine ⟨x, ?_⟩
  rw [hx, ← cutAvgL_ext pres tie P ψ f, ← hFf, cutAvgL_of_mem pres tie P ψ hF]

end Main

theorem mem_lvlNab_iff {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {G₀ : Type} [Group G₀]
    [Fintype G₀] {act : Representation K G₀ S.Forms} {P : Subgroup G₀} {ψ : P →* Kˣ} (x : Fin (S.lvlDim act P ψ) → K) :
    x ∈ S.lvlNab act P ψ ↔ ∀ c, (lvlForm S act P ψ x).1 c ∈ S.Nab c := by
  show (S.lvlE act P ψ).mulVec x ∈ S.nabLat ↔ _
  rw [CSD.nabLat, mem_valLatF] <;> rfl

theorem lvlForm_adelic_basis : ∀ (G Γ W K : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (pres : Bridge.ClassPres ι S σ ρ J χ) (Q : Subgroup G) (ch : Q →* ℂˣ) (G₀ : Type) [Group G₀] [Fintype G₀] (act : Representation K G₀ S.Forms) (tie : Bridge.ActTie ι pres Q ch act) (P : Subgroup G₀) (ψ : P →* Kˣ), (LinearIndependent ℂ fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) ∧ Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S act P ψ (Pi.single a 1)).1) = cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ) ∧ (∀ F ∈ cutSp ι ρ J χ Q ch tie.red P ((Units.map σ.toMonoidHom).comp ψ), (∀ c, F (pres.y c) ∈ Set.range pres.coef) → ∃ x, F = pres.ext (lvlForm S act P ψ x).1) ∧ (∀ x, x ∈ S.lvlNab act P ψ ↔ ∀ c, (lvlForm S act P ψ x).1 c ∈ S.Nab c) ∧ (∀ (f : S.Forms) c, pres.ext f.1 (pres.y c) = pres.coef (f.1 c)) ∧ Function.Injective pres.coef := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ pres Q ch G₀ _ _ act tie P ψ
  exact ⟨lvlForm_linInd pres P ψ, lvlForm_span pres tie P ψ, fun F hF hv => lvlForm_of_mem pres tie P ψ hF hv,
    fun x => mem_lvlNab_iff x, fun f c => Bridge.ClassPres.ext_rep pres f c,
    fun a b h => sub_eq_zero.1 (Bridge.ClassPres.coef_inj pres (by rw [map_sub, h, sub_self]))⟩

end GlobalTheory.MtIn
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TSetDenom

open GlobalTheory.TSetFinCong (IntM)

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem int_of_double_coset (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ ≤ 1)
    (a b g : GL (Fin n) (v.adicCompletion F))
    (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hb : b ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (ϖ * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨ia, ia'⟩ := GlobalTheory.TSetFin.glint_int ha
  obtain ⟨ib, ib'⟩ := GlobalTheory.TSetFin.glint_int hb
  set D := Formalism.UG.diagJ n ϖ k
  let D' : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.diagonal fun i => if (i : ℕ) < k then 1 else ϖ
  have hDD : D' * D = ϖ • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    simp only [D', D, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hD : IntM D := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then ϖ else 1) ≤ 1
    split_ifs <;> simp [hϖ]
  have hD' : IntM D' := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then 1 else ϖ) ≤ 1
    split_ifs <;> simp [hϖ]
  have haa : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * b = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgi : ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * g = ϖ • 1 := by
      rw [hg]
      calc _ = ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (D' *
            ((((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a) * D)) * b := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • 1 := by rw [haa, Matrix.one_mul, hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hbb]
    calc ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))
        = (ϖ • 1) * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = _ := by rw [← h1, Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)), hgg, Matrix.mul_one]
  refine ⟨?_, fun i j => ?_⟩
  · rw [hg]; exact GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ia) hD) (show IntM _ from ib)
  · have h := GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ib') hD') (show IntM _ from ia') i j
    rw [← hgi, Matrix.smul_apply, smul_eq_mul] at h
    exact h

theorem exists_char (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : 𝓞 F) ∈ v.asIdeal) ∧ ∃ a : ℕ, Nat.card (𝓞 F ⧸ v.asIdeal) = p ^ a := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  obtain ⟨a, hp, hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal))
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), hp, ?_, a, by rw [Nat.card_eq_fintype_card, hcard]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

end Local

section Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open ReciprocityTheory.Aut

local notation3 "L⁺" => maximalRealSubfield L

theorem conj_entry (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem natCast_mul_mem (s : SplitPlace L) (c : ℕ) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (i j : Fin n) : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hc1 : Valued.v (c : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v c
  have hone : ∀ i j, s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := by
    intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hconj1 : conjAL L ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (AL L)) j i := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hdel : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) * (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    intro i j; rw [Valuation.map_mul]; refine mul_le_one' hc1 ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hz : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.TSetFin.mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, map_mul, map_mul, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h1 i j) (hdel i j))
    · rw [map_sub, map_mul, map_mul, map_natCast, conj_entry x i j, hconj1, map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h2 j i) (hdel j i))
  have hd : (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L :=
    Subring.mul_mem _ (natCast_mem (ALint L) c)
      (by by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using add_mem hz hd

theorem tSet_denom (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : Formalism.AUTREP.IsUnif L s.v ϖ)
    (p : ℕ) (hp : ((p : ℕ) : 𝓞 L⁺) ∈ s.v.asIdeal) (x : Formalism.AUTREP.GAf L n) (hx : x ∈ Formalism.AUTREP.tSet L n s ϖ k)
    (i j : Fin n) :
    (p : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
      (p : AL L) * (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨htriv, a, ha, b, hb, hg⟩ := hx
  have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hunif, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hunif; exact WithZero.coe_ne_zero hunif.symm
  obtain ⟨h1, h2⟩ := int_of_double_coset ϖ k hϖ1 a b _ ha hb hg
  have hpv : Valued.v (p : s.v.adicCompletion L⁺) ≤ WithZero.exp (-1) := by
    refine le_exp_neg_one_of_lt_one ?_
    have e : (p : s.v.adicCompletion L⁺) = algebraMap L⁺ (s.v.adicCompletion L⁺) (((p : ℕ) : 𝓞 L⁺) : L⁺) := by simp
    rw [e, adic_valued_algebraMap]
    exact (s.v.valuation_lt_one_iff_mem (K := L⁺) _).2 hp
  have ht : Valued.v ((p : s.v.adicCompletion L⁺) / ϖ) ≤ 1 := by
    rw [map_div₀, hunif]; exact div_le_one_of_le₀ hpv zero_le'
  have hpe : (p : s.v.adicCompletion L⁺) = (p : s.v.adicCompletion L⁺) / ϖ * ϖ := (div_mul_cancel₀ _ hϖ0).symm
  have hc1 : Valued.v (p : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v p
  have A1 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by rw [Valuation.map_mul]; exact mul_le_one' hc1 (h1 i j)
  have A2 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by
      rw [map_inv, hpe, mul_assoc, Valuation.map_mul]; exact mul_le_one' ht (h2 i j)
  exact ⟨natCast_mul_mem s p x htriv A1 A2 i j,
    natCast_mul_mem s p x⁻¹ (GlobalTheory.TSetFin.triv_inv htriv) A2 (fun i j => by rw [inv_inv]; exact A1 i j) i j⟩

end Glob

theorem tSet_denominator : ∀ (D : D7) (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), Formalism.AUTREP.IsUnif D.host.E s.v ϖ → ∃ p : ℕ, p.Prime ∧ s.Above p ∧ (∃ a, s.q = p ^ a) ∧ ∀ x ∈ Formalism.AUTREP.tSet D.host.E n s ϖ k, ∀ a b, (p : EAf D) * (km D n x).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (p : EAf D) * (km D n x⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n s ϖ k hϖ
  obtain ⟨p, hp, hmem, a, ha⟩ := exists_char s.v
  refine ⟨p, hp, hmem, ⟨a, ha⟩, fun x hx i j => ?_⟩
  obtain ⟨k1, k2⟩ := tSet_denom s ϖ k hϖ p hmem x hx i j
  exact ⟨(GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k1, (GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k2⟩

end GlobalTheory.TSetDenom
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.MtInType

variable {D : D7}

theorem km_eq {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    Formalism.UG.bc (swapAE D) ((toGf P g : Bridge.Gf V) : GL _ _) = km D V.rank g := hU g

section Mem

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)

theorem rowFrameImage_mem_levelQ_iff_swap {P : principalLevelFrame.RowPsi V V.rank} (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q ↔
      Formalism.UG.bc (swapAE D) ((toGf P g : Bridge.Gf V) : GL _ _) ∈ lev D.sp.cm V.gram 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  unfold levEnv
  rw [Subgroup.mem_comap]
  rfl

theorem mem_Q_iff (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q ↔
      km D V.rank g ∈ parLev D.sp.cm (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  rw [rowFrameImage_mem_levelQ_iff_swap, km_eq P hU, hg, mem_lev]
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

theorem mem_stdFrameLevelSubgroup_iff_parabolicLevel (LP : LevelP Pg D.R.r ℂ) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    g ∈ stdJ (datV D V.rank hr Pg Q LP chi xi) ↔
      km D V.rank g ∈ parLev D.sp.cm (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) ∧
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) ∈ LP.H := by
  unfold stdJ
  rw [Subgroup.mem_comap, mem_lev]
  rfl

variable {G₀ : Type} [Group G₀]

theorem mem_levPOf_H {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ) (x : G₀) :
    eG x ∈ (levPOf eG σ P₀ ψ₀).H ↔ x ∈ P₀ := by
  show eG.symm.toMonoidHom (eG x) ∈ P₀ ↔ _
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem red_eq {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) (h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q) :
    eG (red ⟨_, h⟩) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) :=
  (hred ⟨_, h⟩).trans (congrArg (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km_eq P hU g))

theorem mem_stdJ_iff (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    g ∈ stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ↔
      ∃ h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, red ⟨_, h⟩ ∈ P₀ := by
  have hQ := mem_Q_iff hr Pg Q chi xi hg hU (P := P) g
  have hH : ∀ h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q,
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) ∈ (levPOf eG D.what₂.embLL P₀ ψ₀).H ↔
        red ⟨_, h⟩ ∈ P₀ := by
    intro h
    rw [← red_eq hr Pg Q chi xi hU red eG hred g h]
    exact mem_levPOf_H Pg eG D.what₂.embLL P₀ ψ₀ _
  refine (mem_stdFrameLevelSubgroup_iff_parabolicLevel hr Pg Q chi xi _ g).trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hQ.2 h1, (hH (hQ.2 h1)).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hQ.1 h1, (hH h1).2 h2⟩

end Mem

section Chr

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
variable {G₀ : Type} [Group G₀]

theorem levPOf_ext1_apply_eq_units_map_inv {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ)
    (x : G₀) (hx : x ∈ P₀) :
    ext1 (levPOf eG σ P₀ ψ₀).conj.H (levPOf eG σ P₀ ψ₀).conj.chi (eG x) = Units.map σ.toMonoidHom ((ψ₀ ⟨x, hx⟩)⁻¹) := by
  rw [extendOne_of_mem _ (show eG x ∈ (levPOf eG σ P₀ ψ₀).conj.H from (mem_levPOf_H Pg eG σ P₀ ψ₀ x).2 hx)]
  show ((Units.map σ.toMonoidHom) (ψ₀ ((eG.symm.toMonoidHom.subgroupComap P₀) ⟨eG x, _⟩)))⁻¹ = _
  have e : (eG.symm.toMonoidHom.subgroupComap P₀) ⟨eG x, (mem_levPOf_H Pg eG σ P₀ ψ₀ x).2 hx⟩ = ⟨x, hx⟩ :=
    Subtype.ext (eG.symm_apply_apply x)
  rw [e, map_inv]

theorem extension_conj_character_eq {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ)
    (x : G₀) (hx : x ∈ P₀) (y : G0 Pg D.R.r) (hy : eG x = y) :
    ext1 (levPOf eG σ P₀ ψ₀).conj.H (levPOf eG σ P₀ ψ₀).conj.chi y = ((Units.map σ.toMonoidHom).comp ψ₀⁻¹) ⟨x, hx⟩ := by
  subst hy
  rw [levPOf_ext1_apply_eq_units_map_inv Pg eG σ P₀ ψ₀ x hx]
  rfl

theorem stdX_eq (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) (hJ : g ∈ stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi))
    (h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q) (hP : red ⟨_, h⟩ ∈ P₀) :
    stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ⟨g, hJ⟩ =
      (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch ⟨_, h⟩ *
        ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, h⟩, hP⟩ := by
  have e1 : stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ⟨g, hJ⟩ =
      ext1 (levPOf eG D.what₂.embLL P₀ ψ₀).conj.H (levPOf eG D.what₂.embLL P₀ ψ₀).conj.chi
        (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g)) *
      levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km D V.rank g) :=
    levFn_withP (V := V) (L := datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) _ _
  have e2 : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch ⟨_, h⟩ =
      levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km D V.rank g) :=
    congrArg (levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi))) (km_eq P hU g)
  have e3 : ext1 (levPOf eG D.what₂.embLL P₀ ψ₀).conj.H (levPOf eG D.what₂.embLL P₀ ψ₀).conj.chi
        (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g)) =
      ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, h⟩, hP⟩ := by
    exact extension_conj_character_eq Pg eG D.what₂.embLL P₀ ψ₀ _ hP _ (red_eq hr Pg Q chi xi hU red eG hred g h)
  exact e1.trans ((mul_comm _ _).trans (congrArg₂ (· * ·) e2.symm e3))

end Chr

section Jlev

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
variable {G₀ : Type} [Group G₀]

theorem mem_twoBlockLevelJ_iff_swap (k : Bridge.Gf V) :
    k ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J ↔
      Formalism.UG.bc (swapAE D) (k : GL _ _) ∈ lev D.sp.cm V.gram 1
        (flag1L (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  unfold levEnv
  rw [Subgroup.mem_comap]
  rfl

theorem red_J (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (k : Bridge.Gf V) (hk : k ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J) :
    red ⟨k, (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J_le hk⟩ = 1 := by
  apply eG.injective
  rw [map_one, hred]
  have h2 := ((mem_twoBlockLevelJ_iff_swap hr Pg Q chi xi k).1 hk).2
  exact Subgroup.mem_bot.1 h2

end Jlev

section Main

variable {V : HSp D} {hr : D.R.r ≤ V.rank} {Pg Q : Finset (Pl D.host.E)} {chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
  {c : CoefA V} {P : principalLevelFrame.RowPsi V V.rank} {e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V}
  {G₀ : Type} [Group G₀] {eG : G₀ ≃* G0 Pg D.R.r} {P₀ : Subgroup G₀} {ψ₀ : P₀ →* D.what₂.LLˣ}

local notation "LE" => levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)
local notation "LP" => datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi

theorem fwd_rat (hR : RatIso P e) {F : Bridge.Gf V → c.W} (hA : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (LE).J (LE).χ)
    (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    F (toGf P (↑γ * g)) = c.coef.ρ (e γ) (F (toGf P g)) := by
  have h1 := hA (e γ) (toGf P g) 1
  simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at h1
  rw [(hR γ).1, ← map_mul] at h1
  exact h1

set_option maxHeartbeats 4000000 in
theorem bwd_ad (hg : V.gram = 1) (hU : UnitFr P) (hR : RatIso P e)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (hAut : ∀ (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g : Formalism.AUTREP.GAf D.host.E V.rank),
      F (toGf P (↑γ * g)) = c.coef.ρ (e γ) (F (toGf P g)))
    (law : ∀ κ (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank),
        F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g)) :
    F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (LE).J (LE).χ := by
  intro γ h k
  have hs : Function.Surjective (toGf P) := GlobalTheory.MtInRat.toGf_surjective P
  have key : ∀ (γ' : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g k' : Formalism.AUTREP.GAf D.host.E V.rank) (hkJ : toGf P k' ∈ (LE).J),
      F (Bridge.ratF V (e γ') * toGf P g * toGf P k') = (((LE).χ ⟨_, hkJ⟩ : ℂˣ) : ℂ) • c.coef.ρ (e γ') (F (toGf P g)) := by
    intro γ' g k' hkJ
    have hQk := (LE).J_le hkJ
    have hr1 := red_J hr Pg Q chi xi red eG hred _ hkJ
    have hP : red ⟨_, hQk⟩ ∈ P₀ := by rw [hr1]; exact P₀.one_mem
    have hJ := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _).2 ⟨hQk, hP⟩
    have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _ hJ hQk hP
    have hch := (LE).ch_J ⟨_, hkJ⟩
    have h1 := hAut γ' (g * k')
    have h2 := law k' hJ g
    have e1 : Bridge.ratF V (e γ') * toGf P g * toGf P k' = toGf P (↑γ' * (g * k')) := by
      calc _ = toGf P (↑γ' * g) * toGf P k' := by rw [(hR γ').1, (toGf P).map_mul ↑γ' g]
        _ = toGf P (↑γ' * g * k') := ((toGf P).map_mul _ _).symm
        _ = _ := by rw [mul_assoc]
    have h1' : (⟨red ⟨_, hQk⟩, hP⟩ : P₀) = 1 := Subtype.ext hr1
    have hval : stdX (LP) ⟨k', hJ⟩ = (LE).χ ⟨_, hkJ⟩ := by
      rw [hX, h1', map_one, mul_one]
      exact hch
    refine (congrArg F e1).trans (h1.trans ((congrArg (c.coef.ρ (e γ')) h2).trans ((map_smul _ _ _).trans ?_)))
    rw [hval]
  have hgh : toGf P (Function.surjInv hs h) = h := Function.surjInv_eq hs h
  have hk' : toGf P (Function.surjInv hs k.1) = k.1 := Function.surjInv_eq hs k.1
  have hkJ : toGf P (Function.surjInv hs k.1) ∈ (LE).J := by rw [hk']; exact k.2
  have hk2 : (⟨_, hkJ⟩ : (LE).J) = k := Subtype.ext hk'
  have hmain := key (e.symm γ) (Function.surjInv hs h) (Function.surjInv hs k.1) hkJ
  rw [hk2, e.apply_symm_apply γ, hgh, hk'] at hmain
  exact hmain

set_option maxHeartbeats 4000000 in
theorem bwd_q (hg : V.gram = 1) (hU : UnitFr P)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (law : ∀ κ (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank),
        F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g))
    (κ : (LE).Q) (hκ : red κ ∈ P₀) (h : Bridge.Gf V) :
    F (h * κ) = (((LE).ch κ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h := by
  have hs : Function.Surjective (toGf P) := GlobalTheory.MtInRat.toGf_surjective P
  have key : ∀ (g k' : Formalism.AUTREP.GAf D.host.E V.rank) (hQ : toGf P k' ∈ (LE).Q) (hP : red ⟨_, hQ⟩ ∈ P₀),
      F (toGf P g * toGf P k') =
        (((LE).ch ⟨_, hQ⟩ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, hQ⟩, hP⟩ : ℂˣ) : ℂ) • F (toGf P g) := by
    intro g k' hQ hP
    have hJ := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _).2 ⟨hQ, hP⟩
    have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _ hJ hQ hP
    refine ((congrArg F ((toGf P).map_mul g k')).symm.trans (law k' hJ g)).trans ?_
    rw [hX]
  have hgh : toGf P (Function.surjInv hs h) = h := Function.surjInv_eq hs h
  have hk' : toGf P (Function.surjInv hs κ.1) = κ.1 := Function.surjInv_eq hs κ.1
  have hQ : toGf P (Function.surjInv hs κ.1) ∈ (LE).Q := by rw [hk']; exact κ.2
  have hk2 : (⟨_, hQ⟩ : (LE).Q) = κ := Subtype.ext hk'
  have hP : red ⟨_, hQ⟩ ∈ P₀ := by rw [hk2]; exact hκ
  have hmain := key (Function.surjInv hs h) (Function.surjInv hs κ.1) hQ hP
  revert hP
  rw [hk2]
  intro hP hmain
  rw [hgh, hk'] at hmain
  exact hmain

set_option maxHeartbeats 4000000 in
theorem fwd_law (hg : V.gram = 1) (hU : UnitFr P)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (hQc : ∀ (κ : (LE).Q) (hκ : red κ ∈ P₀) (h : Bridge.Gf V),
      F (h * κ) = (((LE).ch κ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h)
    (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g) := by
  have hm := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred κ).1 hJ
  have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred κ hJ hm.1 hm.2
  refine (congrArg F ((toGf P).map_mul g κ)).trans ?_
  rw [hX]
  exact hQc ⟨_, hm.1⟩ hm.2 (toGf P g)

end Main

set_option maxHeartbeats 4000000 in
theorem cutSp_iff_typeSp : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  intro D V hr Pg Q chi xi c P e hg hU hR G₀ _ red eG P₀ ψ₀ hred F
  constructor
  · intro hF
    refine ⟨⟨fun γ g => fwd_rat hR hF.1 γ g, ?_⟩, fun κ => funext fun g => fwd_law hg hU red hred hF.2 κ.1 κ.2 g⟩
    have hC := (GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial D V.rank (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)).2.1
    refine ⟨hC.choose, hC.choose_spec.1, fun κ hκ g => ?_⟩
    have hC' := hC.choose_spec.2 κ hκ
    refine (fwd_law hg hU red hred hF.2 κ hC'.1 g).trans ?_
    rw [hC'.2, Units.val_one, one_smul]
  · intro hF
    exact ⟨bwd_ad hg hU hR red hred hF.1.1 (fun κ hJ g => congrFun (hF.2 ⟨κ, hJ⟩) g),
      bwd_q hg hU red hred (fun κ hJ g => congrFun (hF.2 ⟨κ, hJ⟩) g)⟩

end GlobalTheory.MtInType
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  atlas_forward_decl GlobalTheory.MtInType.cutSp_iff_typeSp
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedStdLattice_lattice_comparison_rational : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  first | exact @GlobalTheory.HLatStd.hLat_props | exact GlobalTheory.HLatStd.hLat_props | (intros; apply GlobalTheory.HLatStd.hLat_props <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem ext_vals : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  intro D V hStd c S J χ pres lam c0 pair del hMap hTie hJ hχ f
  obtain ⟨e, -, hcoef, -, hnab, -⟩ := hTie
  have hL := (GlobalTheory.T.translatedStdLattice_lattice_comparison_rational D V hStd).2.2
  have key : ∀ h, ∃ (z : 𝓞 D.what₂.LL) (γE : GL (Fin V.rank) D.host.E),
      Bridge.IsRatMat V (pres.decG h) γE ∧
      pres.ext f.1 h = c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
    intro h
    obtain ⟨z, hz⟩ := hχ (pres.decK h)
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V (pres.decG h) γE := by
      obtain ⟨g, hg⟩ := (pres.decG h).2
      exact ⟨g, hg.2.symm⟩
    refine ⟨z, γE, hγ, ?_⟩
    have a1 : pres.ext f.1 h = ((χ (pres.decK h) : ℂˣ) : ℂ) • c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) := rfl
    have a2 : c.coef.ρ (pres.decG h) (pres.coef (f.1 (pres.decC h))) =
        c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) := by
      rw [hcoef]; exact (hMap.1 _ _ hγ _).symm
    have a3 : c0 ((z : D.what₂.LL) • rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) =
        D.what₂.embLL (z : D.what₂.LL) • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h)))) :=
      map_smulₛₗ c0 _ _
    refine a1.trans ((congrArg (fun w => ((χ (pres.decK h) : ℂˣ) : ℂ) • w) a2).trans ?_)
    refine Eq.trans ?_ a3.symm
    exact congrArg (fun s : ℂ => s • c0 (rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))))) hz.symm
  refine ⟨fun h => ?_, fun hf h => ?_⟩
  · obtain ⟨z, γE, -, hv⟩ := key h
    exact ⟨_, hv.symm⟩
  obtain ⟨z, γE, hγ, hv⟩ := key h
  refine ⟨_, ?_, hv⟩

  have hlat : Bridge.hLat V h = (Bridge.hLat V (pres.y (pres.decC h))).map
      ((Matrix.mulVecLin (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).restrictScalars (𝓞 D.host.E)) := by
    have h1 : Bridge.hLat V h = Bridge.hLat V (Bridge.ratF V (pres.decG h) * pres.y (pres.decC h)) := by
      conv_lhs => rw [pres.dec_spec h]
      exact hJ _ (pres.decK h).2 _
    rw [h1]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    constructor
    · intro hx
      refine ⟨((γE⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x, ?_, ?_⟩
      · rw [hL _ _ hγ, Matrix.mulVec_mulVec]
        simpa using hx
      · rw [Matrix.mulVec_mulVec]
        simp
    · rintro ⟨y, hy, rfl⟩
      exact (hL _ _ hγ _ _).1 hy
  have hmem : e (f.1 (pres.decC h)) ∈ nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h))) := by
    rw [← hnab]
    exact ⟨_, hf _, rfl⟩
  have hga := Formalism.L2.Col.nabAtr_gmap (labLL D) lam ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE)
    (Bridge.hLat V (pres.y (pres.decC h)))
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply] at hga
  rw [hlat, hga]
  have h2 : rhoVr (labLL D) lam γE (e (f.1 (pres.decC h))) ∈ (nabAtr (labLL D) lam (Bridge.hLat V (pres.y (pres.decC h)))).map
      ((rhoVr (labLL D) lam γE).restrictScalars (𝓞 D.what₂.LL)) := ⟨_, hmem, rfl⟩
  first
    | exact Submodule.smul_mem _ z h2
    | exact (algebraMap_smul D.what₂.LL z _ ▸ Submodule.smul_mem _ z h2)
    | simpa [Algebra.smul_def] using Submodule.smul_mem _ z h2

end GlobalTheory.MtIn
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFormFunction_values_mem_coefficientLattice : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  atlas_forward_decl GlobalTheory.MtIn.ext_vals
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInHecke

section

open Formalism.L2.Col Formalism.HermitianLatticesTheory Module

section Comm

variable {K : Type} [Field K] [NumberField K]

theorem localized_eq_of_commensurable {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K))
    {M M' : Submodule (𝓞 K) W} {s : 𝓞 K} (hs : s ∉ w.asIdeal) (h1 : ∀ x ∈ M, s • x ∈ M') (h2 : ∀ x ∈ M', s • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M' := by
  apply le_antisymm
  · rintro x ⟨t, ht, hx⟩
    exact ⟨s * t, lc_mul_notMem w hs ht, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨s * t, lc_mul_notMem w hs ht, by rw [mul_smul]; exact h2 _ hx⟩

theorem localized_comap {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]
    (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[𝓞 K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (N.comap f) = (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N).comap f := by
  ext x
  simp only [lc_mem_locP, Submodule.mem_comap, map_smul]

theorem lat_dualFr_comm {n : ℕ} {M M' : Submodule (𝓞 K) (Fin n → K)} {s : 𝓞 K} (h : ∀ y ∈ M, s • y ∈ M') :
    ∀ x ∈ dualFr M', s • x ∈ dualFr M := by
  intro x hx y hy
  show (s • x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  rw [smul_dotProduct, ← dotProduct_smul]
  exact hx _ (h y hy)

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K)

theorem lat_tauLat_comm (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {q : ℕ} (h : ∀ x ∈ L, (q : 𝓞 E) • x ∈ L') :
    ∀ y ∈ tauLat emb τ L, (q : 𝓞 K) • y ∈ tauLat emb τ L' := by
  intro y hy
  have hle : tauLat emb τ L ≤ (tauLat emb τ L').comap (LinearMap.lsmul (𝓞 K) (Fin n → K) (q : 𝓞 K)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (q : 𝓞 K) • (fun a => emb τ (x a)) ∈ tauLat emb τ L'
    refine Submodule.subset_span ⟨(q : 𝓞 E) • x, h x hx, ?_⟩
    funext a
    simp [Algebra.smul_def]
  exact hle hy

theorem localized_nabla_eq_of_commensurable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L') {q : ℕ} (h1 : ∀ x ∈ L, (q : 𝓞 E) • x ∈ L')
    (h2 : ∀ x ∈ L', (q : 𝓞 E) • x ∈ L) (hq : (q : 𝓞 K) ∉ w.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam L') := by
  have hM : ∀ τ, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (dualFr (tauLat emb τ L)) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (dualFr (tauLat emb τ L')) :=
    fun τ => localized_eq_of_commensurable w hq (lat_dualFr_comm (lat_tauLat_comm emb τ h2))
      (lat_dualFr_comm (lat_tauLat_comm emb τ h1))
  have hlat := fun τ => dualFr_tauLat_isLattice emb τ L hL
  have hlat' := fun τ => dualFr_tauLat_isLattice emb τ L' hL'
  choose B hB using fun τ => latticeBasisExists_holds K n (dualFr (tauLat emb τ L)) (hlat τ) w
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ L')) (B τ) := fun τ => by
    unfold IsBasisAt
    rw [← hM τ]
    exact hB τ
  unfold nabAtr nabK
  rw [localized_comap, localized_comap]
  congr 1
  unfold nabP
  rw [nb_loc (nb_stab_nab lam) (nb_comm_nab lam) _ hlat w B hB, nb_loc (nb_stab_nab lam) (nb_comm_nab lam) _ hlat' w B hB']

end Comm

end

theorem heckeD_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    (Λ : Formalism.AUTREP.GAf L n → AddSubmonoid W) (J : Subgroup (Formalism.AUTREP.GAf L n)) (T : Set (Formalism.AUTREP.GAf L n))
    (hΛ : ∀ g, ∀ x ∈ T, Λ (g * x) ≤ Λ g) (f : Formalism.AUTREP.GAf L n → W) (hf : ∀ g, f g ∈ Λ g) (g : Formalism.AUTREP.GAf L n) :
    NG.heckeD J T f g ∈ Λ g := by
  classical
  unfold NG.heckeD
  apply finsum_induction (fun w => w ∈ Λ g)
  · exact (Λ g).zero_mem
  · intro a b ha hb; exact (Λ g).add_mem ha hb
  · intro c
    split_ifs with hc
    · exact hΛ g _ hc.choose_spec.1 (hf _)
    · exact (Λ g).zero_mem

theorem tN_val {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {K U : Type} [Field K] [AddCommGroup U] [Module K U] {σ : K →+* ℂ} (c0 : U →ₛₗ[σ] W)
    (Λ : Formalism.AUTREP.GAf L n → AddSubmonoid U) (J : Subgroup (Formalism.AUTREP.GAf L n)) (s : ReciprocityTheory.Aut.SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hΛ : ∀ g, ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, Λ (g * x) ≤ Λ g) (f : Formalism.AUTREP.GAf L n → W)
    (hf : ∀ g, ∃ v ∈ Λ g, f g = c0 v) (g : Formalism.AUTREP.GAf L n) :
    ∃ v ∈ Λ g, NG.tN J s ϖ k f g = c0 (((s.q : K) ^ (k * (n - 1)))⁻¹ • v) := by
  obtain ⟨v, hv, e⟩ := heckeD_mem (fun g => (Λ g).map c0.toAddMonoidHom) J _
    (fun g x hx => AddSubmonoid.monotone_map (hΛ g x hx)) f
    (fun g => by obtain ⟨v, hv, e⟩ := hf g; exact ⟨v, hv, e.symm⟩) g
  refine ⟨v, hv, ?_⟩
  show ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • NG.heckeD J (Formalism.AUTREP.tSet L n s ϖ k) f g = _
  rw [← e, map_smulₛₗ, map_inv₀, map_pow, map_natCast]
  rfl

section Lvl

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ)

def lvlLin : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlLin_apply (x : Fin (S.lvlDim r P ψ) → K) : lvlLin S r P ψ x = lvlForm S r P ψ x := rfl

theorem ext_mem_span {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G}
    {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (pres : Bridge.ClassPres ι S σ ρ J χ)
    (x : Fin (S.lvlDim r P ψ) → K) :
    pres.ext (lvlForm S r P ψ x).1 ∈
      Submodule.span ℂ (Set.range fun a => pres.ext (lvlForm S r P ψ (Pi.single a 1)).1) := by
  have e : pres.ext (lvlForm S r P ψ x).1 = ∑ a, σ (x a) • pres.ext (lvlForm S r P ψ (Pi.single a 1)).1 := by
    show pres.extL (lvlLin S r P ψ x) = ∑ a, σ (x a) • pres.extL (lvlLin S r P ψ (Pi.single a 1))
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, map_smulₛₗ]
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem clear_den (w : HeightOneSpectrum (𝓞 K)) (x : Fin (S.lvlDim r P ψ) → K)
    (h : ∀ c, ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ t • (lvlForm S r P ψ x).1 c ∈ S.Nab c) :
    ∃ d : 𝓞 K, d ∉ w.asIdeal ∧ ∀ c, (lvlForm S r P ψ (d • x)).1 c ∈ S.Nab c := by
  classical
  choose t ht hm using h
  refine ⟨∏ c, t c, ?_, fun c => ?_⟩
  · exact (w.asIdeal.primeCompl (hp := w.isPrime)).prod_mem (fun c _ => ht c)
  · have e : (lvlForm S r P ψ ((∏ c, t c) • x)).1 c = (∏ c, t c) • (lvlForm S r P ψ x).1 c := by
      rw [← algebraMap_smul K (∏ c, t c) x, ← lvlLin_apply, map_smul, ← algebraMap_smul K (∏ c, t c)]
      rfl
    rw [e, ← Finset.prod_erase_mul _ _ (Finset.mem_univ c), mul_smul]
    exact Submodule.smul_mem _ _ (hm c)

end Lvl

theorem inv_smul_locP {K U : Type} [Field K] [NumberField K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U]
    [IsScalarTower (𝓞 K) K U] (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) U) {q : ℕ} (N : ℕ)
    (hq : (q : 𝓞 K) ∉ w.asIdeal) {v : U} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧ t • (((q : K) ^ N)⁻¹ • v) ∈ M := by
  obtain ⟨t, ht, hv⟩ := hv
  have hq0 : (q : K) ≠ 0 := by
    intro h
    have : q = 0 := by exact_mod_cast h
    apply hq
    rw [this, Nat.cast_zero]
    exact w.asIdeal.zero_mem
  refine ⟨t * (q : 𝓞 K) ^ N, fun h => ?_, ?_⟩
  · rcases w.isPrime.mem_or_mem h with h | h
    · exact ht h
    · exact hq (w.isPrime.mem_of_pow_mem _ h)
  · rw [mul_smul, ← algebraMap_smul K ((q : 𝓞 K) ^ N), map_pow, map_natCast, smul_smul ((q : K) ^ N),
      mul_inv_cancel₀ (pow_ne_zero _ hq0), one_smul]
    exact hv

variable {D : D7}

theorem lev_int (V : HSp D) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V) (hk : k ∈ (levEnv V 1 L).J) (a b) :
    swapAE D (k.1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h : Formalism.UG.bc (swapAE D) k.1 ∈ lev D.sp.cm V.gram 1 (flag1L L) := hk
  obtain ⟨y, hy⟩ := parLev_St h.1
  have e : intGL D.host.F D.host.E V.rank y = Formalism.UG.bc (swapAE D) k.1 := by
    rw [← hy]; simp [frGL]
  have e2 : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = swapAE D (k.1.val a b) :=
    congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) e
  rw [← e2]
  exact (y.val a b).2

theorem hLat_lev (V : HSp D) (hV : Seed.FrmC.StdLat V) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ k ∈ (levEnv V 1 L).J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h := by
  have key : ∀ k ∈ (levEnv V 1 L).J, ∀ h, Bridge.hLat V h ≤ Bridge.hLat V (h * k) := by
    intro k hk h y hy
    have := (GlobalTheory.HLatStd.hLat_props D V hV).2.1 h k 1 (fun a b => by
      rw [Nat.cast_one, one_mul]; exact lev_int V L _ (inv_mem hk) a b) y hy
    rwa [Nat.cast_one, one_smul] at this
  intro k hk h
  refine le_antisymm ?_ (key k hk h)
  have := key k⁻¹ (inv_mem hk) (h * k)
  rwa [mul_inv_cancel_right] at this

theorem swap_toGf {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) (x) (a b) :
    swapAE D ((toGf P x).1.val a b) = (km D V.rank x).val a b := by
  rw [← hU x]; rfl

theorem localization_nabAtr_eq' {V : HSp D} (hV : Seed.FrmC.StdLat V)
    (lam : D.what₂.Tau → DomWeight V.rank) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) {p : ℕ} (hp : (p : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (h y : Bridge.Gf V)
    (hy : ∀ a b, (p : EAf D) * swapAE D (y.1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy' : ∀ a b, (p : EAf D) * swapAE D ((y⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (h * y))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V h)) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HLatStd.hLat_props D V hV
  have a1 := h2 (h * y) y⁻¹ p (fun a b => by rw [inv_inv]; exact hy a b)
  rw [mul_inv_cancel_right] at a1
  exact localized_nabla_eq_of_commensurable _ lam w (h1 _) (h1 _) a1 (h2 h y p hy') hp

theorem line₅ {V : HSp D} (hV : Seed.FrmC.StdLat V) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P)
    (lam : D.what₂.Tau → DomWeight V.rank) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) {p : ℕ} (hp : (p : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (g x : Formalism.AUTREP.GAf D.host.E V.rank)
    (hx : ∀ a b, (p : EAf D) * (km D V.rank x).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      (p : EAf D) * (km D V.rank x⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P (g * x)))) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P g))) := by
  have e1 : toGf P (g * x) = toGf P g * toGf P x := (toGf P).map_mul g x
  have e2 : (toGf P x)⁻¹ = toGf P x⁻¹ := ((toGf P).map_inv x).symm
  rw [e1]
  refine localization_nabAtr_eq' hV lam w hp _ _ (fun a b => ?_) (fun a b => ?_)
  · rw [swap_toGf P hU]; exact (hx a b).1
  · rw [e2, swap_toGf P hU]; exact (hx a b).2

set_option maxHeartbeats 1600000 in

theorem tN_core {V : HSp D} {c : CoefA V} (P : principalLevelFrame.RowPsi V V.rank) (hg : V.gram = 1) (hV : Seed.FrmC.StdLat V) (hU : UnitFr P)
    {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {Qg : Subgroup (Bridge.Gf V)} {ch : Qg →* ℂˣ}
    {G₀ : Type} [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms)
    (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (tie : Bridge.ActTie (Bridge.ratF V) pres Qg ch act)
    (P₀ : Subgroup G₀) (ψ : P₀ →* D.what₂.LLˣ) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (pair del) (hmap : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam))
    (hcoef : Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del)
    (hlev : ∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h)
    (hint : ∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ))
    (Js : Subgroup (Formalism.AUTREP.GAf D.host.E V.rank)) (TS : Set (Formalism.AUTREP.GAf D.host.E V.rank → c.W))
    (htype : ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ J χ Qg ch tie.red P₀
      ((Units.map D.what₂.embLL.toMonoidHom).comp ψ) ↔ (fun g => F (toGf P g)) ∈ TS)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ)
    (hϖ : Formalism.AUTREP.IsUnif D.host.E s.v ϖ) (hTS : ∀ f ∈ TS, NG.tN Js s ϖ k f ∈ TS) (x) :
    ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ x').1 (toGf P g)) =
        NG.tN Js s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) ∧
      ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) →
        x ∈ S.lvlNab act P₀ ψ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ := by
  obtain ⟨-, hspan, hrat, hnab, hy, hinj⟩ := GlobalTheory.MtIn.lvlForm_adelic_basis _ _ _ _ _ S _ _ _ _ pres _ _ G₀ act tie P₀ ψ
  have hbij := (GlobalTheory.MtInRat.toGf_bij_ratIso D V P hg hU).1
  have hvals := GlobalTheory.T.adelicFormFunction_values_mem_coefficientLattice D V hV c S _ _ pres lam c0 pair del hmap hcoef hlev hint (lvlForm S act P₀ ψ x)
  have hF0 := ext_mem_span S act P₀ ψ pres x
  rw [hspan] at hF0
  have hT := hTS _ ((htype _).1 hF0)
  obtain ⟨eV, -, hce, -, hN, -⟩ := hcoef
  obtain ⟨u, hu, hu'⟩ : ∃ u : Bridge.Gf V → Formalism.AUTREP.GAf D.host.E V.rank,
      (∀ g, u (toGf P g) = g) ∧ ∀ h, toGf P (u h) = h :=
    ⟨Function.surjInv hbij.2, Function.leftInverse_surjInv hbij, Function.surjInv_eq hbij.2⟩
  have hval := fun Λ h1 h2 => tN_val c0 Λ Js s ϖ k h1 (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) h2
  have hv1 : ∀ g, ∃ v ∈ (⊤ : AddSubmonoid (VV D.what₂.LL lam)), pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g) = c0 v :=
    fun g => (Set.mem_range.1 (hvals.1 (toGf P g))).imp fun v hv => ⟨trivial, hv.symm⟩
  obtain ⟨T, hTd⟩ : ∃ T : Formalism.AUTREP.GAf D.host.E V.rank → c.W,
      T = NG.tN (W := c.W) Js s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g)) := ⟨_, rfl⟩
  replace hT : T ∈ TS := by rw [hTd]; exact hT
  replace hval : ∀ Λ : Formalism.AUTREP.GAf D.host.E V.rank → AddSubmonoid (VV D.what₂.LL lam),
      (∀ g, ∀ y ∈ Formalism.AUTREP.tSet D.host.E V.rank s ϖ k, Λ (g * y) ≤ Λ g) →
      (∀ g, ∃ v ∈ Λ g, pres.ext (lvlForm S act P₀ ψ x).1 (toGf P g) = c0 v) →
      ∀ g, ∃ v ∈ Λ g, T g = c0 (((s.q : D.what₂.LL) ^ (k * (V.rank - 1)))⁻¹ • v) := by
    rw [hTd]; exact hval
  have hTu : (fun g => T (u (toGf P g))) = T := funext fun g => congrArg T (hu g)
  have hT' : (fun g => T (u (toGf P g))) ∈ TS := by rw [hTu]; exact hT
  have hcut := (htype (fun h => T (u h))).2 hT'
  obtain ⟨x', hx'⟩ := hrat _ hcut (fun a => by
    obtain ⟨v, -, hv⟩ := hval (fun _ => ⊤) (fun _ _ _ => le_rfl) hv1 (u (pres.y a))
    exact ⟨eV.symm _, (hce _).trans ((congrArg c0 (eV.apply_symm_apply _)).trans hv.symm)⟩)
  refine ⟨x', (funext fun g => (congrFun hx' (toGf P g)).symm).trans (hTu.trans hTd), fun w hw hx => ?_⟩
  obtain ⟨p, hp, hab, ⟨m, hq⟩, hts⟩ := GlobalTheory.TSetDenom.tSet_denominator D V.rank s ϖ k hϖ
  have hpw := hw p hp hab
  have hqw : ((s.q : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hpw (w.isPrime.mem_of_pow_mem m (by
    rwa [hq, Nat.cast_pow] at h))
  have hint' := hvals.2 ((hnab x).1 hx)
  obtain ⟨d, hd, hdm⟩ := clear_den S act P₀ ψ w x' (fun a => by
    obtain ⟨v, hvm, hv⟩ := hval
      (fun g => (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam (Bridge.hLat V (toGf P g)))).toAddSubmonoid)
      (fun g y hy => le_of_eq (congrArg Submodule.toAddSubmonoid (line₅ hV P hU lam w hpw g y (hts y hy))))
      (fun g => by
        obtain ⟨v, hv, e⟩ := hint' (toGf P g)
        exact ⟨v, ⟨1, (w.asIdeal.primeCompl (hp := w.isPrime)).one_mem, by rwa [one_smul]⟩, e⟩) (u (pres.y a))
    rw [hu'] at hvm
    obtain ⟨t, ht, htm⟩ := inv_smul_locP w _ (k * (V.rank - 1)) hqw hvm
    refine ⟨t, ht, ?_⟩
    have e1 : (lvlForm S act P₀ ψ x').1 a = eV.symm (((s.q : D.what₂.LL) ^ (k * (V.rank - 1)))⁻¹ • v) := by
      apply hinj
      exact (hy _ a).symm.trans ((congrFun hx' _).symm.trans
        (hv.trans ((hce _).trans (congrArg c0 (eV.apply_symm_apply _))).symm))
    rw [← hN a] at htm
    obtain ⟨z, hz, hze⟩ := htm
    have : t • (lvlForm S act P₀ ψ x').1 a = z := by
      apply eV.injective
      rw [e1, ← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
      exact hze.symm
    rw [this]; exact hz)
  exact ⟨d, hd, (hnab _).2 hdm⟩

set_option maxHeartbeats 1600000 in

theorem tN_lvlForm : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → Seed.FrmC.StdLat V → UnitFr P → RatIso P e → Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e) → (wtRep c e).IsIrreducible → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ) (tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ((levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)) → ∀ B, NG.HypOutside (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) B → ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ V.rank → ∀ x, ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x').1 (toGf P g)) = NG.tN (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x).1 (toGf P g)) ∧ ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) → x ∈ S.lvlNab act P₀ ψ₀⁻¹ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ₀⁻¹ := by
  intro D V hr Pg Q chi xi c P e hg hV hU hR halg hirr G₀ _ _ S act pres tie eG P₀ ψ₀ hred lam c0 pair del hmap hcoef hint
    B hB s ϖ k hs hϖ hk1 hk2 x
  exact tN_core P hg hV hU S act pres tie P₀ ψ₀⁻¹ lam c0 pair del hmap hcoef (hLat_lev V hV _) hint _ _
    (GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace D V hr Pg Q chi xi c P e hg hU hR G₀ tie.red eG P₀ ψ₀ hred) s ϖ k hϖ
    (GlobalTheory.HeckeStdFacts.heckeStdPlain D.host.E V.rank (NG.AlgWt.mk c.W (wtRep c e) halg hirr) _ _ B
      (GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial D V.rank _).2.1 hB s ϖ k hs hϖ hk1 hk2).1 x

end GlobalTheory.MtInHecke

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_keeps_rational_integral_levelForms : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → Seed.FrmC.StdLat V → UnitFr P → RatIso P e → Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e) → (wtRep c e).IsIrreducible → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ) (tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ((levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)) → ∀ B, NG.HypOutside (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) B → ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ V.rank → ∀ x, ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x').1 (toGf P g)) = NG.tN (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x).1 (toGf P g)) ∧ ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) → x ∈ S.lvlNab act P₀ ψ₀⁻¹ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ₀⁻¹ := by
  atlas_forward_decl GlobalTheory.MtInHecke.tN_lvlForm
end
