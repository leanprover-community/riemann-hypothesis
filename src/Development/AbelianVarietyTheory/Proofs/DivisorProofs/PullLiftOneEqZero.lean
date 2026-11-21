import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZero

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleOnOpen_pull_comp_iso : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z), IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  first | exact @GlobalTheory.PicGlue.isOn_pull_comp | exact GlobalTheory.PicGlue.isOn_pull_comp | (intros; apply GlobalTheory.PicGlue.isOn_pull_comp <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'), L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  first | exact @GlobalTheory.PicGlue.exists_isOn_of_openImmersion | exact GlobalTheory.PicGlue.exists_isOn_of_openImmersion | (intros; apply GlobalTheory.PicGlue.exists_isOn_of_openImmersion <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso : ∀ (X : Scheme.{0}) (W : X.Opens) (L M : LB X), LBIso (L.pull W.ι) (M.pull W.ι) → ∃ w : Cmp W L M, IsoOn W L M w := by
  first | exact @GlobalTheory.PicGlue.isoOn_of_lbIso | exact GlobalTheory.PicGlue.isoOn_of_lbIso | (intros; apply GlobalTheory.PicGlue.isoOn_of_lbIso <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X), IsoOn W L M w → (∀ z, r z ∈ W) → LBIso (L.pull r) (M.pull r) := by
  first | exact @GlobalTheory.PicGlue.lbIso_pull_of_isoOn | exact GlobalTheory.PicGlue.lbIso_pull_of_isoOn | (intros; apply GlobalTheory.PicGlue.lbIso_pull_of_isoOn <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X), (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  first | exact @GlobalTheory.PicGlue.rigOn_of_triv_open | exact GlobalTheory.PicGlue.rigOn_of_triv_open | (intros; apply GlobalTheory.PicGlue.rigOn_of_triv_open <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → ∀ (V : Y.Opens) (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M), IsOn W₁ L → IsOn W₂ M → p ⁻¹ᵁ V ≤ W₁ → p ⁻¹ᵁ V ≤ W₂ → IsoOn (p ⁻¹ᵁ V) L M w → RigOn e L r → RigOn e M r' → ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  first | exact @GlobalTheory.PicGlue.exists_norm | exact GlobalTheory.PicGlue.exists_norm | (intros; apply GlobalTheory.PicGlue.exists_norm <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem cocycle_defect_eq {G : Type} [CommGroup G] {A B C A' B' C' G₁ G₂ G₃ : G} (h₁ : A * G₂ = G₁ * A')
    (h₂ : B * G₃ = G₂ * B') (h₃ : C * G₃ = G₁ * C') : A * B * C⁻¹ = A' * B' * C'⁻¹ := by
  have e₁ : A' = G₁⁻¹ * (A * G₂) := by rw [h₁, inv_mul_cancel_left]
  have e₂ : B' = G₂⁻¹ * (B * G₃) := by rw [h₂, inv_mul_cancel_left]
  have e₃ : C' = G₁⁻¹ * (C * G₃) := by rw [h₃, inv_mul_cancel_left]
  subst e₁ e₂ e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cocycle_defect_one {G : Type} [CommGroup G] {A B C R₁ R₂ R₃ : G} (h₁ : A * R₂ = R₁) (h₂ : B * R₃ = R₂)
    (h₃ : C * R₃ = R₁) : A * B * C⁻¹ = 1 := by
  rw [mul_inv_eq_one]
  apply mul_right_cancel (b := R₃)
  rw [_root_.mul_assoc, h₂, h₁, h₃]

theorem norm_cocycle : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  intro X Y p e hep hp V W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ L₁ L₂ L₃ w₁₂ w₂₃ w₁₃ r₁ r₂ r₃ h₁ h₂ h₃ hVW hVW' i₁₂ i₂₃ i₁₃
    n₁₂ n₂₃ n₁₃ x a b c hx ha hb hc
  let O : L₁.ι × L₂.ι × L₃.ι → X.Opens := fun j ↦ p ⁻¹ᵁ V ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1 ⊓ L₃.U j.2.2)
  have mO : ∀ (j : L₁.ι × L₂.ι × L₃.ι) (z : X),
      z ∈ O j ↔ p z ∈ V ∧ z ∈ L₁.U j.1 ∧ z ∈ L₂.U j.2.1 ∧ z ∈ L₃.U j.2.2 := by
    intro j z
    simp only [O, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have mW : ∀ z : X, p z ∈ V → (z ∈ W₁ ∧ z ∈ W₂ ∧ z ∈ W₃) ∧ z ∈ W₁₂ ∧ z ∈ W₂₃ ∧ z ∈ W₁₃ := by
    intro z hz
    have e₁ := hVW (show z ∈ p ⁻¹ᵁ V from hz)
    have e₂ := hVW' (show z ∈ p ⁻¹ᵁ V from hz)
    simp only [TopologicalSpace.Opens.mem_inf] at e₁ e₂
    exact ⟨⟨e₁.1.1, e₁.1.2, e₁.2⟩, e₂.1.1, e₂.1.2, e₂.2⟩
  have l₁₂ : ∀ j, O j ≤ W₁₂ ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.1, hz.2.1, hz.2.2.1⟩
  have l₂₃ : ∀ j, O j ≤ W₂₃ ⊓ (L₂.U j.2.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.1, hz.2.2.1, hz.2.2.2⟩
  have l₁₃ : ∀ j, O j ≤ W₁₃ ⊓ (L₁.U j.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.2, hz.2.1, hz.2.2.2⟩
  let u : ∀ j, Γ(X, O j)ˣ := fun j ↦
    res (l₁₂ j) (w₁₂ j.1 j.2.1) * res (l₂₃ j) (w₂₃ j.2.1 j.2.2) * (res (l₁₃ j) (w₁₃ j.1 j.2.2))⁻¹
  have hu : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j : L₁.ι × L₂.ι × L₃.ι), f z ∈ O j →
      gm f z (O j) (u j) = gm f z _ (w₁₂ j.1 j.2.1) * gm f z _ (w₂₃ j.2.1 j.2.2) * (gm f z _ (w₁₃ j.1 j.2.2))⁻¹ := by
    intro Z f z j hz
    simp only [u, map_mul, map_inv]
    rw [gm_res f z (l₁₂ j) hz, gm_res f z (l₂₃ j) hz, gm_res f z (l₁₃ j) hz]
  have compat : ∀ i j, ∀ z ∈ O i ⊓ O j, gm (𝟙 X) z (O i) (u i) = gm (𝟙 X) z (O j) (u j) := by
    intro i j z hz
    rw [TopologicalSpace.Opens.mem_inf] at hz
    have hzi := hz.1
    have hzj := hz.2
    rw [hu (𝟙 X) z i hzi, hu (𝟙 X) z j hzj]
    rw [mO] at hzi hzj
    have hW := mW z hzi.1
    exact cocycle_defect_eq (i₁₂ z hW.2.1 i.1 j.1 i.2.1 j.2.1 hzi.2.1 hzj.2.1 hzi.2.2.1 hzj.2.2.1)
      (i₂₃ z hW.2.2.1 i.2.1 j.2.1 i.2.2 j.2.2 hzi.2.2.1 hzj.2.2.1 hzi.2.2.2 hzj.2.2.2)
      (i₁₃ z hW.2.2.2 i.1 j.1 i.2.2 j.2.2 hzi.2.1 hzj.2.1 hzi.2.2.2 hzj.2.2.2)
  have chart : ∀ z : X, p z ∈ V → ∃ j, z ∈ O j := by
    intro z hz
    have hW := mW z hz
    obtain ⟨a', ha'⟩ := h₁.cov z hW.1.1
    obtain ⟨b', hb'⟩ := h₂.cov z hW.1.2.1
    obtain ⟨c', hc'⟩ := h₃.cov z hW.1.2.2
    exact ⟨(a', b', c'), (mO _ z).2 ⟨hz, ha', hb', hc'⟩⟩
  have hcov : p ⁻¹ᵁ V ≤ iSup O := fun z hz ↦ by
    obtain ⟨j, hj⟩ := chart z hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨ρ, hρ⟩ := glue_unit (p ⁻¹ᵁ V) O (fun j ↦ inf_le_left) hcov u compat

  let φ := RingEquiv.ofBijective (p.app V).hom (hp V)
  let v : Γ(Y, V)ˣ := Units.map φ.symm.toMonoidHom ρ
  have hv : pullU p V v = ρ := by
    apply Units.ext
    exact φ.apply_symm_apply ρ.val

  have hepy : ∀ y : Y, p (e y) = y := fun y ↦ by
    change (e ≫ p) y = y
    rw [hep]
    rfl
  have hρe : ∀ y : Y, y ∈ V → gm e y (p ⁻¹ᵁ V) ρ = 1 := by
    intro y hy
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    obtain ⟨j, hj⟩ := chart (e y) hy'
    rw [← gm_res e y (inf_le_left : O j ≤ p ⁻¹ᵁ V) hj, hρ j, hu e y j hj]
    rw [mO] at hj
    have hW := mW (e y) hj.1
    exact cocycle_defect_one (n₁₂ y j.1 j.2.1 hW.2.1 hj.2.1 hj.2.2.1) (n₂₃ y j.2.1 j.2.2 hW.2.2.1 hj.2.2.1 hj.2.2.2)
      (n₁₃ y j.1 j.2.2 hW.2.2.2 hj.2.1 hj.2.2.2)
  have hv1 : v = 1 := by
    apply unit_ext
    intro y hy
    rw [map_one]
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    have h := gm_pull e p y V hy' v
    rw [hep, hv] at h
    rw [← h]
    exact hρe y hy
  have hρ1 : ρ = 1 := by rw [← hv, hv1, map_one]

  have hxO : x ∈ O (a, b, c) := (mO _ x).2 ⟨hx, ha, hb, hc⟩
  have h := hu (𝟙 X) x (a, b, c) hxO
  rw [← hρ, hρ1, map_one, map_one] at h
  exact (mul_inv_eq_one.1 h.symm)

end GlobalTheory.PicGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_lineBundleIso_cocycle_identity : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  atlas_forward_decl GlobalTheory.PicGlue.norm_cocycle
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_glue_of_openCover_cocycle : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  first | exact @GlobalTheory.PicGlue.lb_glue | exact GlobalTheory.PicGlue.lb_glue | (intros; apply GlobalTheory.PicGlue.lb_glue <;> assumption)
end

section
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_glue_rigidified (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (hp : FnBij p)
    (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i))
    (hf : ∀ i, IsOpenImmersion (f i)) (hr : ∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) (hV : ∀ y, ∃ i, y ∈ V i)
    (hrig : ∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0)
    (hov : ∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k →
      GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) :
    ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  have hpe : ∀ y : Y, p (e y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hep]; rfl
  have hrange : ∀ i, (f i).opensRange = p ⁻¹ᵁ V i := fun i ↦ by
    ext x; exact hr i x
  choose M hM hMc using fun i ↦ cls_surj (c i)
  choose L hL hLM using fun i ↦ GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion X (X' i) (f i) (M i) (hM i)
  have hL' : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i) := fun i ↦ hrange i ▸ hL i
  have hfm : ∀ i (z : X' i), f i z ∈ p ⁻¹ᵁ V i := fun i z ↦ (hr i _).1 ⟨z, rfl⟩
  have hfl : ∀ i, ((L i).pull (f i)).IsLB := fun i ↦ GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) (f i) (hL' i) (hfm i)
  have hcl : ∀ i, cls _ (hfl i) = c i := fun i ↦ ((cls_eq_iff (hfl i) (hM i)).2 (hLM i)).trans (hMc i)
  have lifts : ∀ i (T : Scheme.{0}) (g : T ⟶ X), (∀ z, g z ∈ p ⁻¹ᵁ V i) → ∃ t : T ⟶ X' i, t ≫ f i = g :=
    fun i T g hg ↦ ⟨IsOpenImmersion.lift (f i) g (by rintro _ ⟨z, rfl⟩; exact (hr i _).2 (hg z)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hpl : ∀ i (T : Scheme.{0}) (t : T ⟶ X' i) (g : T ⟶ X), t ≫ f i = g →
      ∃ h : ((L i).pull g).IsLB, cls _ h = GlobalTheory.CechPic.pull t (c i) := by
    rintro i T t _ rfl
    have h : ((L i).pull (t ≫ f i)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) _ (hL' i) fun z ↦ by
      rw [Scheme.Hom.comp_apply]; exact hfm i _
    refine ⟨h, ?_⟩
    rw [← hcl i, ← cls_pull (hfl i) t (pull_isLB (hfl i) t)]
    exact ((cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleOnOpen_pull_comp_iso X _ _ _ (L i) (f i) t (hL' i) (hfm i))).symm
  have hR : ∀ i, ∃ r : RigD e (L i), RigOn e (L i) r := fun i ↦ by
    refine GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open X Y e (V i) (L i) (fun a y hy ↦ ?_) ?_
    · have : p (e y) ∈ V i := (hL' i).le a hy
      rwa [hpe] at this
    · obtain ⟨t, ht⟩ := lifts i _ ((V i).ι ≫ e) fun z ↦ by
        rw [Scheme.Hom.comp_apply]
        change p (e _) ∈ V i
        rw [hpe]
        exact z.2
      obtain ⟨h, hc⟩ := hpl i _ t _ ht
      exact (cls_eq_zero_iff h).1 (hc.trans (hrig i _ t _ ht))
  choose r hr' using hR
  have hw : ∀ i k, ∃ w : Cmp (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k), IsoOn (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w ∧
      Norm e (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w (r i) (r k) := fun i k ↦ by
    obtain ⟨a, ha⟩ := lifts i _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.1
    obtain ⟨b, hb⟩ := lifts k _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.2
    obtain ⟨h1, e1⟩ := hpl i _ a _ ha
    obtain ⟨h2, e2⟩ := hpl k _ b _ hb
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso X (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k)
      ((cls_eq_iff h1 h2).1 (e1.trans ((hov i k _ a b (ha.trans hb.symm)).trans e2.symm)))
    exact GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction X Y p e hep (V i ⊓ V k) _ _ (L i) (L k) w (r i) (r k) (hL' i) (hL' k)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr' i) (hr' k)
  choose w hwi hwn using hw
  obtain ⟨N, hN, hv⟩ := GlobalTheory.T.lineBundle_glue_of_openCover_cocycle X Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL' hwi
    fun i j k x a b d ha hb hd ↦ GlobalTheory.T.normalised_lineBundleIso_cocycle_identity X Y p e hep hp (V i ⊓ V j ⊓ V k) _ _ _ _ _ _ (L i) (L j) (L k)
      (w i j) (w j k) (w i k) (r i) (r j) (r k) (hL' i) (hL' j) (hL' k) (fun _ h ↦ h)
      (fun _ h ↦ ⟨⟨h.1, h.1.2, h.2⟩, h.1.1, h.2⟩) (hwi i j) (hwi j k) (hwi i k) (hwn i j) (hwn j k) (hwn i k)
      x a b d ⟨⟨(hL' i).le a ha, (hL' j).le b hb⟩, (hL' k).le d hd⟩ ha hb hd
  have hNc : ∀ i, GlobalTheory.CechPic.pull (f i) (cls N hN) = c i := fun i ↦ by
    obtain ⟨v, hv⟩ := hv i
    rw [← hcl i, ← cls_pull hN (f i) (pull_isLB hN _)]
    exact (cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen X _ _ N (L i) v (f i) hv (hfm i))
  refine ⟨cls N hN - GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.pull e (cls N hN)), ?_, fun i ↦ ?_⟩
  · rw [map_sub, ← pull_comp e p, hep, pull_id, sub_self]
  · obtain ⟨t, ht⟩ := lifts i _ ((f i ≫ p) ≫ e) fun z ↦ by
      rw [Scheme.Hom.comp_apply]
      change p (e _) ∈ V i
      rw [hpe, Scheme.Hom.comp_apply]
      exact hfm i z
    rw [map_sub, hNc, ← pull_comp (f i) p, ← pull_comp (f i ≫ p) e, ← ht, pull_comp, hNc,
      hrig i _ t _ ht, sub_zero]

end GlobalTheory.PicGlue
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_rigidified_line_bundle_classes : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i)), (∀ i, IsOpenImmersion (f i)) → (∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) → (∀ y, ∃ i, y ∈ V i) → (∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0) → (∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k → GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) → ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  atlas_forward_decl GlobalTheory.PicGlue.exists_glue_rigidified
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}}

theorem pull_pull_over {X Y Z : Over S} (u : Z ⟶ Y) (v : Y ⟶ X) (c : Pic X.left) :
    CechPic.pull u.left (CechPic.pull v.left c) = CechPic.pull (u ≫ v).left c := by
  rw [Over.comp_left, pull_comp]

def addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) : Pic (A ⊗ (A ⊗ T)).left :=
  CechPic.pull (lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)).left c

theorem pull_addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) {Z : Over S} (u : Z ⟶ A ⊗ (A ⊗ T)) :
    CechPic.pull u.left (addDefect A T c) =
      CechPic.pull (lift ((u ≫ fst _ _) * (u ≫ snd _ _ ≫ fst _ _)) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ snd _ _ ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c := by
  simp only [addDefect, map_sub, pull_pull_over, comp_lift, MonObj.comp_mul]

theorem addCls_of_locally : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 →
    (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  intro S A T _ hA c h0 hloc
  have hd : addDefect A T c = 0 := by
    refine GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A (A ⊗ T) hA _ ?_ fun p ↦ ?_
    · rw [pull_addDefect]
      have h1 : lift (1 : A ⊗ T ⟶ A) (snd A T) = snd A T ≫ lift (1 : T ⟶ A) (𝟙 T) := by
        rw [comp_lift, MonObj.comp_one, Category.comp_id]
      simp only [lift_fst, lift_snd_assoc, Category.id_comp, _root_.one_mul]
      rw [h1, ← pull_pull_over, h0, map_zero, sub_zero, sub_self]
    · obtain ⟨Z, z, hz, hp, hadd⟩ := hloc ((snd A T).left p)
      obtain ⟨ho, hr⟩ := GlobalTheory.whiskerLeft_isOpenImmersion_range S A T Z z hz
      refine ⟨A ⊗ Z, A ◁ z, ho, (hr p).2 hp, ?_⟩
      have h2 := hadd (A ⊗ (A ⊗ Z)) (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
      simp only [pull_pull_over, lift_whiskerLeft, Category.assoc] at h2
      rw [pull_addDefect]
      simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd]
      rw [h2]
      abel
  intro Z a a' t
  have h3 := pull_addDefect A T c (lift a (lift a' t))
  rw [hd, map_zero] at h3
  simp only [lift_fst, lift_snd_assoc, lift_snd] at h3
  rw [sub_sub] at h3
  exact sub_eq_zero.1 h3.symm

end GlobalTheory.PicGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_picClass_of_locally_additive : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 → (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  atlas_forward_decl GlobalTheory.PicGlue.addCls_of_locally
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
end
end
