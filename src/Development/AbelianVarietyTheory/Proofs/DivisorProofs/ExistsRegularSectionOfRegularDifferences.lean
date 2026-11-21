import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

open GlobalTheory.AbLaw in

theorem cech_one_cocycle_split : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  intro X U hU K W hW hc f hf
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB X
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU K W hW hc
    (fun a b => (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).symm (f a b)) (by
      intro a b d O ha hb hd
      apply (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).injective
      have h : rs X inf_le_left (f a b) + rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W a ⊓ W b ⊓ W d ≤ W a ⊓ W d) (f a d) := hf a b d
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) h
      simp only [map_add, rs_rs] at h
      rw [map_add, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]
      simpa only [LinearEquiv.apply_symm_apply] using h)
  refine ⟨fun a => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  atlas_forward_decl GlobalTheory.CechPer.cech_one_cocycle_split
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_section_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ →
    (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ,
    ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  intro A _ g L u hA K W h hcov hreg U
  obtain ⟨-, -, -, -, hinf, -, -, -, hres, he, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hres' : ∀ (V V' : A.left.Opens) (hle : V' ≤ V) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V',
      val u.ex V' ((A.left.presheaf.map (homOfLE hle).op).hom b) z = val u.ex V b z :=
    fun V V' hle b z hz ↦ hres V V' hle b z hz
  have vsub : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b - c) z = val u.ex V b z - val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_sub e (show Sec (str A) V from b) c
  have vadd : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b + c) z = val u.ex V b z + val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_add e (show Sec (str A) V from b) c
  have vneg : ∀ (V : A.left.Opens) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (-b) z = - val u.ex V b z := by
    intro V b z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he']
    exact map_neg e (show Sec (str A) V from b)
  choose b hb using hreg
  have hle : ∀ i j, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ≤ W i ⊓ W j :=
    fun i j ↦ inf_le_inf inf_le_right inf_le_right
  let f : ∀ i j, Γ(A.left, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := fun i j ↦
    (A.left.presheaf.map (homOfLE (hle i j)).op).hom (b i j)
  have hf : ∀ i j, ∀ z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)), val u.ex _ (f i j) z = h i z - h j z := by
    intro i j z hz
    rw [hres' _ _ (hle i j) (b i j) z hz]
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := (hinf _ _).symm ▸ (by
      rw [hinf, hinf, hinf] at hz
      exact ⟨hz.1.2, hz.2.2⟩)
    rw [← hb i j z hz']
    rfl
  have hcoc : ∀ i j k, (A.left.presheaf.map (homOfLE (inf_le_left : (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j))).op).hom (f i j) +
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k))).op).hom (f j k) =
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W i) ⊓ (U.1 ⊓ W k))).op).hom (f i k) := by
    intro i j k
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA _ _ fun z hz ↦ ?_
    have hz3 := hz
    rw [hinf, hinf, hinf, hinf, hinf] at hz3
    rw [vsub _ _ _ z hz, vadd _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz,
      hf i j z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.1.2.1, hz3.1.2.2⟩),
      hf j k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.2.1, hz3.1.2.2⟩, hz3.2.1, hz3.2.2⟩),
      hf i k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.2.1, hz3.2.2⟩)]
    ring
  have hcov' : U.1 ≤ ⨆ i, U.1 ⊓ W i := by
    rw [← inf_iSup_eq, hcov, inf_top_eq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary A.left U.1 U.2 K (fun i ↦ U.1 ⊓ W i) (fun i ↦ inf_le_left) hcov' f hcoc
  have key : ∀ i j z, z ∈ pre u.ex (U.1 ⊓ W i) → z ∈ pre u.ex (U.1 ⊓ W j) →
      h i z - val u.ex _ (a i) z = h j z - val u.ex _ (a j) z := by
    intro i j z hi hj
    have hz : z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := by rw [hinf]; exact ⟨hi, hj⟩
    have h1 := hf i j z hz
    rw [ha i j, vsub _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz] at h1
    linear_combination -h1
  classical
  refine ⟨fun z ↦ if hz : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) then
      h hz.choose z - val u.ex _ (a hz.choose) z else 0, fun i ↦ ⟨-(a i), fun z hz ↦ ?_⟩⟩
  have hex : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) := ⟨i, hz⟩
  simp only [Pi.sub_apply, dif_pos hex]
  rw [key _ i z hex.choose_spec hz, vneg _ _ z hz]
  ring

end GlobalTheory.CechPer
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_section_of_regular_differences : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ, ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  atlas_forward_decl GlobalTheory.CechPer.exists_section_of_isReg_sub
end
