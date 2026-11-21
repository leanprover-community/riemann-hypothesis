import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpaceStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrEqvEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}

theorem perpX (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) :
    ∀ x ∈ F.X, H.B x v = 0 := by
  have h : F.X ≤ LinearMap.ker (H.B.flip v) := by
    rw [FlagD.X, FlagD.Xa, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  intro x hx
  simpa using h hx

theorem map_mem {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : x ∈ F.X) :
    γ x ∈ G.X := by
  have h : F.X.map (γ : V →ₗ[K] V) = G.X := by
    simp only [FlagD.X, FlagD.Xa, Submodule.map_span, Set.image_image, hG, LinearEquiv.coe_coe]
  rw [← h]
  exact Submodule.mem_map_of_mem hx

theorem mem_of_map {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : γ x ∈ G.X) :
    x ∈ F.X := by
  have h := map_mem (F := G) (G := F) (γ := γ.symm)
    (fun a => by rw [hG a, LinearEquiv.symm_apply_apply]) hx
  rwa [LinearEquiv.symm_apply_apply] at h

theorem B_mod {S : Submodule K V} {u u' y y' : V} (hu : ∀ x ∈ S, H.B x u = 0) (hy' : ∀ x ∈ S, H.B x y' = 0)
    (h : y - u ∈ S) (h' : y' - u' ∈ S) : H.B y y' = H.B u u' := by
  have h1 : H.B (y - u) y' = 0 := hy' _ h
  have h2 : H.B (y' - u') u = 0 := hu _ h'
  have h3 : H.B u (y' - u') = 0 := by rw [← H.herm, h2, star_zero]
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
  rw [map_sub, sub_eq_zero] at h3
  rw [h1, h3]

end GlobalTheory.DegAsm.IndIsom

namespace GlobalTheory.DegAsm
open IndIsom
private lemma sup_iff_lemma {K V : Type} [Field K] [AddCommGroup V] [Module K V] {R : Type} [CommRing R]
    [Algebra R K] [Module R V] [IsScalarTower R K V] (M : Submodule R V) (S : Submodule K V) {a b : V}
    (h : a - b ∈ S) : a ∈ M ⊔ S.restrictScalars R ↔ b ∈ M ⊔ S.restrictScalars R := by
  have h' : a - b ∈ M ⊔ S.restrictScalars R := Submodule.mem_sup_right h
  constructor
  · intro ha
    simpa using sub_mem ha h'
  · intro hb
    simpa using add_mem hb h'

theorem exists_isH : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hCM r F G 𝔡 N γ hE hAd hγ hG
  classical
  obtain ⟨-, hXF, hXG, hV0, -⟩ := adapt_invariants K V H hCM r F G 𝔡 N hAd
  obtain ⟨hfull, -⟩ := NF.geometry K V H hCM r N
  obtain ⟨-, -, -, -, -, hIF, hIG, -, hexG⟩ := hfull
  simp only [II, hXF, hXG, hV0] at hIF hIG hexG
  have hW : ∀ y, y ∈ wSp F G ↔ ∀ v ∈ V0 F G, H.B v y = 0 := fun y =>
    GlobalTheory.DegCnt.NFGeom.mem_perp' (H := H) (V0 F G) y
  have hFV0 : F.X ≤ V0 F G := le_sup_left.trans le_sup_left
  have hGV0 : G.X ≤ V0 F G := le_sup_right.trans le_sup_left
  have hzF : F.z ∈ V0 F G := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have feV0 : ∀ a : Fin (r + 1), F.e a ∈ V0 F G := by
    intro a
    induction a using Fin.lastCases with
    | last => exact hzF
    | cast b => exact hFV0 (Submodule.subset_span ⟨b, b.isLt, rfl⟩)
  have hA : ∀ x ∈ F.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ G.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIF x hx).1 hv)).2
  have hB : ∀ x ∈ G.X, (∀ v ∈ V0 F G, H.B v x = 0) → x ∈ F.X := fun x hx hv =>
    (Submodule.mem_inf.mp ((hIG x hx).1 hv)).1
  have hSG : SameGr G N.F' := hAd.2.2
  have hC : ∀ w, (∀ a, H.B (G.e a) w = 0) → ∃ x ∈ G.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0 := by
    intro w hw
    apply hexG
    intro a
    have h1 : N.F'.e a - G.e a ∈ G.X := AdaptInv.xa_mono G (Nat.lt_succ_iff.mp a.isLt) (hSG a)
    have h2 := perpX G hw _ h1
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at h2
    exact h2
  have hEperp : ∀ u : W, ∀ a, H.B (F.e a) (e u) = 0 := fun u =>
    (hE.2 (e u)).2 (Submodule.mem_sup_left (LinearMap.mem_range_self e u))
  have hEX : ∀ u : W, ∀ x ∈ F.X, H.B x (e u) = 0 := fun u => perpX F (hEperp u)
  have hγB := (mem_isomGrp H γ).1 hγ
  have hγperp : ∀ u : W, ∀ a, H.B (G.e a) (γ (e u)) = 0 := fun u a => by
    rw [hG a, hγB]; exact hEperp u a
  have hγX : ∀ u : W, ∀ x ∈ G.X, H.B x (γ (e u)) = 0 := fun u => perpX G (hγperp u)
  have heX : ∀ u : W, e u ∈ F.X → u = 0 := by
    intro u hu
    apply HW.nondeg u
    intro u'
    rw [← hE.1]
    exact hEX u' _ hu
  have hex : ∀ w : W, ∃ u : W, ∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X := by
    intro w
    obtain ⟨x, hxG, hx⟩ := hC (γ (e w)) (hγperp w)
    have hy : γ (e w) - x ∈ wSp F G := (hW _).2 hx
    have hyF : ∀ a, H.B (F.e a) (γ (e w) - x) = 0 := fun a => hx _ (feV0 a)
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ((hE.2 _).1 hyF)
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy1
    refine ⟨u, γ (e w) - x, hy, ?_, ?_⟩
    · rw [← hyz]; simpa using hz
    · simpa using neg_mem hxG
  have huniq : ∀ w u₁ u₂, (∃ y ∈ wSp F G, y - e u₁ ∈ F.X ∧ y - γ (e w) ∈ G.X) →
      (∃ y ∈ wSp F G, y - e u₂ ∈ F.X ∧ y - γ (e w) ∈ G.X) → u₁ = u₂ := by
    rintro w u₁ u₂ ⟨y₁, hy₁, hF₁, hG₁⟩ ⟨y₂, hy₂, hF₂, hG₂⟩
    have hdG : y₁ - y₂ ∈ G.X := by
      convert sub_mem hG₁ hG₂ using 1; abel
    have hdF : y₁ - y₂ ∈ F.X := hB _ hdG ((hW _).1 (sub_mem hy₁ hy₂))
    have he : e (u₁ - u₂) ∈ F.X := by
      convert add_mem (sub_mem hdF hF₁) hF₂ using 1
      rw [map_sub]; abel
    exact sub_eq_zero.mp (heX _ he)
  choose f hf using hex
  have hchar : ∀ w u, (∃ y ∈ wSp F G, y - e u ∈ F.X ∧ y - γ (e w) ∈ G.X) → f w = u :=
    fun w u hu => huniq w _ _ (hf w) hu
  have hadd : ∀ w₁ w₂, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    apply hchar
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_, ?_⟩
    · convert add_mem hF₁ hF₂ using 1; rw [map_add]; abel
    · convert add_mem hG₁ hG₂ using 1; rw [map_add, map_add]; abel
  have hsmul : ∀ (c : K) (w : W), f (c • w) = c • f w := by
    intro c w
    apply hchar
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_, ?_⟩
    · convert Submodule.smul_mem _ c hF using 1; rw [map_smul, smul_sub]
    · convert Submodule.smul_mem _ c hGG using 1; rw [map_smul, map_smul, smul_sub]
  let fl : W →ₗ[K] W :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c w => by rw [RingHom.id_apply]; exact hsmul c w }
  have hiso : ∀ w₁ w₂, HW.B (f w₁) (f w₂) = HW.B w₁ w₂ := by
    intro w₁ w₂
    obtain ⟨y₁, hy₁, hF₁, hG₁⟩ := hf w₁
    obtain ⟨y₂, hy₂, hF₂, hG₂⟩ := hf w₂
    rw [← hE.1, ← hE.1]
    have e₁ : H.B y₁ y₂ = H.B (e (f w₁)) (e (f w₂)) :=
      B_mod (S := F.X) (hEX (f w₁)) (fun x hx => (hW y₂).1 hy₂ x (hFV0 hx)) hF₁ hF₂
    have e₂ : H.B y₁ y₂ = H.B (γ (e w₁)) (γ (e w₂)) :=
      B_mod (S := G.X) (hγX w₁) (fun x hx => (hW y₂).1 hy₂ x (hGV0 hx)) hG₁ hG₂
    rw [← e₁, e₂, hγB]
  have hinj : Function.Injective fl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply HW.nondeg w
    intro w'
    have hw0 : f w = 0 := hw
    rw [← hiso w w', hw0, map_zero, LinearMap.zero_apply]
  set h := LinearEquiv.ofInjectiveEndo fl hinj with hh
  have hcoe : ∀ w, h w = f w := fun w => by
    rw [hh, LinearEquiv.coe_ofInjectiveEndo]; rfl
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · rw [mem_isomGrp]
    intro x y
    rw [hcoe, hcoe, hiso]
  · intro w
    rw [hcoe]
    exact hf w
  · intro h' hh'
    ext w
    rw [hcoe]
    exact (hchar w (h' w) (hh' w)).symm
  · intro g Λ'
    ext u
    obtain ⟨w, rfl⟩ : ∃ w, h w = u := ⟨h.symm u, h.apply_symm_apply u⟩
    obtain ⟨y, hy, hF, hGG⟩ := hf w
    rw [← hcoe] at hF
    have hR : h w ∈ imLat h (lat0 F e Λ') ↔ e w ∈ Λ' ⊔ rs (𝓞 K) F.X := by
      simp only [imLat, Formalism.HermitianLatticesTheory.gmap, lat0, Submodule.mem_map, Submodule.mem_comap,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨w', hw', hww⟩
        rwa [h.injective hww] at hw'
      · intro hw
        exact ⟨w, hw, rfl⟩
    have hL : h w ∈ (datOf F G e g (γ • Λ')).1 ↔
        e (h w) ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X := Iff.rfl
    rw [hL, hR, ← sup_iff_lemma _ _ hF]
    have hV0c : V0 G F = V0 F G := by
      simp only [V0]
      rw [sup_comm G.X F.X, Set.pair_comm]
    have hWc : ∀ v, v ∈ wSp G F ↔ v ∈ wSp F G := fun v => by
      simp only [wSp, hV0c]
    have hS2 : y ∈ flagPairDefinitePartLattice G F (γ • Λ') ⊔ rs (𝓞 K) F.X ↔ y ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := by
      constructor
      · intro hy'
        obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hy'
        have hl1 : l ∈ γ • Λ' ⊔ rs (𝓞 K) G.X := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hl).1).2
        have hl2 : l ∈ wSp F G := (hWc l).1 (Submodule.mem_inf.mp hl).2
        have hx' : x ∈ G.X := by
          have hxy : x = y - l := by rw [← hlx]; abel
          apply hA x hx
          rw [hxy]
          exact (hW _).1 (sub_mem hy hl2)
        rw [← hlx]
        exact add_mem hl1 (Submodule.mem_sup_right hx')
      · intro hy'
        apply Submodule.mem_sup_left
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, hy'⟩, (hWc y).2 hy⟩
        show y ∈ uPerp G F
        rw [uPerp, GlobalTheory.DegCnt.NFGeom.mem_perp']
        intro x hx
        apply (hW y).1 hy
        exact sup_le hGV0 hFV0 hx
    rw [hS2, sup_iff_lemma _ _ hGG]
    constructor
    · intro h1
      obtain ⟨m, hm, x, hx, hmx⟩ := Submodule.mem_sup.mp h1
      obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
      rw [LinearEquiv.smul_def] at hmx
      have hx' : γ (e w - l) ∈ G.X := by
        rw [map_sub, ← hmx]; simpa using hx
      have : e w - l ∈ F.X := IndIsom.mem_of_map hG hx'
      have hsum : e w = l + (e w - l) := by abel
      rw [hsum]
      exact add_mem (Submodule.mem_sup_left hl) (Submodule.mem_sup_right this)
    · intro h1
      obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp h1
      rw [← hlx, map_add]
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (IndIsom.map_mem hG hx))
      rw [← LinearEquiv.smul_def]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hl

end GlobalTheory.DegAsm
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (γ : V ≃ₗ[K] V), IsEmb F HW e → Adapt F G 𝔡 N → γ ∈ isomGrp H → (∀ a, G.e a = γ (F.e a)) → ∃ h : W ≃ₗ[K] W, h ∈ isomGrp HW ∧ IsH F G e γ h ∧ (∀ h' : W ≃ₗ[K] W, IsH F G e γ h' → h' = h) ∧ ∀ (g : ℕ) (Λ' : Submodule (𝓞 K) V), (datOf F G e g (γ • Λ')).1 = imLat h (lat0 F e Λ') := by
  atlas_forward_decl GlobalTheory.DegAsm.exists_isH
end

section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.TermPair
open GlobalTheory.ModIdent GlobalTheory.DegAsm.AdaptInv
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

theorem perp_lift [FiniteDimensional K V] {F G : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (hU : IsUnimod H Λ) (h : IsAdm G F Λ (g : 𝓞 K)) {l : V} (hl : l ∈ Λ) (hp : ∀ x ∈ G.X, H.B x l = 0) :
    ∃ m ∈ Λ, l - (g : K) • m ∈ perp H F.X := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) F.X), IsIntegral ℤ ((g : K)⁻¹ * H.B x l) := by
    rintro ⟨x, hxΛ, hxS⟩
    obtain ⟨x', -, h1, h2⟩ := h (Fin.last r) 0 x hxΛ (by
      rw [zero_smul, sub_zero]; exact hxS)
    obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 h2
    rw [zero_smul, sub_zero] at h1
    have a1 := hp x' h1
    have a5 : H.B (x' - x) l = g * H.B n l := by rw [hxn]; simp
    obtain ⟨c, hc⟩ := integral_of_unimod hU hn hl
    have : (g : K)⁻¹ * H.B x l = ((-c : 𝓞 K) : K) := by
      rw [inv_mul_eq_iff_eq_mul₀ hg0]
      change _ = (g : K) * (-(c : K))
      rw [hc]
      simp only [map_sub, LinearMap.sub_apply] at a5
      linear_combination a1 - a5
    show IsIntegral ℤ ((g : K)⁻¹ * H.B x l)
    rw [this]
    exact (-c).isIntegral_coe
  let φ : ↥(Λ ⊓ rs (𝓞 K) F.X) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨(g : K)⁻¹ * H.B x l, hdiv x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B ((a : V) + b) l = (g : K)⁻¹ * H.B a l + (g : K)⁻¹ * H.B b l
        simp [mul_add]
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B (a • (b : V)) l = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l)
        rw [← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨m, hm, hφ⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU F.X φ
  refine ⟨m, hm, (mem_perp_iff H _ _).2 fun u hu => orth_symm ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem ((isLatMod_top_bot_iff Λ).1 hU.1) u
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : algebraMap (𝓞 K) K s • u ∈ Λ := by rw [algebraMap_smul]; exact hs
  have e : H.B (algebraMap (𝓞 K) K s • u) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • u) l :=
    hφ ⟨_, hs', F.X.smul_mem _ hu⟩
  rw [eq_inv_mul_iff_mul_eq₀ hg0] at e
  apply mul_left_cancel₀ hs0
  simp only [map_sub, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
    smul_eq_mul] at e ⊢
  linear_combination -e

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_X_iff {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hγ : ∀ a, G.e a = γ (F.e a)) (x : V) :
    γ x ∈ G.X ↔ x ∈ F.X := by
  have : G.X = F.X.map (γ : V →ₗ[K] V) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [hγ]
    rfl
  rw [this, Submodule.mem_map_equiv]
  simp

omit [NumberField K] [StarRing K] in
theorem mem_smul_iff (γ : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) : γ x ∈ γ • Λ ↔ x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := γ.injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

omit [NumberField K] in

theorem mem_graph {F G : FlagD H r} {HW : HermSpace K W} {e : W →ₗ[K] V} (he : IsEmb F HW e)
    (hI : ∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X)
    (hlift : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0)
    {γ : V ≃ₗ[K] V} {h : W ≃ₗ[K] W} (hγ : ∀ a, G.e a = γ (F.e a)) (hh : IsH F G e γ h) (g : ℕ)
    (Λ' : Submodule (𝓞 K) V) (w v : W) :
    (h w, v) ∈ (datOf F G e g (γ • Λ')).2 ↔
      ∃ x ∈ Λ', ∃ m ∈ γ • Λ', e w - x ∈ F.X ∧ e v - (γ x + (g : K) • m) ∈ F.X := by
  obtain ⟨y, hy, hy1, hy2⟩ := hh w
  have hy' : ∀ u ∈ V0 F G, H.B y u = 0 := (mem_perp_iff H _ _).1 hy
  constructor
  · intro hm
    have hm' : (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X) := hm
    obtain ⟨⟨a, b⟩, hab, ⟨s, t⟩, ⟨hs, ht⟩, hst⟩ := Submodule.mem_sup.1 hm'
    obtain ⟨e1, e2⟩ := Prod.mk.inj hst
    have hs : s ∈ F.X := hs
    have ht : t ∈ F.X := ht
    obtain ⟨ha, -, l, hl, m, hm, h1, h2⟩ := (mem_iota F G _ g a b).1 hab
    have ha' := ((mem_perp_lattice_flag_iff G F _ a).1 ha).1
    rw [jointSpan_comm] at ha'
    have k1 : y - a ∈ G.X := by
      refine hI _ ?_ fun u hu => by simp [hy' u hu, ha' u hu]
      have := F.X.add_mem hy1 hs
      rw [← e1] at this
      convert this using 1; abel
    refine ⟨γ.symm l, by rw [← mem_smul_iff γ]; simpa using hl, m, hm, ?_, ?_⟩
    · rw [← mem_X_iff hγ, map_sub, LinearEquiv.apply_symm_apply]
      have := G.X.sub_mem (G.X.add_mem k1 h1) hy2
      convert this using 1; abel
    · rw [LinearEquiv.apply_symm_apply, ← e2]
      have := F.X.add_mem h2 ht
      convert this using 1; abel
  · rintro ⟨x, hx, m, hm, h1, h2⟩
    have hx' := (mem_smul_iff γ Λ' x).2 hx
    obtain ⟨s, hs, hb⟩ := hlift (e v) ((he.2 _).2 (Submodule.mem_sup_left ⟨v, rfl⟩))
    have k1 : y - γ x ∈ G.X := by
      have := G.X.add_mem hy2 ((mem_X_iff hγ _).2 h1)
      rw [map_sub] at this
      convert this using 1; abel
    have k2 : e v - s - (γ x + (g : K) • m) ∈ F.X := by
      have := F.X.sub_mem h2 hs
      convert this using 1; abel
    show (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)
    refine Submodule.mem_sup.2 ⟨(y, e v - s), (mem_iota F G _ g _ _).2 ⟨?_, ?_, γ x, hx', m, hm, k1, k2⟩,
      (-(y - e (h w)), s), ⟨F.X.neg_mem hy1, hs⟩, by simp⟩
    · exact (mem_perp_lattice_flag_iff G F _ _).2 ⟨by rw [jointSpan_comm]; exact hy', _, hx', k1⟩
    · exact (mem_perp_lattice_flag_iff F G _ _).2 ⟨fun u hu => orth_symm (hb u hu), _,
        Submodule.add_mem _ hx' (gsmul_mem g hm), k2⟩

theorem geom [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (hN : Adapt F G 𝔡 N) :
    (∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X) ∧
    (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0) := by
  obtain ⟨-, h, h'⟩ := hN
  obtain ⟨-, -, -, h1, -, -, -, hl, -⟩ := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1
  rw [sitesCommonSpace_v0_eq_Vp h h'] at h1 hl
  rw [x_eq h] at hl
  refine ⟨fun v hv hw => ?_, fun w hw => hl w fun a => ?_⟩
  · have := ((h1 v (isotropicSpan_le_jointSpan_left F G hv)).1 hw).2
    rwa [x_eq h'] at this
  · have k : N.F.e a - F.e a ∈ F.X := xa_mono F (Nat.le_of_lt_succ a.2) (h a)
    have := orth_of_mem_X F (fun b => hw b.castSucc) k
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at this
    exact this

end GlobalTheory.DegAsm.TermPair

namespace GlobalTheory.DegAsm
open GlobalTheory.ModIdent TermPair

theorem trip_of_terms : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N N' : NF H r) (g : ℕ) (Λ Λ' : Submodule (𝓞 K) V) (γ γ' : V ≃ₗ[K] V) (h h' : W ≃ₗ[K] W), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → Adapt F G' 𝔡 N' → N.IsTerm g Λ → N'.IsTerm g Λ → γ ∈ isomGrp H → γ' ∈ isomGrp H → (∀ a, G.e a = γ (F.e a) ∧ G'.e a = γ' (F.e a)) → γ • Λ' = Λ → γ' • Λ' = Λ → IsH F G e γ h → IsH F G' e γ' h' → (∀ x ∈ Λ ⊓ rs (𝓞 K) (perp H F.X), γ' (γ.symm x) - x ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)) → (datOf F G e g Λ, datOf F G' e g Λ, h * h'⁻¹) ∈ Trip HW g (lat0 F e Λ) r (N.gI g Λ) (N'.gI g Λ) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N N' g Λ Λ' γ γ' h h' hg he hN hN' hT hT' hγ hγ' hE
    hΛ hΛ' hh hh' hβ
  obtain ⟨k, hk, -, hku, hkl⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G 𝔡 N γ he hN hγ fun a => (hE a).1
  obtain ⟨k', hk', -, hku', hkl'⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G' 𝔡 N' γ' he hN' hγ' fun a => (hE a).2
  obtain rfl := hku h hh
  obtain rfl := hku' h' hh'
  have d1 := hkl g Λ'
  have d2 := hkl' g Λ'
  rw [hΛ] at d1
  rw [hΛ'] at d2
  obtain ⟨⟨hU, hF, hG⟩, hA⟩ :=
    ((adapt_invariants K V H hK r F G 𝔡 N hN).2.2.2.2.2.2.2.2 g Λ).1.1 hT
  have hA' : IsAdm G F Λ (g : 𝓞 K) := by
    refine isAdm_symm (fun a => ?_) hA
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [hF.2, hG.2]
    · rw [hF.1, hG.1]
  have key : ∀ w : W, ∀ x ∈ Λ', e w - x ∈ F.X → ∃ n ∈ Λ, γ' x - γ x - (g : K) • n ∈ F.X := by
    intro w x hx hw
    have hxΛ : γ x ∈ Λ := hΛ ▸ (mem_smul_iff γ Λ' x).2 hx
    have hp : ∀ u ∈ G.X, H.B u (γ x) = 0 := by
      intro u hu
      obtain ⟨u, rfl⟩ := γ.surjective u
      rw [mem_X_iff fun a => (hE a).1] at hu
      rw [(mem_isomGrp H γ).1 hγ]
      have a1 := X_iso F hu hw
      have a2 := orth_of_mem_X F (fun b => (he.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) b.castSucc) hu
      rw [map_sub, a2] at a1
      simpa using a1
    obtain ⟨m, hm, hmp⟩ := perp_lift hg hU hA' hxΛ hp
    obtain ⟨s, hs, t, ⟨-, ht⟩, hst⟩ := Submodule.mem_sup.1 (hβ _ ⟨Λ.sub_mem hxΛ (gsmul_mem g hm), hmp⟩)
    obtain ⟨n, hn, rfl⟩ := (mem_smulLat g Λ s).1 hs
    have hm' : γ' (γ.symm m) ∈ Λ := by
      rw [← hΛ', mem_smul_iff, ← mem_smul_iff γ, hΛ]
      simpa using hm
    refine ⟨n + γ' (γ.symm m) - m, Λ.sub_mem (Λ.add_mem hn hm') hm, ?_⟩
    have ht : t ∈ F.X := ht
    convert ht using 1
    simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply] at hst
    rw [smul_sub, smul_add, eq_sub_of_add_eq' hst]
    abel
  refine ⟨(GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G 𝔡 N g Λ hg he hN hT).1,
    (GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G' 𝔡 N' g Λ hg he hN' hT').1, mul_mem hk (inv_mem hk'), ?_, fun y v => ?_⟩
  · show imLat (h * h'⁻¹) (datOf F G' e g Λ).1 = (datOf F G e g Λ).1
    rw [d1, d2]
    unfold imLat
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
  · obtain ⟨w, rfl⟩ := h'.surjective y
    have e1 := mem_graph he (geom hK hN).1 (geom hK hN).2 (fun a => (hE a).1) hh g Λ' w v
    have e2 := mem_graph he (geom hK hN').1 (geom hK hN').2 (fun a => (hE a).2) hh' g Λ' w v
    rw [hΛ] at e1
    rw [hΛ'] at e2
    have e3 : (h * h'⁻¹) (h' w) = h w := by simp
    show (h' w, v) ∈ (datOf F G' e g Λ).2 ↔ ((h * h'⁻¹) (h' w), v) ∈ (datOf F G e g Λ).2
    rw [e3, e1, e2]
    constructor
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m + n, Λ.add_mem hm hn, h1, ?_⟩
      have := F.X.add_mem h2 h3
      convert this using 1
      rw [smul_add]; abel
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m - n, Λ.sub_mem hm hn, h1, ?_⟩
      have := F.X.sub_mem h2 h3
      convert this using 1
      rw [smul_sub]; abel

end GlobalTheory.DegAsm
end

section
section
open scoped ENNReal Classical

namespace GlobalTheory

theorem sum_fibre_two_index_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc

end GlobalTheory
end

open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_fibre_two_index_encard_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  atlas_forward_decl GlobalTheory.sum_fibre_two_index_bound
end

section
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_pairs_le_classes_pf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)),
    (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) →
    (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) →
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  intro D large₂ X Y u hS W HW he Λ h hh Sf hSf hη
  obtain ⟨hK, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hlam : ∀ p ∈ Sf, p.2.lam = Λ ∧ p.2.lam' = p.1.lam' := by
    intro p hp
    obtain ⟨hl, hl', -⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, (hSf p hp).1.2.2⟩
    exact ⟨hl.symm.trans (hSf p hp).2, hl'.symm⟩
  have hL : ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) =
      ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (clsOm Y u Λ (frCls Λ p.1) * clsOm Y u Λ (frCls Λ p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [clsOm_frCls hK Λ p.1 (hSf p hp).2, clsOm_frCls hK Λ p.2 (hlam p hp).1]
  rw [hL]
  generalize hT1 : Sf.image (fun p => frCls Λ p.1) = T₁
  generalize hT2 : Sf.image (fun p => frCls Λ p.2) = T₂
  refine GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (GTu Y u) _ Sf (frCls Λ)
    (fun t => wRow D (X.Fu u) t.lam') (clsOm Y u Λ) T₁ T₂ ?_ (clsOm_nonneg Y u Λ hK) ?_ ?_ ?_
  · intro t
    show 0 ≤ wRow D (X.Fu u) t.lam'
    unfold wRow; positivity
  · intro p hp
    subst hT1 hT2
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  · intro p hp q hq h1 hc
    have hrel2 : p.2 ∈ relSet Y u := (hSf p hp).1.2.1
    have hrelq : q.2 ∈ relSet Y u := (hSf q hq).1.2.1
    have hhe : h p.2 = h q.2 := by
      have e := hη p hp q hq
      rw [h1] at e
      have e2 := congrArg (fun g => (h q.1)⁻¹ * g) e
      simp only [inv_mul_cancel_left] at e2
      exact inv_injective e2
    have hfe := (frCls_eq_iff hK Λ p.2 q.2).1 hc
    have hl : p.2.lam = q.2.lam := ((hlam p hp).1).trans ((hlam q hq).1).symm
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS p.2 hrel2
    have hfe' : GlobalTheory.DegAsm.FrEqv (F0 X u) p.2.lam (Ft p.2) (Ft q.2) := by rw [(hlam p hp).1]; exact hfe
    have := GlobalTheory.T.term_determined_by_frameClass_and_isometry D large₂ X Y u hS W HW he p.2 q.2 ⟨N, hN⟩ hl hfe' (h p.2) (hh p.2 hrel2)
      (by rw [hhe]; exact hh q.2 hrelq)
    exact Prod.ext h1 this
  · intro b
    have gen : ∀ s : Finset (GTu Y u), (∀ t ∈ s, t.lam = Λ ∧ frCls Λ t = b) →
        ∑ a ∈ s, wRow D (X.Fu u) a.lam' ≤ 1 := by
      intro s hmem
      rcases s.eq_empty_or_nonempty with he0 | ⟨t₀, ht₀⟩
      · rw [he0, Finset.sum_empty]; exact zero_le_one
      obtain ⟨hl0, hb0⟩ := hmem t₀ ht₀
      have hrel : ∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t) := by
        intro t ht
        obtain ⟨hl, hb⟩ := hmem t ht
        refine ⟨hl0.trans hl.symm, ?_⟩
        rw [hl0]
        exact (frCls_eq_iff hK Λ t₀ t).1 (hb0.trans hb.symm)
      have hw : ∀ t ∈ s, wRow D (X.Fu u) t.lam' = wRow D (X.Fu u) t₀.lam' := by
        intro t ht
        obtain ⟨hl, hf⟩ := hrel t ht
        rw [(GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hS t₀ t hl hf).1]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      exact GlobalTheory.T.frameClass_termCount_le_card_aut D large₂ X Y u hS t₀ s hrel
    refine gen _ fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_image] at ht
    obtain ⟨⟨p, hp, rfl⟩, ht2⟩ := ht
    exact ⟨(hSf p hp).2, ht2⟩

end GlobalTheory.TypeAsm.PerRow
end

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)), (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)), (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) → (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) → ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤ (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  atlas_forward_decl GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf
end

section
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_clsOm_le_datBd : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  intro D large₂ X Y u hStd W HW he Λ j x δ d N A hA hT
  obtain ⟨hK, -, -, -, hf, -, -, -, -, -, hV, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hgS : 1 ≤ gS D := by omega
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨-, -, hj0, hδ0, hAd0, hTm0, hg0, -⟩ := hT t₀ ht₀
  obtain ⟨-, -, hLDel, hLDb, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t₀ (N t₀) hAd0
  obtain ⟨-, hx1, -, -, hfW⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t₀)
    (dI D) (N t₀) (gS D) Λ hgS he hAd0 hTm0
  obtain ⟨-, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS (N t₀) (gS D) Λ hgS hTm0
  rw [hg0] at hx1
  rw [hLDel, hj0, hδ0] at hDel1
  rw [hLDb, hj0, hδ0] at hDb1
  let G : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) → Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := fun b =>
    if hb : ∃ t ∈ A, frCls Λ t = b then Ft hb.choose else F0 X u
  have hGb : ∀ b ∈ A.image (frCls Λ), ∃ t ∈ A, frCls Λ t = b ∧ G b = Ft t := by
    intro b hb
    have hb' : ∃ t ∈ A, frCls Λ t = b := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hb'.choose_spec
    exact ⟨hb'.choose, h1, h2, by simp only [G, dif_pos hb']⟩
  have key := GlobalTheory.DegAsm.sum_weights_per_datum D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (dI D)
    (gS D) j (Tu D u) x (fun l => star (δ l)) Λ d (k2Del D j δ) (DbL D j δ) (Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS))
    (A.image (frCls Λ)) G hgS hx1 hDel1 hDb1 he ?_ ?_ ?_
  · have hsum : ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b =
        ∑ b ∈ A.image (frCls Λ), GlobalTheory.DegAsm.omI (F0 X u) (G b) (dI D) Λ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨t, ht, hbt, hG⟩ := hGb b hb
      obtain ⟨-, hlt, -⟩ := hT t ht
      rw [hG, ← hbt, clsOm_frCls hK Λ t hlt]
      unfold omT
      rw [hlt]
    rw [hsum]
    refine key.trans (le_of_eq ?_)
    rw [show Module.finrank D.host.E W = D.R.k by omega, hf]
    rfl
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, hTmt, hgt, -⟩ := hT t ht
    obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨N t, ?_, hTmt, a1.trans hjt, a2, ?_, ?_, hgt⟩
    · rw [hG]; exact hAdt
    · rw [a3, hjt, hδt]
    · rw [a4, hjt, hδt]
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, -, -, hdt⟩ := hT t ht
    obtain ⟨-, -, -, -, a5⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨?_, ?_⟩
    · rw [hG, ← hjt, a5, hδt]
    · rw [hG]; exact hdt
  · intro b hb b' hb' hE
    obtain ⟨t, -, hbt, hG⟩ := hGb b hb
    obtain ⟨t', -, hbt', hG'⟩ := hGb b' hb'
    rw [hG, hG'] at hE
    rw [← hbt, ← hbt']
    exact (frCls_eq_iff hK Λ t t').2 hE

end GlobalTheory.TypeAsm.PerRow
end

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_frameClassWeights_le_datumBound : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  atlas_forward_decl GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd
end

section
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_le_encard_fibres {α Θ : Type} (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ)
    (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ) (hf : ∀ a ∈ S, 0 ≤ f a)
    (hR : ∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a))
    (hB : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) :
    ENNReal.ofReal (∑ a ∈ S, f a) ≤
      ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) :=
  GlobalTheory.T.sum_fibre_two_index_encard_bound α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB

theorem sum_pairs_le_classes (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W))
    (hh : ∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) (Sf : Finset (GTu Y u × GTu Y u))
    (hSf : ∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ)
    (hη : ∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) :
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
  GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses D large₂ X Y u hS W HW he Λ h hh Sf hSf hη

theorem sum_classes_le (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E)
    (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS)
    (A : Finset (GTu Y u)) (hne : A.Nonempty)
    (hA : ∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧
      (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) :
    ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x :=
  GlobalTheory.T.sum_frameClassWeights_le_datumBound D large₂ X Y u hS W HW he Λ j x δ d N A hne hA

theorem termData (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (t : GTu Y u) (ht : t ∈ relSet Y u) :
    ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
  obtain ⟨N, hA, hj, hT⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS t ht
  have hterm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hS t N hA
  obtain ⟨-, -, hDel, hDb, hlab⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hS t N hA
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨-, hx1, hxD, -, hdim⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t)
    (dI D) N (gS D) t.lam hg he hA hterm
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS N (gS D) t.lam hg hterm
  have hiso : t.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => t.rep.2.2.1 x y
  obtain ⟨h, hh, hH, -, -⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t) (dI D) N
    t.lin he hA hiso (fun a => GlobalTheory.TypeAsm.FibProof.Ft_e t a)
  exact ⟨N, h, hA, hterm, hj, hT, hDel, hDb, hDel1, hDb1, hx1, hxD, hlab, hh, hH, by omega⟩

theorem pairTrip (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (p : GTu Y u × GTu Y u) (hp : p ∈ (Y.tO u u).allPairs (relSet Y u))
    (N₁ N₂ : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h₁ h₂ : W ≃ₗ[D.host.E] W) (hA₁ : AdT p.1 N₁) (hA₂ : AdT p.2 N₂)
    (ht₁ : N₁.IsTerm (gS D) p.1.lam) (ht₂ : N₂.IsTerm (gS D) p.2.lam)
    (hH₁ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.1) W.subtype p.1.lin h₁)
    (hH₂ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.2) W.subtype p.2.lin h₂) :
    p.1.lam = p.2.lam ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) p.1.lam,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) p.1.lam, h₁ * h₂⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype p.1.lam) D.R.rS (N₁.gI (gS D) p.1.lam)
          (N₂.gI (gS D) p.1.lam) := by
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨hl, hl', hc⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, hp.2.2⟩
  refine ⟨hl, ?_⟩
  have hi₁ : p.1.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.1.rep.2.2.1 x y
  have hi₂ : p.2.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.2.rep.2.2.1 x y
  have hΛ₁ : p.1.lin • p.1.lam' = p.1.lam := by
    rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.1.rep.2.2.2.1
  have hΛ₂ : p.2.lin • p.1.lam' = p.1.lam := by
    rw [hl, hl', ← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.2.rep.2.2.2.1
  rw [← hl] at ht₂
  exact GlobalTheory.DegAsm.trip_of_terms D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft p.1) (Ft p.2) (dI D)
    N₁ N₂ (gS D) p.1.lam p.1.lam' p.1.lin p.2.lin h₁ h₂ hg he hA₁ hA₂ ht₁ ht₂ hi₁ hi₂
    (fun a => ⟨GlobalTheory.TypeAsm.FibProof.Ft_e p.1 a, GlobalTheory.TypeAsm.FibProof.Ft_e p.2 a⟩) hΛ₁ hΛ₂ hH₁ hH₂ hc

end GlobalTheory.TypeAsm.PerRow

namespace GlobalTheory.TypeAsm
open PerRow

theorem perRowC : PerRowC := by
  intro D large₂ X Y u hS W HW he Λ j' j'' δ' δ'' S hS'
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N₀, h₀, -⟩ := termData D large₂ X Y u hS W HW he p₀.1 (hS' p₀ hp₀).1.1
  have hdata : ∀ t : GTu Y u, ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), t ∈ relSet Y u →
      AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
    intro t
    by_cases ht : t ∈ relSet Y u
    · obtain ⟨N, h, hp⟩ := termData D large₂ X Y u hS W HW he t ht
      exact ⟨N, h, fun _ => hp⟩
    · exact ⟨N₀, h₀, fun h => absurd h ht⟩
  choose N h hNh using hdata

  have hpair : ∀ p ∈ S, p.2.lam = Λ ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS ((N p.1).gI (gS D) Λ)
          ((N p.2).gI (gS D) Λ) ∧
      (N p.1).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊ ∧ (N p.2).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊ := by
    intro p hp
    obtain ⟨hpa, hl, hj1, hj2, hd1, hd2⟩ := hS' p hp
    obtain ⟨a1, a2, -, -, a5, -, -, -, a9, a10, -, -, a13, -⟩ := hNh p.1 hpa.1
    obtain ⟨b1, b2, -, -, b5, -, -, -, b9, b10, -, -, b13, -⟩ := hNh p.2 hpa.2.1
    obtain ⟨hl2, htr⟩ := pairTrip D large₂ X Y u hS W HW he p hpa (N p.1) (N p.2) (h p.1) (h p.2) a1 b1 a2 b2 a13 b13
    rw [hl] at htr hl2 a9 a10
    rw [← hl2] at b9 b10
    refine ⟨hl2.symm, htr, Finset.mem_Icc.2 ⟨a9, Nat.le_floor ?_⟩, Finset.mem_Icc.2 ⟨b9, Nat.le_floor ?_⟩⟩
    · rw [← hj1, ← hd1, ← a5]; exact a10
    · rw [← hj2, ← hd2, ← b5]; exact b10
  refine sum_le_encard_fibres S (fun p => (N p.1).gI (gS D) Λ) (fun p => (N p.2).gI (gS D) Λ)
    (fun p => (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹))
    (fun x y => GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x y)
    (fun p => wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2))
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x)
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x) _ _ ?_
    (fun p hp => ⟨(hpair p hp).2.2.1, (hpair p hp).2.2.2, (hpair p hp).2.1⟩) ?_
  · intro p _
    have hw : 0 ≤ wRow D (X.Fu u) p.1.lam' := by unfold wRow; positivity
    have ho : ∀ t : GTu Y u, 0 ≤ omT t := fun t =>
      ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
    exact mul_nonneg hw (mul_nonneg (ho _) (ho _))
  · intro a ha
    have key : ∀ Sf : Finset (GTu Y u × GTu Y u), (∀ q ∈ Sf, q ∈ S ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.1) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ ∧
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.2) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ ∧ h q.1 * (h q.2)⁻¹ = h a.1 * (h a.2)⁻¹ ∧
        (N q.1).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧ (N q.2).gI (gS D) Λ = (N a.2).gI (gS D) Λ) → a ∈ Sf →
        ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) ((N a.1).gI (gS D) Λ) *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) ((N a.2).gI (gS D) Λ) := by
      intro Sf hmem haf
      have h1 := sum_pairs_le_classes D large₂ X Y u hS W HW he Λ h (fun t ht => (hNh t ht).2.2.2.2.2.2.2.2.2.2.2.2.1) Sf
        (fun p hp => ⟨(hS' p (hmem p hp).1).1, (hS' p (hmem p hp).1).2.1⟩)
        (fun p hp q hq => ((hmem p hp).2.2.2.1).trans ((hmem q hq).2.2.2.1).symm)
      have hA1 : ∀ t ∈ Sf.image Prod.fst, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j' ∧ labT t = δ' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, c1, -, -, c4, -⟩ := hmem q hq
        obtain ⟨hpa, hl, hj1, -, hd1, -⟩ := hS' q hqS
        obtain ⟨a1, a2, -⟩ := hNh q.1 hpa.1
        rw [hl] at a2
        exact ⟨hpa.1, hl, hj1, hd1, a1, a2, c4, c1⟩
      have hA2 : ∀ t ∈ Sf.image Prod.snd, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j'' ∧ labT t = δ'' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.2).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, -, c2, -, -, c5⟩ := hmem q hq
        obtain ⟨hpa, -, -, hj2, -, hd2⟩ := hS' q hqS
        have hl2 := (hpair q hqS).1
        obtain ⟨b1, b2, -⟩ := hNh q.2 hpa.2.1
        rw [hl2] at b2
        exact ⟨hpa.2.1, hl2, hj2, hd2, b1, b2, c5, c2⟩
      have h2 := sum_classes_le D large₂ X Y u hS W HW he Λ j' _ δ' _ N (Sf.image Prod.fst) ⟨a.1, Finset.mem_image_of_mem _ haf⟩ hA1
      have h3 := sum_classes_le D large₂ X Y u hS W HW he Λ j'' _ δ'' _ N (Sf.image Prod.snd) ⟨a.2, Finset.mem_image_of_mem _ haf⟩ hA2
      rw [Finset.image_image] at h2 h3
      have n2 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      have n1 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      exact h1.trans (mul_le_mul h2 h3 n2 (n1.trans h2))

    rw [Finset.filter_congr_decidable]
    refine key _ (fun q hq => ?_) (Finset.mem_filter.2 ⟨ha, rfl, rfl, rfl⟩)
    obtain ⟨hqS, he1, he2, he3⟩ := Finset.mem_filter.1 hq
    obtain ⟨c1, c2⟩ := Prod.mk.inj he1
    obtain ⟨c2, c3⟩ := Prod.mk.inj c2
    exact ⟨hqS, c1, c2, c3, he2, he3⟩

end GlobalTheory.TypeAsm
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  atlas_forward_decl GlobalTheory.TypeAsm.perRowC
end
