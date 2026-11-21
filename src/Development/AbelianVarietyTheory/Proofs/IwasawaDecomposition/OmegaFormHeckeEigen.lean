import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

open AlgebraicGeometry CategoryTheory in

theorem GlobalTheory.OneMapRef.exists_scalar_of_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y') (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ th th', A.Reads 1 y.s th → A'.Reads 1 y'.s th' → ∃ lam : ℂ, lam ≠ 0 ∧ th' = lam • th ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L hs hx hL hA y y' A A' mk hmk hm hm' th th' hr hr'
  have he := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm'
  have hfr := GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL he
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have hu : y'.u = y.u := funext fun τ => funext fun i => by
    have d := A'.der ⟨τ, i⟩
    simp only [he] at d
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique d (A.der ⟨τ, i⟩)
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hyx hu
  subst hyx hu
  obtain ⟨a, ha⟩ := GlobalTheory.Frames.ChgOf.gen_unit' y.s s' y.gen gen'
  refine ⟨a, a.ne_zero, ?_, fun w n f hf => ?_⟩
  · refine (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L _ A' hs hx hL 1 s').1.unique hr' ?_
    intro j z pt h1 h2 hj
    rw [he] at h1 hj
    have h3 := hr j z pt h1 h2 hj
    have h4 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1
      a (fun _ => j) pt h2
    refine ((congrArg (Geo.Tor.valAt' pt _) (ha fun _ => j)).trans h4).trans ?_
    rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact congrArg _ h3
  · let t : Formalism.L2.Pj.Ix Dw → ℂˣ := fun i => match i with
      | none => a
      | some _ => 1
    refine (GlobalTheory.LamT.evR_frChg_tri (inferInstance) hf t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) (y := y)
      (y' := ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩)
      ⟨rfl, ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c ℂ y y y).1).2.1,
        (GlobalTheory.Frames.ChgOf.secBC_id_iff y.x _ y.s s').2 ha⟩).trans ?_
    congr 1
    simp [wchar, Fintype.prod_option, t, Formalism.L2.Pj.ex]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mulVec_congr {A : Type} [CommRing A] {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) A) {x y w : Fin n → A}
    (e : x - Q *ᵥ y = N • w) : P *ᵥ x - (P * Q) *ᵥ y = N • P *ᵥ w := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e, Matrix.mulVec_smul]

theorem latW_rfl {D : D7} {W : HSp D} (L : Lt D.host.E W.rank) : latW (T := W) rfl L = L := rfl

section

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {h : GA D W}

theorem markAd_rfl (l : Level H) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) :
    MarkAd (T := W) rfl l ι h mk ↔ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
      finVec W (mk a) - (finHom W h).1 *ᵥ (finVec W (ι a)) = l.M • w := Iff.rfl

theorem finVec_add' (a b : Fin W.rank → D.host.E) : finVec W (a + b) = finVec W a + finVec W b :=
  GlobalTheory.AdLat.cap_fv_add D.host.F a b

theorem finVec_nsmul' (n : ℕ) (a : Fin W.rank → D.host.E) : finVec W (n • a) = n • finVec W a :=
  GlobalTheory.AdLat.cap_fv_nsmul D.host.F n a

theorem finVec_sub' (a b : Fin W.rank → D.host.E) : finVec W (a - b) = finVec W a - finVec W b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

theorem markOver_of_markAd {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hI : Mfr l₂ ≤ Mfr l)
    {mk mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} (h1 : MarkAd (T := W) rfl l ι h mk)
    (h2 : MarkAd (T := W) rfl l₂ ι h mk₂) : MarkOver l l₂ (latG W h) mk mk₂ := by
  intro a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨c, hc⟩ := hM
  obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 h1 a (Submodule.smul_mono_left hI ha)
  obtain ⟨w', hw', e'⟩ := (markAd_rfl l₂ mk₂).1 h2 a ha
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w)
    ((finVec_sub' _ _).trans (GlobalTheory.AdMark.sub_congr hc e e'))
  refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W h).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
  rw [← eu]
  abel

theorem finHom_mulVec_finVec {δ : GA D W} {ga : GL (Fin W.rank) D.host.E}
    (hδ : Formalism.L2.Theta.mt W δ = (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
    (v : Fin W.rank → D.host.E) : (finHom W δ).1 *ᵥ finVec W v = finVec W (ga.1 *ᵥ v) := by
  funext i
  have hf : ∀ i j, (finHom W δ).1 i j = (1 : Af D.host.F) ⊗ₜ ga.1 i j := fun i j => by
    have he' : (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ ga.1 i j := congrFun (congrFun hδ i) j
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    rfl
  simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    TensorProduct.tmul_sum]

theorem mem_latGHat_mul (δ : GA D W) (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom W δ).1 *ᵥ z ∈ latGHat W (δ * h) ↔ z ∈ latGHat W h := by
  rw [(GlobalTheory.MarkCoset.latG_spec D W h).2, (GlobalTheory.MarkCoset.latG_spec D W (δ * h)).2]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg (fun v => ((finHom W δ)⁻¹).1 *ᵥ v) e
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.inv_mul_cancel_left] at this
  exact this

end

theorem markAd_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (h : GA D W) (L : Lt D.host.E r), latW hr L = latG W h → ∀ l : Level H, (∃ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) ∧ MarkAd hr l ι h mk) ∧ ∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) → MarkAd hr l ι h mk → IsMark l L mk ∧ (∀ mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) → MarkAd hr l ι h mk') ∧ (∀ l₂ : Level H, l.M ∣ l₂.M → Mfr l₂ ≤ Mfr l → ∀ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk₂ a ∈ L) → MarkAd hr l₂ ι h mk₂ → MarkOver l l₂ L mk mk₂) ∧ ∀ (δ : GA D W) (ga : GL (Fin r) D.host.E), Formalism.L2.Theta.mt W δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) → latW hr (mapL ga L) = latG W (δ * h) ∧ MarkAd hr l ι (δ * h) (mvMap ga mk) := by
  intro D H Dw W r hr ι hι h L hL l
  subst hr
  rw [latW_rfl] at hL
  subst hL
  obtain ⟨mk₀, hm0, ha0, -⟩ := GlobalTheory.AdMark.exists_marking D H Dw l l W _ rfl ι hι dvd_rfl le_rfl h
  rw [GlobalTheory.AdMark.latR_rfl] at hm0
  replace ha0 : MarkAd (T := W) rfl l ι h mk₀ := ha0
  refine ⟨⟨mk₀, hm0.mem, ha0⟩, fun mk hmem hmk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have ho := markOver_of_markAd dvd_rfl le_rfl hmk ha0
    refine ⟨hmem, ?_, fun v hv => ?_⟩
    · rintro a ha ⟨u, hu, e⟩
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact hm0.inj a ha ⟨u + u', add_mem hu hu', by rw [e', e, smul_add]⟩
    · obtain ⟨a, ha, u, hu, e⟩ := hm0.surj v hv
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact ⟨a, ha, u' + u, add_mem hu' hu, by rw [e, e', smul_add, add_assoc]⟩
  · intro mk' hc
    refine (markAd_rfl l mk').2 fun a ha => ?_
    obtain ⟨u, hu, e⟩ := hc a ha
    obtain ⟨w, hw, e'⟩ := (markAd_rfl l mk).1 hmk a ha
    refine ⟨w + finVec W u, add_mem hw (((GlobalTheory.MarkCoset.latG_spec D W h).1 u).1 hu), ?_⟩
    rw [e, finVec_add', finVec_nsmul', smul_add, ← e']
    abel
  · intro l₂ hM hI mk₂ _ h2
    exact markOver_of_markAd hM hI hmk h2
  · intro δ ga hδ
    have hf := finHom_mulVec_finVec (δ := δ) (ga := ga) hδ
    constructor
    · rw [latW_rfl]
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).2 ?_
        change finVec W (ga.1 *ᵥ x) ∈ _
        rw [← hf, mem_latGHat_mul]
        exact ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).1 hx
      · intro hv
        have hri : ga.1 *ᵥ ((ga⁻¹).1 *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        refine ⟨(ga⁻¹).1 *ᵥ v, ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).2 ?_, hri⟩
        rw [← mem_latGHat_mul δ, hf, hri]
        exact ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).1 hv
    · refine (markAd_rfl l _).2 fun a ha => ?_
      obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 hmk a ha
      refine ⟨_, (mem_latGHat_mul δ w).2 hw, ?_⟩
      change finVec W (ga.1 *ᵥ mk a) - _ = _
      rw [← hf, map_mul, Units.val_mul]
      exact mulVec_congr _ _ e

end GlobalTheory.OneMapRef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Equivar

open CategoryTheory MonObj in

theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

variable {D : D7} {S T : HSp D} {r g g' : ℕ}

theorem latW_injective (hr : T.rank = r) : Function.Injective (latW (D := D) (T := T) hr) := by
  subst hr
  intro L L' h
  ext v
  exact SetLike.ext_iff.1 h v

theorem sameSp_of_isSet {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} (h : IsSet ψ θ S T hr X eT bas) (h' : IsSet ψ θ S T hr X' eT' bas')
    (hp : X'.p0 = X.p0) : SameSp X' X := by
  obtain ⟨-, -, -, -, hm, hk, he, -⟩ := h
  obtain ⟨-, -, -, -, hm', hk', he', -⟩ := h'
  refine ⟨?_, hm'.1.trans hm.1.symm, hp, hm'.2.trans hm.2.symm, hk'.trans hk.symm⟩
  ext τ
  constructor
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT'.surjective ⟨τ, hτ⟩
    have : τ = (eT ρ).1 := by rw [he, ← he', hρ]
    exact this ▸ (eT ρ).2
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT.surjective ⟨τ, hτ⟩
    have : τ = (eT' ρ).1 := by rw [he', ← he, hρ]
    exact this ▸ (eT' ρ).2

theorem symm_eq_of_isSet {X X' : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ}
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) (he' : ∀ ρ, (eT' ρ).1 = tauE D ρ) (τ : D.host.E →+* ℂ) (h : τ ∈ X.Ψ)
    (h' : τ ∈ X'.Ψ) : eT'.symm ⟨τ, h'⟩ = eT.symm ⟨τ, h⟩ := by
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [he', ← he, Equiv.apply_symm_apply]

theorem exists_real_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (h : IsSet ψ θ S T hr X eT bas)
    (idx : Fin g ≃ X.Ψ × Fin r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {L : Lt D.host.E r} {th : (Fin g → ℂ) → ℂ}
    (hm : MeanOne X bas idx x L th) : ∃ w : WO S T, Ker.IsRealPt w ∧
      Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) * ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b) ≠ 0 := by
  obtain ⟨-, hθ, -, hev, -, -, -, hs⟩ := h
  obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨_, _, -, -, h3⟩ := hm
    simp [hc] at h3
  have hq : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  obtain ⟨⟨Lz, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws _ r X g _ hq bas idx S.rank hs hev x hx
  obtain ⟨v, hv⟩ := Lz.surjective fun _ => z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hw : rePt θ hr eT (Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a) : WO S T) = v := by
    funext τ k a
    have := hσ.comp (fun ρ => v (eT ρ) k (Fin.cast hr (Fin.cast hr.symm a))) (eT.symm τ)
    refine this.trans ?_
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a), Matrix.ext fun a k => hσ.fin _, ?_⟩
  rw [hw, ← hL, hv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun _ _ => hz)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem compare {σ : c.F →+* ℂ} (hA : l.A = 1) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : LatEmb T ι) {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {e' : Fin g' ≃ Lt1 Dw} (hS : IsSet ψ θ S T hr X eT bas) (hS' : IsSet ψ θ S T hr X' eT' bas')
    (hM : Matched c σ X idx e) (hM' : Matched c σ X' idx' e') (hp : X'.p0 = X.p0) (hD : SelfD X X.Λ)
    (hD' : SelfD X' X'.Λ) {δ a' : GA D T} (hδ : δ ∈ GQ T) (hL : latW hr X.Λ = latG T (δ * a'))
    (hL' : latW hr X'.Λ = latG T a') {Z : Fam T} (hZ : IsONeg T X.p0 Z) {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}
    (hx : x ∈ X.dom) (hx' : x' ∈ X'.dom) (ex : x = frOf hr eT (mvZ θ (δ * a') Z)) (ex' : x' = frOf hr eT' (mvZ θ a' Z)) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x X.Λ y) (A' : AnFib X' bas' idx' e' x' X'.Λ y')
      (th : (Fin g → ℂ) → ℂ) (th' : (Fin g' → ℂ) → ℂ), A.Reads 1 y.s th → A'.Reads 1 y'.s th' →
      ∀ mk mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ X.Λ) → (∀ a, mk' a ∈ X'.Λ) →
      MarkAd hr l ι (δ * a') mk → MarkAd hr l ι a' mk' → A.Marked mk → A'.Marked mk' →
      ∃ lam : ℂ, (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y) ∧
        ∀ w : WO S T, Ker.IsRealPt w → ∃ w' : WO S T, Ker.IsRealPt w' ∧
          Ker.gaussR X' bas' idx' x' (Ker.zR X' idx' x' (rePt θ hr eT' w')) *
              ∏ b, th' (Ker.zR X' idx' x' (rePt θ hr eT' w') b) =
            lam ^ S.rank * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b)) ∧
          ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
            IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → om (1, δ * a') f w = om (1, a') f w' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' A A' th th' hth hth' mk mk' hmk hmk' hm hm' hAm hAm'
  have hX : SameSp X' X := sameSp_of_isSet hS hS' hp
  have hsy := symm_eq_of_isSet hS.2.2.2.2.2.2.1 hS'.2.2.2.2.2.2.1
  obtain ⟨ga, g1, g2, g3, g4, g5⟩ := GlobalTheory.OneMapRef.RatPt.rational_points D S T r g hr ψ θ X eT bas idx hS δ hδ
  obtain ⟨k1, k2⟩ := ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι a' X'.Λ hL' l).2 mk' hmk' hm').2.2.2 δ ga g1
  have eL : mapL ga X'.Λ = X.Λ := latW_injective hr (k1.trans hL.symm)
  have eX : lact ga (castFr hX.psi x') = x := by
    have : castFr hX.psi x' = frOf hr eT (mvZ θ a' Z) := by
      rw [ex']
      funext τ a b
      simp only [castFr, frOf]
      rw [hsy τ.1 τ.2]
    rw [this, g3, ex, ((GlobalTheory.OneMapRef.oneg_frames D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 a').2.2.1 δ]
  have key := GlobalTheory.OneMapRef.anFib_move_renum D H Dw l Xo c σ r g g' X' X hX bas' idx' e' bas idx e hS'.2.2.2.2.2.2.2
    hS.2.2.2.2.2.2.2 hM' hM x' hx' X'.Λ hD' ga g2 y' A' th' hth'
  rw [eL, eX] at key
  obtain ⟨A₁, th₁, r1, r2, r3⟩ := key
  have hmem : ∀ a, mvMap ga mk' a ∈ X.Λ := fun a => eL ▸ ⟨mk' a, hmk' a, rfl⟩
  obtain ⟨m1, -, m3, -⟩ := (GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmem k2
  obtain ⟨lam, -, l2, l3⟩ := GlobalTheory.OneMapRef.exists_scalar_of_marked _ H Dw l Xo c r g X bas idx e x X.Λ hS.2.2.2.2.2.2.2 hx hD
    hA y y' A A₁ mk ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmk hm).1 hAm
    (marked_congr A₁ (r2 mk' hAm') (m3 l dvd_rfl le_rfl mk hmk hm)) th th₁ hth r1
  refine ⟨lam, l3, fun w hw => ?_⟩
  obtain ⟨w', hw', rfl⟩ := (g4 w).1 hw
  refine ⟨w', hw', ?_, fun χS χT om ho f hf => ?_⟩
  · rw [← r3 S.rank (rePt θ hr eT' w') (rePt θ hr eT (actO S T 1 δ w')), l2]
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    · intro τ k
      rw [(g4 w').2]
      congr 1
      funext a
      simp only [rePt]
      rw [hsy τ.1 (hX.psi ▸ τ.2) τ.2]
  · have : ((1, δ * a') : GA D S × GA D T) = (1, δ) * (1, a') := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply]
    exact g5 χS χT om ho _ (ho.om_pres _ _ hf) w'

theorem rdU_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (hx : x ∈ (U.X k).dom) : rdU U f k x = @evR _ _ _ _ _ _ _ Xo c f ℂ _ σ.toAlgebra (ptC U k ⟨x, hx⟩) :=
  dif_pos hx

end GlobalTheory.OneMapRef.Equivar
end
