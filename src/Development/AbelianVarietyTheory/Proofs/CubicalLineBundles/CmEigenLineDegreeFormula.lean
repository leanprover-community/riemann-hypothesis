import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriodStatement
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyExtendsOverDedekindDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamily
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegreeEigenLatticeTensorRankOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lieLattices_cmTriple_baseChange : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K'))) (_ : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) (F' : GenFib T'.pol) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K' (Fin F'.P₀.g → K')), F.IsHerm h → F'.IsHerm h' → deg h' F'.lieLat = deg h F.lieLat ∧ ∀ τ : 𝓞 E →+* 𝓞 K, deg h' (F'.eigLat T'.t.act ((RingOfIntegers.mapRingHom j).comp τ)) = deg h (F.eigLat T.t.act τ) := by
  first | exact @GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | exact GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | (intros; apply GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  first | exact @GlobalTheory.CM.exists_famLift | exact GlobalTheory.CM.exists_famLift | (intros; apply GlobalTheory.CM.exists_famLift <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_surjective_principalPairing : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  first | exact @GlobalTheory.CM.PairingIso.isIso_of_lamEq | exact GlobalTheory.CM.PairingIso.isIso_of_lamEq | (intros; apply GlobalTheory.CM.PairingIso.isIso_of_lamEq <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem OntoAt.exists_eq_comp {S : Scheme.{0}} {I : Type} {B : I → Over S} {A A' : Over S} [GrpObj A] [GrpObj A']
    {φ : ∀ i, B i ⟶ A} {k : Type} [Field k] {t : Sp k ⟶ S} (hφ : OntoAt φ t) (Φ : A' ⟶ A) [IsMonHom Φ]
    (χ : ∀ i, B i ⟶ A') (e : ∀ i, χ i ≫ Φ = φ i) (y : Over.mk t ⟶ A) : ∃ x : Over.mk t ⟶ A', y = x ≫ Φ := by
  obtain ⟨n, i, x, rfl⟩ := hφ y
  refine ⟨(List.ofFn fun m => x m ≫ χ (i m)).prod, ?_⟩
  let F : (Over.mk t ⟶ A') →* (Over.mk t ⟶ A) :=
    MonoidHom.mk' (fun z => z ≫ Φ) fun z w => MonObj.mul_comp z w Φ
  change _ = F _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext m
  simp [F, e]

theorem nonempty_isTen_of_isFam_top : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  intro hL E _ _ _ H R _ _ _ σ ω C D ε h T ψ hσ hh hpos hfam honto
  obtain ⟨T₁, ⟨t⟩, -⟩ := GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple hL E H R ω C D ε h hh hpos
  obtain ⟨Φ, hlin, htm, hlam⟩ := GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily E H R ω C D D ε h h T₁ T t ⊤ ψ
    (Submodule.topEquiv.symm : D.La ≃ₗ[𝓞 E] (⊤ : Submodule (𝓞 E) D.La)).toLinearMap 1 hh hh
    (fun a b => by rw [one_smul]; rfl) hfam
  rw [T₁.t.act.one] at hlam
  have hm : IsMonHom Φ := hlin.isMonHom
  have hsurj := (GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points R σ hσ T.t.G T₁.t.G Φ T.ab T₁.ab
    (honto.exists_eq_comp Φ (fun a => t.ten.tmul a.1) fun a => htm a.1)).1
  have hred : IsReduced (Sp R) := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hiso : IsIso Φ := GlobalTheory.T.isIso_of_surjective_principalPairing (Sp R) T₁.t.G T.t.G T₁.t.PP.L T.t.PP.L Φ T₁.ab T.ab T₁.t.PP.isLB T.t.PP.isLB hm
    T₁.ktriv hlam hsurj
  have key : ∀ a, (t.ten.ofIso (b' := Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (asIso Φ)
      ⟨hm, fun c => hlin.comm _⟩).tmul a = ψ ⟨a, trivial⟩ := fun a => htm a
  refine ⟨⟨t.ten.ofIso (asIso Φ) ⟨hm, fun c => hlin.comm _⟩, fun s a => ?_, fun a b => ?_⟩⟩
  · rw [key, key]
    exact hfam.2.2.1 s ⟨a, trivial⟩
  · rw [key, key]
    exact hfam.2.2.2 ⟨a, trivial⟩ ⟨b, trivial⟩

end GlobalTheory.CM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tensor_of_onto_full_family : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  atlas_forward_decl GlobalTheory.CM.nonempty_isTen_of_isFam_top
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homFamily_of_pureType_complex_triple : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (T : PAT H (Sp ℂ)) (r : ℕ), C.IsPrincipalAt (RingHom.id ℂ) → HasType H T.t.act (2 * ω - 1) r 0 → ∃ (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ IsFam C T h ⊤ ψ ∧ OntoAt ψ (spMap (RingHom.id ℂ)) := by
  first | exact @GlobalTheory.CM.exists_isFam_of_pureType | exact GlobalTheory.CM.exists_isFam_of_pureType | (intros; apply GlobalTheory.CM.exists_isFam_of_pureType <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Recog

theorem ontoAt_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {I : Type} {B A : Over S} {B' A' : Over S'}
    [GrpObj A] [GrpObj A'] {φ : B'.left ⟶ B.left} {χ : A'.left ⟶ A.left} (hφ : φ ≫ B.hom = B'.hom ≫ f)
    (hχ : IsGrpPullback A' A f χ) {ψ : I → (B ⟶ A)} {ψ' : I → (B' ⟶ A')}
    (hψ : ∀ i, (ψ' i).left ≫ χ = φ ≫ (ψ i).left) {k : Type} [Field k] {t' : Sp k ⟶ S'} {t : Sp k ⟶ S}
    (ht : t = t' ≫ f) (h : OntoAt (B := fun _ => B') ψ' t') : OntoAt (B := fun _ => B) ψ t := by
  intro y
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hχ t' t ht
  obtain ⟨n, i, x, hx⟩ := h (e.symm y)
  refine ⟨n, i, fun m => Over.homMk ((x m).left ≫ φ) ?_, ?_⟩
  · have hw := Over.w (x m)
    simp only [Over.mk_hom] at hw ⊢
    rw [Category.assoc, hφ, ← Category.assoc, hw, ht]
  · calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = (List.ofFn fun m => e (x m ≫ ψ' (i m))).prod := by
        rw [hx, map_list_prod, List.map_ofFn]; rfl
      _ = _ := by
        congr 1
        refine List.ofFn_inj.mpr (funext fun m => ?_)
        apply Over.OverMorphism.ext
        rw [he, Over.comp_left, Over.comp_left, Category.assoc, hψ]
        rfl

private lemma spMap_comp_moduli_spaces {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_isTen_of_hasType : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  intro hU hL hD E _ _ _ H k _ ω C T r hP hT
  have hB : Out.PolBaseChangeSt := hL.polBaseChange

  obtain ⟨Ck, φk, hCk⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C k (algebraMap (𝓞 k) k)
  obtain ⟨Tk, mk, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k) k)) T
  obtain ⟨Cc, φc, hCc⟩ := GlobalTheory.CM.exists_ellMap hB E H k _ Ck ℂ (algebraMap k ℂ)
  obtain ⟨Tc, mc, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap k ℂ)) Tk
  have hPk : Ck.IsPrincipalAt (algebraMap k ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C k _ Ck (algebraMap (𝓞 k) k) φk hCk).2.1 _ hP
  have hPc : Cc.IsPrincipalAt (RingHom.id ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H k _ Ck ℂ _ Cc (algebraMap k ℂ) φc hCc).2.1 _ (by rwa [RingHom.id_comp])
  obtain ⟨nc, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mk mc
  rw [spMap_comp_moduli_spaces] at nc
  have hinj : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k ℂ).injective.comp (IsFractionRing.injective (𝓞 k) k)
  have hTc := (GlobalTheory.CM.hasType_baseChange E H (𝓞 k) ℂ _ T.t Tc.t nc (2 * ω - 1) r 0).1 hinj hT
  have hωc : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) (2 * ω - 1) =
      2 * algebraMap k ℂ (algebraMap (𝓞 k) k ω) - 1 := by
    simp only [map_sub, map_mul, map_ofNat, map_one, RingHom.comp_apply]
  rw [hωc] at hTc

  obtain ⟨D, ε, h, ψc, hpq, hK, hpos, hFc, hOc⟩ := GlobalTheory.T.exists_homFamily_of_pureType_complex_triple hU hL E H _ Cc Tc r hPc hTc

  obtain ⟨k₁, hfin, hk, huniv⟩ := GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k _ Ck D h Tk ⊤ _ Cc φc Tc mc ψc hCc hFc
  have : FiniteDimensional ℚ k₁ := hfin
  have : NumberField k₁ := ⟨⟩
  obtain ⟨C₁, φ₁, hC₁⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C (𝓞 k₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)
  obtain ⟨T₁, m₁, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)) T
  obtain ⟨C₂, φa, hC₂⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k₁) _ C₁ k₁ (algebraMap (𝓞 k₁) k₁)
  obtain ⟨T₂, ma, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k₁) k₁)) T₁
  have hring : (algebraMap (𝓞 k₁) k₁).comp
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) =
      (IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k) := by
    ext x; rfl
  have hring' : (algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom = algebraMap k ℂ := by
    ext x; rfl
  have h21 := (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C (𝓞 k₁) _ C₁ _ φ₁ hC₁).1 k₁ _ C₂ _ φa hC₂
  rw [hring] at h21
  obtain ⟨φ₂, hφ₂, -⟩ := GlobalTheory.CM.Factor.ellMap_cancel hCk h21
  have hCc' : EllMap Cc Ck ((algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom) φc := by
    rw [hring']; exact hCc
  obtain ⟨φ₃, hφ₃, hφ₃c⟩ := GlobalTheory.CM.Factor.ellMap_cancel hφ₂ hCc'
  obtain ⟨n21, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ ma
  obtain ⟨m₂, -⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k k k₁ (RingHom.id k)
    (IntermediateField.inclusion hk).toRingHom).2 _ _ _ T.t Tk.t T₂.t mk n21
    (by rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, hring])
  obtain ⟨m₃, hm₃⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k₁ k₁ ℂ (RingHom.id k₁)
    (algebraMap k₁ ℂ)).2 _ _ _ Tk.t T₂.t Tc.t m₂ mc (by rw [spMap_comp_moduli_spaces, hring'])
  obtain ⟨ψ₂, hF₂, hψ₂⟩ := huniv k₁ hk le_rfl _ C₂ φ₂ φ₃ T₂ m₂ m₃ hφ₂ hφ₃ hφ₃c hm₃

  obtain ⟨ψ₁, hF₁, hψ₁⟩ := GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hD E H (𝓞 k₁) k₁ _ C₁ D h T₁ ⊤ _ C₂ φa T₂ ma ψ₂ hC₂ hF₂

  obtain ⟨n1, hn1⟩ := GlobalTheory.ObjMaps.exists_sab_comp ma m₃
  obtain ⟨-, ⟨-, ⟨hsq3, -⟩, -⟩, -⟩ := hφ₃
  obtain ⟨-, ⟨-, ⟨hsqa, -⟩, -⟩, -⟩ := hC₂
  have hOnto : OntoAt ψ₁ (spMap ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁))) := by
    refine ontoAt_of_isGrpPullback (φ := φ₃ ≫ φa) (χ := n1.φ) ?_ n1.cart (fun a => ?_) ?_ hOc
    · rw [Category.assoc, hsqa.w, ← Category.assoc, hsq3.w, Category.assoc]
    · rw [hn1, ← Category.assoc, hψ₂ a, Category.assoc, hψ₁ a, Category.assoc]
    · rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, RingHom.id_comp]
  have hinj₁ : Function.Injective ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k₁ ℂ).injective.comp (IsFractionRing.injective (𝓞 k₁) k₁)
  exact ⟨k₁, inferInstance, hk, _, C₁, φ₁, T₁, m₁, D, ε, h, hC₁, hpq, hK, hpos,
    GlobalTheory.T.nonempty_tensor_of_onto_full_family hL E H (𝓞 k₁) _ _ C₁ D ε h T₁ ψ₁ hinj₁ hK hpos hF₁ hOnto⟩

end GlobalTheory.CM.Recog
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_decomposition_pure_type_cm_triple : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  first | exact @GlobalTheory.CM.Recog.exists_isTen_of_hasType | exact GlobalTheory.CM.Recog.exists_isTen_of_hasType | (intros; apply GlobalTheory.CM.Recog.exists_isTen_of_hasType <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.cmCurveBaseChange_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  first | exact @GlobalTheory.CM.EllComp.ellMap_comp | exact GlobalTheory.CM.EllComp.ellMap_comp | (intros; apply GlobalTheory.CM.EllComp.ellMap_comp <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasPeriod_of_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M K : Type) [Field M] [NumberField M] [Field K] [NumberField K] (j : M →+* K) (ω : 𝓞 M) (ω' : 𝓞 K) (C : Ell H (𝓞 M) ω) (C' : Ell H (𝓞 K) ω') (φ : C'.P.A.left ⟶ C.P.A.left) (x : ℝ), EllMap C' C (RingOfIntegers.mapRingHom j) φ → C.HasPeriod x → C'.HasPeriod x := by
  intro hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx
  obtain ⟨n, hn, hmean⟩ := hx
  refine ⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.cmCurveBaseChange_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]
    have e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j)
        = (s.comp j).comp (algebraMap (𝓞 M) M) := by
      ext a; rfl
    rw [e]
    exact (hn _).2 r
  · rw [GlobalTheory.meanLog_comp]; exact hmean

end GlobalTheory.CM
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.PureDeg

theorem exists_compositum (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] :
    ∃ (k : IntermediateField ℚ ℂ) (_ : NumberField k) (j : K →+* k) (i : M →+* k),
      (∀ x, (j x : ℂ) = σ x) ∧ ∀ x, (i x : ℂ) = x := by
  let f : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  let k : IntermediateField ℚ ℂ := f.fieldRange ⊔ M
  have : FiniteDimensional ℚ f.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv
  have : FiniteDimensional ℚ k := IntermediateField.finiteDimensional_sup _ _
  have : NumberField k := NumberField.mk
  have hmem : ∀ x, σ x ∈ k := fun x => le_sup_left (a := f.fieldRange) ⟨x, rfl⟩
  refine ⟨k, inferInstance, σ.codRestrict k hmem, (IntermediateField.inclusion le_sup_right).toRingHom,
    fun x => rfl, fun x => rfl⟩

theorem mapRingHom_injective {K K' : Type} [Field K] [Field K'] (j : K →+* K') :
    Function.Injective (RingOfIntegers.mapRingHom j) := by
  intro a b h
  apply RingOfIntegers.ext
  apply j.injective
  exact congrArg (fun x : 𝓞 K' => (x : K')) h

theorem degSt : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → DegSt := by
  intro hC hU hL hX
  have hB : Out.PolBaseChangeSt := hL.polBaseChange
  intro E _ _ _ H _ χ hχ K _ _ ρ T hsp hρ htype F h hh τ hτ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
  have hρc : σ (ρ : K) ^ 2 = -(H.d : ℂ) := by
    have e := congrArg (fun a : 𝓞 K => σ (a : K)) hρ
    simpa using e
  obtain ⟨M, _, ω, C, x, hωρ, hprin, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period hC hU hL hX E H χ hχ (σ (ρ : K)) hρc
  obtain ⟨k, _, j, i, hj, hi⟩ := exists_compositum K σ M

  obtain ⟨C', φC, hCC'⟩ := exists_ellMap hB E H (𝓞 M) ω C (𝓞 k) (RingOfIntegers.mapRingHom i)
  have hCm := EllComp.ellMap_comp E H (𝓞 M) ω C (𝓞 k) _ C' (RingOfIntegers.mapRingHom i) φC hCC'
  have hemb : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)).comp (RingOfIntegers.mapRingHom i) =
      (algebraMap M ℂ).comp (algebraMap (𝓞 M) M) := RingHom.ext fun a => hi (a : M)
  have hprin' : C'.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    apply hCm.2.1
    rw [hemb]
    exact hprin
  have hper' : C'.HasPeriod x := hasPeriod_of_ellMap hB E H M k i ω _ C C' φC x hCC' hper

  obtain ⟨T', mT, -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j)) T
  have htype' : HasType H T'.t.act (RingOfIntegers.mapRingHom j ρ) 1 0 :=
    (hasType_baseChange E H (𝓞 K) (𝓞 k) (RingOfIntegers.mapRingHom j) T.t T'.t mT ρ 1 0).1
      (mapRingHom_injective j) htype
  have hinjk : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) :=
    (algebraMap k ℂ).injective.comp RingOfIntegers.coe_injective
  have hρω : RingOfIntegers.mapRingHom j ρ = 2 * RingOfIntegers.mapRingHom i ω - 1 := by
    apply hinjk
    have e1 : (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) = σ (ρ : K) := hj _
    have e2 : (((RingOfIntegers.mapRingHom i ω : 𝓞 k) : k) : ℂ) = ((ω : M) : ℂ) := hi _
    change (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) =
      (((2 * RingOfIntegers.mapRingHom i ω - 1 : 𝓞 k) : k) : ℂ)
    rw [e1]
    push_cast
    rw [e2]
    exact hωρ.symm
  obtain ⟨k₁, _, hk, ω₁, C₁, φ₁, T₁, m₁, D, ε, hD, hE1, hpq, hKF, hpos, hten⟩ :=
    GlobalTheory.T.exists_tensor_decomposition_pure_type_cm_triple hU hL hX E H k (RingOfIntegers.mapRingHom i ω) C' T' 1 hprin' (by rw [← hρω]; exact htype')
  have hper₁ : C₁.HasPeriod x :=
    hasPeriod_of_ellMap hB E H k k₁ (IntermediateField.inclusion hk).toRingHom _ ω₁ C' C₁ φ₁ x hE1 hper'
  have hsp₁ : Splits E k₁ :=
    (((splits_basic E).2.2 K).2.2 k₁ ((IntermediateField.inclusion hk).toRingHom.comp j) hsp).1

  obtain ⟨F'⟩ := GenFib.nonempty_of_baseChange hB k T'.pol
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hB k₁ T₁.pol
  obtain ⟨⟨h', hh'⟩, -⟩ := LieMetric.exists_unique_isHerm hU hL k T'.pol F'
  obtain ⟨⟨h₁, hh₁⟩, -⟩ := LieMetric.exists_unique_isHerm hU hL k₁ T₁.pol F₁

  have d1 := (GlobalTheory.T.degree_lieLattices_cmTriple_baseChange hU hL E H K k j T T' mT F F' h h' hh hh').2 τ
  have d2 := (GlobalTheory.T.degree_lieLattices_cmTriple_baseChange hU hL E H k k₁ (IntermediateField.inclusion hk).toRingHom T' T₁ m₁ F' F₁ h' h₁
    hh' hh₁).2 ((RingOfIntegers.mapRingHom j).comp τ)

  have h2 : 2 * τ H.w0 = 1 + ρ := by
    have e := congrArg τ H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, map_ofNat, hτ] at e
    exact e
  have two : (2 : 𝓞 k) ≠ 0 := two_ne_zero
  have h3 : (2 : 𝓞 k) * RingOfIntegers.mapRingHom j (τ H.w0) = 2 * RingOfIntegers.mapRingHom i ω := by
    have e := congrArg (RingOfIntegers.mapRingHom j) h2
    rw [map_mul, map_add, map_one, map_ofNat, hρω] at e
    rw [e]
    ring
  have h4 := mul_left_cancel₀ two h3
  have hw : ((RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom).comp
      ((RingOfIntegers.mapRingHom j).comp τ)) H.w0 = ω₁ := by
    simp only [RingHom.comp_apply]
    rw [h4]
    exact hE1.1
  have key := GlobalTheory.T.two_mul_degree_eigenLattice_tensor_rankOne hU hL E H k₁ ω₁ C₁ D ε hD T₁ x hsp₁ hpq hKF hpos hten hper₁ F₁ h₁ hh₁ _ hw

  have hd : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hrd : 0 < NumberField.rootDiscr E := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hr : Real.log (2 * Real.pi / √(H.d : ℝ)) + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) =
      Real.log (2 * Real.pi / NumberField.rootDiscr E) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) hrd.ne', Real.log_sqrt hd.le]
    ring
  rw [← d2.trans d1, key, logOm, ← hr]
  push_cast at hx ⊢
  linear_combination hx

end GlobalTheory.CM.PureDeg
end
end
