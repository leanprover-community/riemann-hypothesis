import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSecField

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR

theorem flat_of_injective {R K : Type} [CommRing R] [IsDomain R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) : φ.Flat := by
  have e : φ = (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  · let _ := (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).toAlgebra
    exact (inferInstance : Module.Flat (FractionRing R) K)

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_pow_one (u : LB.Sec L) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
    sval s r z J = gs r z _ (u.f (J r)) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ?_⟩
  · refine (gs_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      (gs_res (𝟙 X) y _ hy _))).symm)
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    simp
  · rw [sval_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z (le fun _ => J r) (Set.mem_iInter.2 fun _ => hJ r) _

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, map_zero, gs_eq q z ⊤ trivial, map_zero, map_zero]

theorem sval_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] {f : X ⟶ Sp R} {π : X' ⟶ X} {f' : X' ⟶ Sp R'}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) {th : H0 L 1} (hth : ∀ s : H0 L 1, ∃ a, SecIsMul f a s th)
    (h₀ : ∀ y J, Good L y J → sval th π y J = 0) (s : H0 L' 1) (y : X') {J'} (hJ' : Good L' y J') :
    sval s (𝟙 X') y J' = 0 := by
  obtain ⟨t, ht⟩ := exists_sec hL' (φ' := fun _ : PUnit => 𝟙 X') (ε' := fun _ => 1)
    (fun U _ h => by simp) s
  obtain ⟨σ, hσ⟩ := ArcPull.exists_up_sec ((isGen_iff w).1 hw) hL hL' (fun _ : PUnit => 𝟙 X') (fun _ => π)
    (fun _ => 1) (𝟙 X') (fun _ => by simp) t
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H L hL σ
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have e := hσ _ (𝟙 X') y J J' hJ hJ'
  rw [ht _ _ y J' hJ', sval_of σ _ y J (fun _ => J π) (fun _ => by rw [Category.id_comp]), Category.id_comp] at e
  have z : ∀ i, gs π y _ ((u i).f (J π)) = 0 := fun i => by
    obtain ⟨v, hv⟩ := exists_pow_one (u i)
    obtain ⟨a, ha⟩ := hth v
    rw [← hv _ π y J hJ, sval_of_secIsMul ha π y hJ, h₀ y J hJ, mul_zero]
  have e' := (hu y (J π) (hJ π)).symm.trans e
  simp only [z, mul_zero, Finset.sum_const_zero] at e'
  exact (Units.mul_right_eq_zero _).1 e'.symm

end GlobalTheory.GenSecField

namespace GlobalTheory

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.GenSecField in

theorem exists_unit_generating_section_pull : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  intro R K _ _ _ φ hφ D D' hD th th' hth hth'
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (PsiEvenPull.proj hD) hc th
  obtain ⟨c, hac⟩ := hth' a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval th (r ≫ PsiEvenPull.proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (ArcPull.om hD.w z J J' r).val * sval th' r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id, zpow_natCast,
      pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : SecIsMul D'.P.A.hom (0 : K) th' th' := secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [cst_zero', zero_mul]
      refine sval_eq_zero (flat_of_injective hφ) (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen hth
        (fun x J hJ => ?_) th' y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', sval_of_secIsMul h₀ r z hJ', cst_zero', zero_mul, zero_mul, zero_mul, mul_zero]
  · refine ⟨Units.mk0 c h, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', Units.val_mul, TauTwist.unitAt_val]
    rfl

end GlobalTheory
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_generatingSection_pullback_field : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  first | exact @GlobalTheory.exists_unit_generating_section_pull | exact GlobalTheory.exists_unit_generating_section_pull | (intros; apply GlobalTheory.exists_unit_generating_section_pull <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesPullIso
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem units_of_vF {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L z J) {u : Fˣ} (h : (u : F) = vF t r J) : stalkUnits z u = val t r z J :=
  Units.ext ((congrArg (stalkConst z) h).trans (const_vF t r hJ))
end Val

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  units_of_vF (good ν z) (ν.θ_eq x y u)

theorem stalk_σ (x : N.A) : stalkUnits z (N.σ x) = val (Z := Sp F) D.sym (ν.eA x).left z ν.J :=
  units_of_vF (good ν z) (ν.σ_eq x)

theorem const_rig : stalkConst z (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom ν.J) = (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val :=
  (const_vF _ _ (good ν z)).trans (congrArg Units.val (val_pull (good ν z) _ _ _).symm)

theorem stalk_ψ (χ : N.X) : stalkUnits z (N.ψ χ) =
    val (Z := Sp F) (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J :=
  Units.ext ((congrArg (stalkConst z) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (const_vF _ _ (good ν z)) (const_rig ν z))))

theorem stalk_th (x : N.A) : stalkConst z (N.th x) * (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val =
    sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  (congrArg _ (const_rig ν z).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))

theorem stalk_pt {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (χ : N.X) :
    stalkUnits z (c.s χ) = val (Z := Sp F) (g.s (ν.eX χ)) (𝟙 (Sp F)) z ν.J :=
  units_of_vF (good ν z) (h.2 χ)
end Num

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem injective_of_compat (hF : ArcPull.Compat φ F) : Function.Injective φ := fun a b h =>
  IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective
    ((hF a).trans ((congrArg _ (congrArg _ h)).trans (hF b).symm)))

def pushEquiv (hF : ArcPull.Compat φ F) : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
  MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hF.base) (pushF_mul _ _))
    ⟨pushF_injective (pull_grp hD) hF.base, pushF_surjective (pull_grp hD) hF.base⟩

theorem exists_iso_of_th (hG : GlobalFnsSt) (hF : ArcPull.Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') (z : Sp F) (lam : ((Sp F).presheaf.stalk z)ˣ)
    (hth : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (lam * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J) :
    ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  have hJ := good ν z
  have hJ' := good ν' z
  let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left
  obtain ⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹ :=
    ⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x) :=
    ⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩
  obtain ⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y) :=
    ⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩
  have hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ) := ν'.c_eq
  have a₁ : ∀ χ, jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm
  have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).symm
  have rig : val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J :=
    (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans
      (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)
  refine ⟨{
    φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e
    h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩
  · apply (stalkUnits z).injective
    rw [hh, map_one, map_one, mul_inv_cancel]
  · apply (stalkUnits z).injective
    have k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y))
        (pushF (pull_grp hD) hF.base (ν'.eA u)) =
        Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ *
          (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y) * Ω (ν'.eA u) * (Ω 1)⁻¹ *
          thS D' z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u) :=
      thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _
    simp only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J =
        Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J :=
      PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'
    simp only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkConst z).injective
    have k := stalk_th ν z (Φ x)
    have k' := stalk_th ν' z x
    rw [hΦ, rig] at k
    have k₁ := k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))
    rw [map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]
    refine (Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)
    have := (Ω 1).inv_mul
    simp only [Units.val_mul]
    linear_combination (-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) *
      (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this
  · apply ν.eA.injective
    rw [hΦ, ν.c_eq, he, hc]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J =
        (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J :=
      (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ *
        val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J) (a₁ _))
    rw [map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply ν.eA.injective
    refine hg.1.trans (Eq.trans ?_ (hΦ _).symm)
    rw [hg'.1]
    exact Over.OverMorphism.ext H.1.symm
  · apply (stalkUnits z).injective
    have k₀ := pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at k₀
    have k : val (Z := Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J =
        (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ *
          val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀
    show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)
    rw [map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_values_iso : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  intro hG R K _ _ _ φ D D' hD F _ _ _ hF N N' ν ν'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_generatingSection_pullback_field R K φ (injective_of_compat hF) D D' hD ν.th ν'.th ν.th_gen ν'.th_gen
  let z : Sp F := IsLocalRing.closedPoint F
  refine exists_iso_of_th hD hG hF ν ν' z (TauTwist.unitAt (Z := Sp F) (TF (R := K) F).hom z c) fun x => ?_
  have := hc (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  exact this.trans (congrArg (fun q => (TauTwist.unitAt (Z := Sp F) q z c * om hD.w z ν.J ν'.J x.left).val *
    sval (Z := Sp F) ν'.th x.left z ν'.J) (Over.w x))

end GlobalTheory.ValuesPullIso
end
end
