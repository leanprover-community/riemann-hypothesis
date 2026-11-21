import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsIsoPairOfEq
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsSemiAbelianIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent

set_option maxHeartbeats 3200000 in

theorem hasArcData_descends : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  intro hL h2 h3 h4 h5 h6 hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ y hy t m P hT V _ _ _ hV g hg hI
    _ _ hA
  letI := H.starRing
  obtain ⟨hV₁, hV₂, -⟩ := hV
  have hV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV₂⟩
  have := hR.1
  have := hR.2.2.1
  obtain ⟨t', m₀, P', hD, bc, mbc, hPU, hm₀, xl, el⟩ :=
    exists_pelUnif_pull h3.cubePull hL.polBaseChange h4.unifBaseChange h5 hR hV t P g hg hI
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨W₁⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨W, rfl, k₁, k₂⟩ := WitnessMove.exists_wit h4.unifBaseChange h5 h6.unifUniq (qkPullExists hL.globalFns) hV W₁
    t' m' P'
  obtain rfl : m' = W.m := (eq_of_heq k₁).symm
  obtain rfl : P' = W.P := (eq_of_heq k₂).symm
  have hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ := by rw [hm', hm₀]
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have gD := pull_grp hD
  obtain ⟨φ, gφ, hφ, wφ⟩ := exists_desc_pol hL h2 hH f hg a.D₀.P P.D.toPre.P W.P.D.toPre.P gD s1 ⟨hD.w, hD.w_gen⟩
    ⟨W.w, s2⟩ (fun F _ _ i₁ i₂ => agree hL h2 h5 hR hV hf hg y hy m P hT W hD bc mbc hPU hm xl el F i₁ i₂)
  have he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A := (cubeMapOf gφ).e_comm
  obtain ⟨w, gw, rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A P.D.toPre.P.A φ he
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩ ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ wφ
  have pw := (isGen_iff w).1 gw
  have pD := (isGen_iff hD.w).1 hD.w_gen
  obtain ⟨w', T⟩ := exists_comp P.D.toPre.P.isLB w hD.w pw pD a.D₀.P.isLB W.P.D.toPre.P.isLB
  have tr : ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
      {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
      (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel w' s s₀ x ↔ GenRel W.w s s₀ x := by
    have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he a.D₀.P.L) (fun _ => rfl)).1 rw'
    have r₂ := T.pmaps_comp P.D.toPre.P.isLB (fun _ => hD.he) r₀ (pmaps_rig' hD)
    rw [← spMap_comp] at r₂
    have g' := (isGen_iff w').2 (T.pgen_comp P.D.toPre.P.isLB pw pD)
    have key : ∀ (ψ : W.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left) (v : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ψ)), ψ = W.φ →
        v.IsGen → PMaps v (K := PUnit) (fun _ => eSec W.P.D.toPre.P.A) (fun _ => eSec a.D₀.P.A) (fun _ => 1)
          W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) →
        ∀ {F : Type} [Field F] {K : Type} [Fintype K] {pt : K → (Sp F ⟶ W.P.D.toPre.P.A.left)}
          {pt₀ : K → (Sp F ⟶ a.D₀.P.A.left)} {ε : K → ℤ} (s : LB.Gen (LB.LinComb W.P.D.toPre.P.L pt ε))
          (s₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ ε)) (x : F), GenRel v s s₀ x ↔ GenRel W.w s s₀ x := by
      rintro _ v rfl gv pv F _ K _ pt pt₀ ε s s₀ x
      rw [rigidified_iso_unique hL.globalFns W.P.D.toPre.P a.D₀.P.isLB W.φ v W.w gv s2 _ _
        ((maps_iff v _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
          (rigPull_le W.φ (spMap (g.comp f)) W.he a.D₀.P.L) (fun _ => rfl)).2 pv) s3]
    intro F _ K _ pt pt₀ ε s s₀ x
    exact key _ w' hφ g' r₂ s s₀ x
  let xD : W.P.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := P.D.toPre.P.isAb.smooth
  have := a.D₀.P.isAb.proper
  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  refine ⟨t, m, P, φ, he, w, W.e.trans xD, gφ, gw, rw', fun x => ?_, fun z => ?_, fun F _ _ _ _ uF ha hu => ?_⟩
  · refine ext_of_injective hg gD.1 a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, gφ.1.w]
    · rw [← Category.assoc, ← act_proj hD (el x), Category.assoc, hφ, s4 x, ← Category.assoc, hφ]
  · refine ext_of_injective (p := 𝟙 _) (p' := 𝟙 _) hg (IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩) a.D₀.P.A.hom ?_ ?_
    · rw [Category.assoc, gφ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · have k := hD.c_pr (W.e z)
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) k.symm)).trans ?_
      rw [Category.assoc, hφ, s5 z, spMap_comp, Category.assoc]
  · obtain ⟨F', _, _, σ, ρ, hσρ⟩ := exists_common_field (algebraMap (FractionRing R) F) gam
    letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap (FractionRing R) F)).toAlgebra
    letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap (FractionRing O') F)).toAlgebra
    letI : Algebra (FractionRing V) F' := ρ.toAlgebra
    have hF : ∀ r : R, algebraMap (FractionRing R) F' (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) (g r)) := fun r =>
      (RingHom.congr_fun hσρ _).trans (congrArg ρ (hgam r))
    have ha' : ∀ x, algebraMap (FractionRing O') F' (algebraMap O' _ x) =
        algebraMap (FractionRing R) F' (algebraMap R _ (f x)) := fun x => congrArg σ (ha x)
    have hu' : σ uF = algebraMap (FractionRing R) F' (algebraMap R _ u) := congrArg σ hu
    have hj := jFK_comm hF
    have jR : jFK (R := R) F' = spMap σ ≫ jFK (R := R) F := spMap_comp _ _
    have jO : jFK (R := O') F' = spMap σ ≫ jFK (R := O') F := spMap_comp _ _
    refine ⟨fun z => ?_, fun yF hyF k p₀ s hs q₀ q x e₁ e₂ e₃ e₄ => ?_⟩
    · have k := (s6 F' (σ uF) (fun x => (ha' x).trans (hF _)) (hu'.trans (hF _))).1 z
      obtain ⟨n₁, n₂⟩ := pmaps_psi' hD hj (χ' := W.e z) rfl
      have k' := (genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB (fun _ => n₁) n₂ _ _).2 ((tr _ _ _).2 k)
      rw [← map_zpow₀] at k'
      refine (genRel_pull_iff σ w _ _ _).1 ((genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w ?_ ?_
        (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen _) _) _)
        (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _)
        (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (a.D₀.psi_gen _) _) _)
        (fun p J hJ => ?_) (fun p J hJ => ?_) _).1 k')
      · exact funext fun _ => (congrArg (· ≫ _) jR).trans (Category.assoc _ _ _)
      · exact funext fun _ => (congrArg (· ≫ _) jO).trans (Category.assoc _ _ _)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (P.D.toPre.psi (hD.xe (W.e z))) r p J)
          ((congrArg (𝟙 _ ≫ ·) jR).trans (Category.assoc _ _ _).symm)
      · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm)
        exact congrArg (fun r => val (a.D₀.psi z) r p J) ((congrArg (𝟙 _ ≫ ·) jO).trans (Category.assoc _ _ _).symm)
    · have hk : 1 ≤ k := by
        rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      obtain ⟨q₀', hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult σ (F' := F') rfl q₀
      obtain ⟨q', hq, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ (F' := F') rfl q
      let x' : TFK (R := R) F' ⟶ P.A.A := Over.homMk (spMap σ ≫ x.left) (by
        have w₂ : x.left ≫ P.A.A.hom = jFK (R := R) F := Over.w x
        show (spMap σ ≫ x.left) ≫ P.A.A.hom = jFK (R := R) F'
        rw [Category.assoc, w₂, jR])
      let σ' : F →ₐ[FractionRing R] F' := ⟨σ, fun _ => rfl⟩
      refine (TorsionExt.qkToAkU_iff_of_qkExt ⟨hL, h2, h3, h4, h5⟩ R I hR P.D P.A t.G t.semi P.U F F' σ' k hk q q' x x' hq
        rfl).2 ?_
      obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv hL h2 R V g P.D.toPre W.P.D.toPre hD P.D.tau_bimult W.P.D.tau_bimult F' hF k
      obtain ⟨k₁, k₂⟩ := (hτ q' _).1 rfl
      refine toA_down hL hR hV m P W hD bc mbc hPU hm F' hF (σ uF) ha' hu' (spMap σ ≫ yF)
        (by rw [Category.assoc, hyF, jR, Category.assoc]) k p₀ s hs q₀' q' (τ q') x' (ArcSpecialise.qkExt_trans e₁ hq₀)
        k₁ k₂ ?_ (fun z => ?_) ?_
      · rw [k₁, AddEquiv.symm_apply_eq, hq.1, hq₀.1]; exact e₂
      · obtain ⟨n₁, n₂⟩ := pmaps_of_isPullGtF k₂ (χ' := W.e z) rfl
        refine (tr _ _ _).1 ((genRel_transfer T P.D.toPre.P.isLB W.P.D.toPre.P.isLB n₁ n₂ _ _).1 ?_)
        rw [← map_zpow₀, hq₀.1]
        exact (genRel_congr P.D.toPre.P.isLB a.D₀.P.isLB w (gtφ_ext rfl hq _) (gtφ_ext rfl hq₀ _) (q'.g.isGen _)
          (DVR.pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (DVR.pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
          (fun p J hJ => val_corr hJ (hq.2.2 _) _) (fun p J hJ => val_corr hJ (hq₀.2.2 _) _) _).2
          ((genRel_pull_iff σ w _ _ _).2 (e₃ z))
      · show (spMap σ ≫ x.left) ≫ _ = _
        rw [Category.assoc, e₄, Category.assoc]

end GlobalTheory.ArcDataDescent
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_descends_from_completeDVR : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  atlas_forward_decl GlobalTheory.ArcDataDescent.hasArcData_descends
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

namespace ResidueGalois

theorem galois_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] [CharZero k] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    FiniteDimensional k K ∧ IsGalois k K ∧
      ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  have hn : Normal k K := Ideal.IsFractionRing.normal G P Q k K
  have hs : Algebra.IsSeparable k K := inferInstance
  refine ⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

theorem map_maximalIdeal_le {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]

end ResidueGalois

theorem exists_cDvr_residue_galois : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  intro V V' _ _ _ _ _ _ hV _ hu g hg hfin
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff V).1 hV
  let _ : Algebra V V' := g.toAlgebra
  have : Module.Finite V V' := hfin
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  let K := FractionRing V
  let K' := FractionRing V'
  let _ : Algebra K K' := FractionRing.liftAlgebra V K'
  have : IsScalarTower V K K' := FractionRing.isScalarTower_liftAlgebra V K'
  have : FiniteDimensional K K' := inferInstance
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  let W := integralClosure V L
  have hB : Module.Finite V W := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have : IsFractionRing W L := IsIntegralClosure.isFractionRing_of_finite_extension V K L W
  let i : V' →ₐ[V] L :=
    ((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')
  have hi : Function.Injective i :=
    (algebraMap K' L).injective.comp (IsFractionRing.injective V' K')
  let j : V' →ₐ[V] W := i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hjg : ∀ x, j (g x) = algebraMap V W x := fun x => j.commutes x
  have hjg' : (j : V' →+* W).comp g = algebraMap V W := RingHom.ext hjg
  have hint : ((j : V' →+* W).comp g).IsIntegral := by
    rw [hjg']
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W),
    (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
      inferInstance⟩, hj,
    ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint),
    ResidueGalois.map_maximalIdeal_le _ hint, ?_⟩
  intro k K₁ _ _ _ p q hp hq h
  have : CharZero k := ⟨fun m n hmn => by
    by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have := ((hu (n - m) (by omega)).map p).ne_zero
    rw [map_natCast, Nat.cast_sub hlt.le, hmn, sub_self] at this
    exact this rfl⟩
  have : Algebra.IsInvariant V W (W ≃ₐ[V] W) := Algebra.isInvariant_of_isGalois' V K L W
  have : Finite (W ≃ₐ[V] W) := Finite.of_equiv _ (galRestrict V K L W).toEquiv
  obtain ⟨h₁, h₂, h₃⟩ := ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq
    fun x => (h x).trans (congrArg q (hjg x))
  refine ⟨h₁, h₂, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h₃ τ
  refine ⟨σ.toRingEquiv, fun x => ?_, hσ⟩
  change σ (j (g x)) = j (g x)
  rw [hjg, AlgEquiv.commutes]

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  first | exact @GlobalTheory.exists_cDvr_residue_galois | exact GlobalTheory.exists_cDvr_residue_galois | (intros; apply GlobalTheory.exists_cDvr_residue_galois <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatumMatch_length_symm_preimages : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) := by
  first | exact @GlobalTheory.LN.be_symm_eq_of_match | exact GlobalTheory.LN.be_symm_eq_of_match | (intros; apply GlobalTheory.LN.be_symm_eq_of_match <;> assumption)
end

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.TorusPull

open ReciprocityTheory.ChartRestriction.G.DVR

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem mem_torus_iff {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) :
    (∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z) ↔
      z ≫ g.pG.left = z ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A := by
  have hb : (fstG I e G).left ≫ G.hom ≫ eSec D.P.A =
      ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D.P.A) (Over.w (fstG I e G)))
  constructor
  · rintro ⟨τ, rfl⟩
    have c := ((CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w).trans (congrArg (g.i.left ≫ ·) hb)
    exact (Category.assoc _ _ _).trans ((congrArg (τ ≫ ·) c).trans (Category.assoc _ _ _).symm)
  · intro h
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (z ≫ (thickObj R I e G).hom)
    let a : FinalForm ⟶ thickObj R I e G := Over.homMk z rfl
    have k := (CharAgree.comp_q_eq_one_iff g a).2 (h.trans (congrArg (z ≫ ·) hb.symm))
    exact ⟨(g.isKernel.lift a (toUnit _) k).left,
      congrArg (fun q => q.left) (g.isKernel.lift_fst a (toUnit _) k)⟩

theorem val_torus {T : Scheme.{0}}
    (τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left) (χ : D.X) {y : T}
    {J : (T ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) :
    val (g.t χ) (τ ≫ g.i.left) y J = gm τ y ⊤ (charUnit _ D.X χ) := by
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (τ ≫ (splitTorus _ D.X).hom)
  let a : FinalForm ⟶ splitTorus _ D.X := Over.homMk τ rfl
  exact (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm a 1 y J hJ χ).1

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))}
  {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)

include hp in

theorem unit_iff {Z : Scheme.{0}} (z : Z ⟶ T'.left) :
    z ≫ p'.left = z ≫ T'.hom ≫ eSec D'.P.A ↔ (z ≫ h) ≫ p.left = (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
  have b := TorusCoordPull.over_base hD p p' h hp
  have l : (z ≫ p'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = (z ≫ h) ≫ p.left := by
    rw [Category.assoc, hp, Category.assoc]
  have r : (z ≫ T'.hom ≫ eSec D'.P.A) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
    rw [Category.assoc, Category.assoc, hD.he, Category.assoc, reassoc_of% b]
  refine ⟨fun H => l.symm.trans ((congrArg (· ≫ _) H).trans r), fun H => ?_⟩
  refine (pull_grp hD).1.hom_ext (l.trans (H.trans r.symm)) ?_
  have u : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  rw [Category.assoc, Category.assoc, Category.assoc, u, Over.w]
  exact congrArg (z ≫ ·) (Category.comp_id _).symm

end Two

theorem appTop_ext {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (r' : Z ⟶ Y') (a : Γ(Y, ⊤)ˣ) (b : Γ(Y', ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = gm r' z ⊤ b) : r.appTop.hom a.val = r'.appTop.hom b.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have := congrArg Units.val (h z)
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at this
  exact this

theorem torus_point_iff : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  intro R R' _ _ _ _ I I' φ D D' hD G _ _ G' _ _ e g g' h hp ht T z a
  have mem := (mem_torus_iff g' z).trans ((unit_iff hD g.pG g'.pG h hp z).trans (mem_torus_iff g (z ≫ h)).symm)
  have ch : ∀ τ' τ, τ' ≫ g'.i.left = z → τ ≫ g.i.left = z ≫ h → ∀ x,
      τ'.appTop.hom (charUnit _ D'.X x).val = τ.appTop.hom (charUnit _ D.X (hD.xe x)).val := by
    intro τ' τ h' h₀ x
    refine appTop_ext _ _ _ _ fun y => ?_
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB y
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB y
    obtain ⟨hψ, H⟩ := ht x
    have P := (maps_iff hD.w _ _ _ (g'.t x) (g.t (hD.xe x)) h _
      (GeneratorPullback.pullAlong_le D.P.L _ h _ _ hψ) (fun _ => rfl)).1 H
    let FinalForm : Over (Spec (CommRingCat.of R')) :=
      Over.mk (z ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom)
    let ρ : FinalForm ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk z rfl
    have hρ : ρ ≫ g'.pG = 1 := by
      refine Over.OverMorphism.ext (((mem_torus_iff g' z).1 ⟨τ', h'⟩).trans ?_)
      have k : (toUnit FinalForm).left = FinalForm.hom := (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D'.P.A) k.symm)
    have v := TorusCoordPull.val_unit_pull hD g.pG g'.pG h hp P ρ hρ (y := y) hJ hJ'
    have v' := val_torus g' τ' x hJ'
    have v₀ := val_torus g τ (hD.xe x) hJ
    rw [h'] at v'
    rw [h₀] at v₀
    exact v'.symm.trans (v.symm.trans v₀)
  constructor
  · rintro ⟨τ', h', hx⟩
    obtain ⟨τ, h₀⟩ := mem.1 ⟨τ', h'⟩
    exact ⟨τ, h₀, fun x => (ch τ' τ h' h₀ x).symm.trans (hx x)⟩
  · rintro ⟨τ, h₀, hx⟩
    obtain ⟨τ', h'⟩ := mem.2 ⟨τ, h₀⟩
    exact ⟨τ', h', fun x => (ch τ' τ h' h₀ x).trans (hx x)⟩

end GlobalTheory.TorusPull
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoint_with_characters_iff_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  atlas_forward_decl GlobalTheory.TorusPull.torus_point_iff
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have hc := GlobalTheory.ZM.DwModel.isGaloisCover_field k K
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := hc.of_isPullback (ρ' := s) hG.1.flip hs₂ hs₁
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := hc.of_isPullback
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := SplitTorus.bcMap_torusFst (spMap (algebraMap k K)) X
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((SplitTorus.bcMap_torusFst _ X).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := hcG.existsUnique_desc (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := hcT.existsUnique_desc (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (hcG.existsUnique_desc (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (hcT.existsUnique_desc (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitTorusExtension_descent_galois_invariant : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  atlas_forward_decl GlobalTheory.exists_splitExt_of_galois_invariant
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.SplitAtTrait

section Torus

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}

def TorPt {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) {X : Type} (ε : X → D.X) (a : X → Γ(T, ⊤)) : Prop :=
  ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left,
    τ ≫ g.i.left = z ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (ε x)).val = a x

omit [IsDomain R] in
theorem mono_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

theorem pull_rel {φ : R →+* R'} {D : DegData R I} {D' : DegData R' I'} {hD : IsPullDeg φ D.toPre D'.toPre}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') (e : ℕ) {X : Type} (ε : X → D.toPre.X) (ε' : X ≃ D'.toPre.X)
    (hε : ∀ x, hD.xe (ε' x) = ε x) {T : Scheme.{0}} (z' : T ⟶ (thickObj R' I' e G').left)
    (z : T ⟶ (thickObj R I e G).left)
    (hz : z' ≫ (fstG I' e G').left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = z ≫ (fstG I e G).left) :
    z' ≫ (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) = z ≫ (U.gt e).pG.left ∧
      ∀ a, TorPt (U'.gt e) z' ε' a ↔ TorPt (U.gt e) z ε a := by
  obtain ⟨_, _, _, _, lev⟩ := hU.lg
  obtain ⟨h, h₁, h₂, h₃, -⟩ := lev e
  have := mono_fstG (I := I) e G
  obtain rfl : z' ≫ h = z := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, h₁, hz]
  refine ⟨by rw [h₂, Category.assoc], fun a => ?_⟩
  have key := GlobalTheory.T.torusPoint_with_characters_iff_pullDeg R R' I I' φ D.toPre D'.toPre hD G G' e (U.gt e) (U'.gt e) h h₂ h₃ T z' (fun x => a (ε'.symm x))
  constructor
  · rintro ⟨τ, hτ, ha⟩
    obtain ⟨τ₁, k₁, k₂⟩ := key.1 ⟨τ, hτ, fun x => by rw [← ha, Equiv.apply_symm_apply]⟩
    exact ⟨τ₁, k₁, fun x => by rw [← hε, k₂, Equiv.symm_apply_apply]⟩
  · rintro ⟨τ, hτ, ha⟩
    obtain ⟨τ₁, k₁, k₂⟩ := key.2 ⟨τ, hτ, fun x => by rw [← ha, ← hε, Equiv.apply_symm_apply]⟩
    exact ⟨τ₁, k₁, fun x => by rw [k₂, Equiv.symm_apply_apply]⟩

end Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {W₀ : ValuationSubring ℂ}
  {Y : Model Xo c (c.V W₀).subtype} {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'}
  {a : ArcIn D l (c.V W₀).subtype O' b}

set_option maxHeartbeats 3200000 in

theorem same_rel (hL : Laws) (h2 : Laws2) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {I : Ideal R} (hadm : AdmBase R I) {f : O' →+* R} {u : R}
    (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu' : ¬ IsUnit u) {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ)
    (y : Sp (FractionRing R) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK R ≫ χ) (e : ℕ) {T : Scheme.{0}}
    (z : T ⟶ (thickObj R I e W.t.G).left) (z' : T ⟶ (thickObj R I e W'.t.G).left)
    (hz₁ : z ≫ (fstG I e W.t.G).left ≫ W.m.φ = z' ≫ (fstG I e W'.t.G).left ≫ W'.m.φ)
    (hz₂ : z ≫ (fstG I e W.t.G).left ≫ W.t.G.hom = z' ≫ (fstG I e W'.t.G).left ≫ W'.t.G.hom) :
    z ≫ (W.P.U.gt e).pG.left ≫ W.φ = z' ≫ (W'.P.U.gt e).pG.left ≫ W'.φ ∧
      ∀ s, TorPt (W.P.U.gt e) z W.e s ↔ TorPt (W'.P.U.gt e) z' W'.e s := by
  letI := H.starRing
  have hs := specOf_id R
  have hQ := qkPullExists hL.globalFns
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact not_isUnit_zero (hx ▸ hf x h0)
  obtain ⟨ψ, hφ, hψ, hact, -⟩ := ArcWit.uwIso W W'
  obtain ⟨bc, D'', hD₂, U'', mod'', oD'', mbc, hbc, hLG, -, hPU₂, xl₂, el₂, lin'', -⟩ :=
    ArcWit.uwMove h4.unifBaseChange h5 hadm W W' ψ hφ hact
  obtain ⟨wL₀, -, g₀, -, m₀, -, -⟩ := exists_iso_pair_of_eq hLG
  obtain ⟨hD₁, hlev, holin⟩ := h6.unifUniq R I hadm W.P.D D'' W.P.A W'.P.A W.t.G W.t.semi W.P.U U'' wL₀ g₀ m₀
  obtain ⟨xl₁, el₁⟩ := holin (𝓞 E) W.P.oD oD'' W.P.oA W'.P.oA W.t.act.toRingAct W.P.lin lin''
  have mR : IsMonHom (Iso.refl W.t.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl W.t.G)).congr hs.symm rfl)
    (isGrpPullback_pullback W.t.G (specOf (RingHom.id R)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst W.t.G.hom (specOf (RingHom.id R)) = 𝟙 _ := hbc₀
  have hPU₁ := isPullUnif_of_uniq W.P.U U'' hD₁ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨he₁, w₁, e₁, hxe₁, -, d1, d2, d3, d4, d5, d6⟩ :=
    ArcWit.witMove h5 hQ hadm W U'' oD'' bc₀ hD₁ hPU₁ xl₁ el₁
  obtain ⟨he₂, w₂, e₂, hxe₂, -, d1', d2', d3', d4', d5', d6'⟩ :=
    ArcWit.witMove h5 hQ hadm W' U'' oD'' bc hD₂ hPU₂ xl₂ el₂
  have M₁ : Match a f u D''.toPre oD'' _ he₁ w₁ e₁ :=
    ⟨d1, d2, d3, d4, d5, fun F _ _ _ _ uF h1 h2 => (d6 F uF h1 h2).1⟩
  have M₂ : Match a f u D''.toPre oD'' _ he₂ w₂ e₂ :=
    ⟨d1', d2', d3', d4', d5', fun F _ _ _ _ uF h1 h2 => (d6' F uF h1 h2).1⟩
  obtain ⟨hφe, hee, -⟩ := GlobalTheory.MatchRigid.rigid hL h2 E H D l c W₀ O' b a R f u hfi D''.toPre oD'' _ _ he₁ he₂ w₁ w₂ e₁ e₂
    D''.tau_bimult M₁ M₂ (GlobalTheory.T.arcDatumMatch_length_symm_preimages E H D l c _ _ O' b a R f u hf hu' D''.toPre oD'' _ _ he₁ he₂ w₁ w₂ e₁ e₂ M₁ M₂)
    (fun F _ _ _ _ uF hF hu v hv q₀ q₁ q₂ hq₀ hy₁ hy₂ hg₁ hg₂ => by
      have hn : 1 ≤ l.M := le_trans (by norm_num) l.three_le
      have hσ : (l.M = l.A ∧ ∃ v', HEq (a.eta v) (a.etaA v') ∧ Y.oF.eta v = Y.oF.etaA v') ∨
          (l.M = l.M ∧ ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
            HEq (a.eta v) (a.eta v') ∧ Y.oF.eta v = Y.oF.eta v') := Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩
      have hyF : (jFK (R := R) F ≫ y) ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ := by
        rw [Category.assoc, hy]
      have hσw : (Y.oF.eta v).left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w (Y.oF.eta v)
      have hmw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _ := Y.m.cart.1.w
      have hc0 : ((jFK (R := R) F ≫ y) ≫ (Y.oF.eta v).left ≫ Y.m.φ) ≫ Y.t.G.hom = (jFK (R := R) F ≫ jK R) ≫ χ := by
        simp only [Category.assoc]
        rw [hmw, reassoc_of% hσw]
        simpa only [Category.assoc, Model.j] using hyF
      have hz₀ := W.m.cart.1.lift_fst _ _ hc0
      have hz₀' := W.m.cart.1.lift_snd _ _ hc0
      let z₁ : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj W.t.G :=
        Over.homMk (pullback.lift _ (jFK (R := R) F) hz₀') (pullback.lift_snd _ _ _)
      let x'' : TFK (R := R) F ⟶ W'.P.A.A := z₁ ≫ U''.gen.hom
      have hx₀ : x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) = W.m.cart.1.lift _ _ hc0 := by
        have hgi : U''.gen.hom.left ≫ U''.gen.inv.left = 𝟙 _ := by
          rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
        show (z₁.left ≫ U''.gen.hom.left) ≫ _ = _
        rw [Category.assoc, ← Category.assoc U''.gen.hom.left, hgi, Category.id_comp]
        exact pullback.lift_fst _ _ _
      have A1 := (d6 F uF hF hu).2 _ hyF l.M _ _ hσ q₀ q₁ x'' hq₀ hy₁ hg₁ (by
        rw [show x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) ≫ bc₀.hom.left ≫
            pullback.fst W.t.G.hom (specOf (RingHom.id R)) ≫ W.m.φ =
            (x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) ≫
              (bc₀.hom.left ≫ pullback.fst W.t.G.hom (specOf (RingHom.id R))) ≫ W.m.φ by
            simp only [Category.assoc], hx₀, hbc₀', Category.id_comp, hz₀])
      have A2 := (d6' F uF hF hu).2 _ hyF l.M _ _ hσ q₀ q₂ x'' hq₀ hy₂ hg₂ (by
        rw [show x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) ≫ bc.hom.left ≫
            pullback.fst W'.t.G.hom (specOf (RingHom.id R)) ≫ W'.m.φ =
            (x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) ≫
              (bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id R))) ≫ W'.m.φ by
            simp only [Category.assoc], hx₀, hbc, hφ, hz₀])
      exact GlobalTheory.TorsionMapInj.qkToAk_injective hL h2 R _ hadm D'' W'.P.A W.t.G W.t.semi U'' F l.M hn q₁ q₂ x'' A1 A2)
  subst hee
  have hzψ : z ≫ (fstG I e W.t.G).left ≫ ψ.hom.left = z' ≫ (fstG I e W'.t.G).left := by
    apply W'.m.cart.1.hom_ext
    · have hφ' : ψ.hom.left ≫ W'.m.cm.F = W.m.φ := hφ
      simp only [Category.assoc, hφ']; exact hz₁
    · simp only [Category.assoc, Over.w ψ.hom]; exact hz₂
  obtain ⟨a₁, b₁⟩ := pull_rel hPU₁ e W.e e₁.toEquiv hxe₁ z z (by rw [hbc₀']; exact congrArg _ (Category.comp_id _))
  obtain ⟨a₂, b₂⟩ := pull_rel hPU₂ e W'.e e₁.toEquiv hxe₂ z z' (by rw [hbc]; exact hzψ)
  refine ⟨?_, fun s => (b₁ s).symm.trans (b₂ s)⟩
  have k := congrArg (z ≫ (U''.gt e).pG.left ≫ ·) hφe
  simp only [Category.assoc] at k
  rw [← reassoc_of% a₁, ← reassoc_of% a₂]
  exact k

theorem bc_rel (hL : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {R R' : Type} [CommRing R]
    [IsDomain R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} {f' : O' →+* R'} {u' : R'}
    {χ' : Sp R' ⟶ Y.X} (hf : ∀ x, x ≠ 0 → IsUnit (f' x)) (hu : ¬ IsUnit u') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (e₁ : f' = g.comp f) (e₂ : u' = g u) (e₃ : χ' = spMap g ≫ χ) (W : ArcWit Y a I f u χ)
    (W' : ArcWit Y a I' f' u' χ') (y : Sp (FractionRing R') ⟶ Xo.XF c) (hy : y ≫ Y.j = jK R' ≫ χ') (e : ℕ)
    {T : Scheme.{0}} (z' : T ⟶ (thickObj R' I' e W'.t.G).left) (z : T ⟶ (thickObj R I e W.t.G).left)
    (hz₁ : z' ≫ (fstG I' e W'.t.G).left ≫ W'.m.φ = z ≫ (fstG I e W.t.G).left ≫ W.m.φ)
    (hz₂ : z' ≫ (fstG I' e W'.t.G).left ≫ W'.t.G.hom ≫ spMap g = z ≫ (fstG I e W.t.G).left ≫ W.t.G.hom) :
    z' ≫ (W'.P.U.gt e).pG.left ≫ W'.φ = z ≫ (W.P.U.gt e).pG.left ≫ W.φ ∧
      ∀ s, TorPt (W'.P.U.gt e) z' W'.e s ↔ TorPt (W.P.U.gt e) z W.e s := by
  subst e₁ e₂ e₃
  obtain ⟨W₁, hD, bc, -, hPU, hm, hxe, -, hφ₁, -, -⟩ := ArcWit.baseChange h3.cubePull hL.polBaseChange
    h4.unifBaseChange h5 (qkPullExists hL.globalFns) polOActPull hR hR' W g hg hI
  obtain ⟨ψ, hφ, -⟩ := ArcWit.uwIso W' W₁
  let z₁ : T ⟶ (thickObj R' I' e W₁.t.G).left := z' ≫ ((Over.pullback (thick R' I' e)).map ψ.hom).left
  have k₀ : ((Over.pullback (thick R' I' e)).map ψ.hom).left ≫ (fstG I' e W₁.t.G).left =
      (fstG I' e W'.t.G).left ≫ ψ.hom.left := pullback.lift_fst _ _ _
  have k₁ : z₁ ≫ (fstG I' e W₁.t.G).left = z' ≫ (fstG I' e W'.t.G).left ≫ ψ.hom.left := by
    rw [← k₀]; exact Category.assoc _ _ _
  obtain ⟨a₁, b₁⟩ := same_rel hL h2 h4 h5 h6 hR' hf hu W' W₁ y hy e z' z₁
    (by rw [reassoc_of% k₁, hφ]) (by rw [reassoc_of% k₁, Over.w ψ.hom])
  obtain ⟨a₂, b₂⟩ := pull_rel hPU e W.e W₁.e.toEquiv hxe z₁ z (by
    apply W.m.cart.1.hom_ext
    · have hm' : bc.hom.left ≫ pullback.fst W.t.G.hom (specOf g) ≫ W.m.cm.F = W₁.m.φ := by
        rw [hm, Category.assoc]
      simp only [Category.assoc]
      rw [hm', reassoc_of% k₁, hφ]; exact hz₁
    · have w₁ : bc.hom.left ≫ pullback.snd W.t.G.hom (specOf g) = W₁.t.G.hom := Over.w bc.hom
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% w₁, reassoc_of% k₁, reassoc_of% (Over.w ψ.hom)]; exact hz₂)
  refine ⟨?_, fun s => (b₁ s).trans (b₂ s)⟩
  rw [a₁, hφ₁, ← reassoc_of% a₂]
  simp only [Category.assoc]

theorem torus_ext {S T : Scheme.{0}} {X : Type} [AddCommGroup X] (τ τ' : T ⟶ (splitTorus S X).left)
    (h₁ : τ ≫ (splitTorus S X).hom = τ' ≫ (splitTorus S X).hom)
    (h₂ : ∀ x, τ.appTop.hom (charUnit S X x).val = τ'.appTop.hom (charUnit S X x).val) : τ = τ' := by
  have := GlobalTheory.SplitTorus.hom_ext (T := Over.mk (τ ≫ (splitTorus S X).hom)) (g := Over.homMk τ rfl)
    (g' := Over.homMk τ' h₁.symm) (fun x => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val]; exact h₂ x)
  exact congrArg (·.left) this

set_option maxHeartbeats 1600000 in

theorem split_of_galois (hL : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {V R : Type}
    [CommRing V] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} (hR : AdmBase R I)
    (hI : I = IsLocalRing.maximalIdeal R) (f : O' →+* V) (u : V) (χ : Sp V ⟶ Y.X) (t : SAB H (Sp V))
    (m : SABMap t Y.t χ) (g : V →+* R) (hf : ∀ x, x ≠ 0 → IsUnit (g (f x))) (hu : ¬ IsUnit (g u))
    (W : ArcWit Y a I (g.comp f) (g u) (spMap g ≫ χ)) (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK R ≫ spMap g ≫ χ) (k : Type) [Field k] (p : V →+* k) [(I ^ (0 + 1)).IsMaximal]
    (α : k →+* R ⧸ I ^ (0 + 1)) (hα : α.comp p = (Ideal.Quotient.mk _).comp g)
    (hG : letI := Ideal.Quotient.field (I ^ (0 + 1)); letI := α.toAlgebra
      FiniteDimensional k (R ⧸ I ^ (0 + 1)) ∧ IsGalois k (R ⧸ I ^ (0 + 1)) ∧
        ∀ τ : (R ⧸ I ^ (0 + 1)) ≃ₐ[k] (R ⧸ I ^ (0 + 1)), ∃ σ : R ≃+* R, (∀ x, σ (g x) = g x) ∧
          ∀ x, Ideal.Quotient.mk _ (σ x) = τ (Ideal.Quotient.mk _ x)) :
    ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (spMap p)).obj t.G) := by
  letI := Ideal.Quotient.field (I ^ (0 + 1))
  letI := α.toAlgebra
  obtain ⟨hfin, hgal, haut⟩ := hG
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m W.m
  have sq : thick R I 0 ≫ spMap g = spMap α ≫ spMap p :=
    (spMap_comp g _).symm.trans ((congrArg spMap hα.symm).trans (spMap_comp p α))
  have sq' : thick R I 0 ≫ spMap (g.comp f) = spMap α ≫ spMap (p.comp f) := by
    rw [spMap_comp, spMap_comp, reassoc_of% sq]
  have gG : IsGrpPullback (thickObj R I 0 W.t.G) t.G (spMap α ≫ spMap p) ((fstG I 0 W.t.G).left ≫ n.φ) :=
    ((isGrpPullback_pullback W.t.G (thick R I 0)).comp n.cart).congr sq rfl
  have gB : IsGrpPullback (thickObj R I 0 W.P.D.toPre.P.A) a.D₀.P.A (spMap α ≫ spMap (p.comp f))
      (pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) ≫ W.φ) :=
    ((isGrpPullback_pullback W.P.D.toPre.P.A (thick R I 0)).comp W.spec.1).congr sq' rfl
  obtain ⟨φG, G₁, G₂⟩ : ∃ φG : (thickObj R I 0 W.t.G).left ⟶ ((Over.pullback (spMap p)).obj t.G).left,
      φG ≫ pullback.fst t.G.hom (spMap p) = (fstG I 0 W.t.G).left ≫ n.φ ∧
      φG ≫ ((Over.pullback (spMap p)).obj t.G).hom = (thickObj R I 0 W.t.G).hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gG.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨φB, B₁, B₂⟩ : ∃ φB : (thickObj R I 0 W.P.D.toPre.P.A).left ⟶
      ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A).left,
      φB ≫ pullback.fst a.D₀.P.A.hom (spMap (p.comp f)) = pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) ≫ W.φ ∧
      φB ≫ ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A).hom =
        (thickObj R I 0 W.P.D.toPre.P.A).hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gB.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have haff := (W.P.U.gt 0).q_affine
  refine GlobalTheory.T.exists_splitTorusExtension_descent_galois_invariant k (R ⧸ I ^ (0 + 1)) ((Over.pullback (spMap p)).obj t.G)
    ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A) (GlobalTheory.isAbelianScheme_pullback_obj _ _ a.D₀.P.isAb)
    (thickObj R I 0 W.t.G) (thickObj R I 0 W.P.D.toPre.P.A) W.P.D.toPre.X φG φB
    ((isGrpPullback_pullback t.G (spMap p)).cancel (gG.congr rfl G₁.symm) G₂)
    ((isGrpPullback_pullback a.D₀.P.A (spMap (p.comp f))).cancel (gB.congr rfl B₁.symm) B₂)
    (W.P.U.gt 0).q (W.P.U.gt 0).i (W.P.U.gt 0).q_hom (W.P.U.gt 0).q_flat (W.P.U.gt 0).q_surj inferInstance
    (W.P.U.gt 0).i_hom (W.P.U.gt 0).isKernel (fun τ s s₁ s₂ => ?_)
  obtain ⟨σ, σ₁, σ₂⟩ := haut τ
  have σg : (σ : R →+* R).comp g = g := RingHom.ext σ₁
  have σI : I.map (σ : R →+* R) ≤ I := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    exact (map_mem_nonunits_iff (σ : R →+* R) x).2 hx
  have σt : thick R I 0 ≫ spMap (σ : R →+* R) = spMap (τ : _ →+* _) ≫ thick R I 0 :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext σ₂)).trans (spMap_comp _ _))
  have τα : spMap (τ : _ →+* _) ≫ spMap α = spMap α :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext τ.commutes))
  have c₀ : (fstG I 0 W.t.G).left ≫ W.t.G.hom = (thickObj R I 0 W.t.G).hom ≫ thick R I 0 := pullback.condition
  have rel := fun (T : Scheme.{0}) (z : T ⟶ (thickObj R I 0 W.t.G).left) =>
    bc_rel hL h2 h3 h4 h5 h6 hR hR hf hu (σ : R →+* R) σ.injective σI
      (by rw [← RingHom.comp_assoc, σg]) (σ₁ u).symm (by rw [← Category.assoc, ← spMap_comp, σg]) W W y hy 0 z (z ≫ s)
      (by rw [hn, ← reassoc_of% G₁, Category.assoc, reassoc_of% s₁])
      (by rw [reassoc_of% c₀, σt, c₀, Category.assoc, reassoc_of% s₂])
  have pq : (W.P.U.gt 0).pG.left = (W.P.U.gt 0).q.left ≫ pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) := rfl
  constructor
  · apply pullback.hom_ext
    · have r₁ := (rel _ (𝟙 _)).1
      rw [Category.id_comp, Category.id_comp, pq] at r₁
      simp only [Category.assoc] at r₁ ⊢
      rw [B₁]; exact r₁.symm
    · have wq : (W.P.U.gt 0).q.left ≫ (thickObj R I 0 W.P.D.toPre.P.A).hom = (thickObj R I 0 W.t.G).hom :=
        Over.w _
      have B₂' : φB ≫ pullback.snd a.D₀.P.A.hom (spMap (p.comp f)) =
        (thickObj R I 0 W.P.D.toPre.P.A).hom ≫ spMap α := B₂
      simp only [Category.assoc]
      rw [B₂', reassoc_of% wq, reassoc_of% s₂, τα]
  · obtain ⟨τ₁, k₁, k₂⟩ := ((rel _ (W.P.U.gt 0).i.left).2 (fun x => (charUnit _ _ (W.e x)).val)).1
      ⟨𝟙 _, Category.id_comp _, fun x => by rw [Scheme.Hom.id_appTop]; rfl⟩
    rw [← k₁]
    congr 1
    have wi : (W.P.U.gt 0).i.left ≫ (thickObj R I 0 W.t.G).hom = (splitTorus _ W.P.D.toPre.X).hom := Over.w _
    refine torus_ext _ _ ?_ fun x => ?_
    · rw [GlobalTheory.SplitTorus.bcMap_hom, ← wi, reassoc_of% k₁, s₂, Category.assoc]
    · obtain ⟨x, rfl⟩ := W.e.surjective x
      refine Eq.trans ?_ (k₂ x).symm
      beta_reduce
      rw [GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.bcMap_appTop_chi]

theorem splitOver_of_hasArcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : O' →+* V) (u : V), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (χ : Sp V ⟶ Y.X) (y : Sp (FractionRing V) ⟶ Xo.XF c), y ≫ Y.j = jK V ≫ χ → ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t χ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V' → ∀ g : V →+* V', Function.Injective g → g.Finite → Y.HasArcData a (IsLocalRing.maximalIdeal V') (g.comp f) (g u) (spMap g ≫ χ) → SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  intro hL h2 h3 h4 h5 h6 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a V _ _ _ hV f u hf hu χ y hy t m V' _ _ _ hV' g hg hfin hA
  obtain ⟨W'⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨R, _, _, _, j, hR, hj, hjI, hgI, hG⟩ := GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms V V' hV hV'
    (fun n hn => by rw [← map_natCast f]; exact hf _ (Nat.cast_ne_zero.2 hn)) g hg hfin
  have := hR.1
  have := hV'.1
  have aR : AdmBase R (IsLocalRing.maximalIdeal R) := ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩
  have aV : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'.2.1⟩
  obtain ⟨W₁, -⟩ := ArcWit.baseChange h3.cubePull hL.polBaseChange h4.unifBaseChange h5 (qkPullExists hL.globalFns)
    polOActPull aV aR W' j hj hjI
  have W : ArcWit Y a (IsLocalRing.maximalIdeal R) ((j.comp g).comp f) ((j.comp g) u) (spMap (j.comp g) ≫ χ) := by
    rw [spMap_comp, Category.assoc]; exact W₁
  let gam : FractionRing V →+* FractionRing R :=
    IsFractionRing.lift (g := (algebraMap R (FractionRing R)).comp (j.comp g))
      ((IsFractionRing.injective R _).comp (hj.comp hg))
  have hgam : ∀ r, gam (algebraMap V _ r) = algebraMap R _ (j.comp g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK V = jK R ≫ spMap (j.comp g) :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp (j.comp g) _))
  have hp : IsLocalRing.maximalIdeal R ^ (0 + 1) = IsLocalRing.maximalIdeal R := pow_one _
  haveI : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by rw [hp]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R ^ (0 + 1))
  let α : V ⧸ IsLocalRing.maximalIdeal V →+* R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1) :=
    Ideal.quotientMap _ (j.comp g) (by rw [hp]; exact Ideal.map_le_iff_le_comap.1 hgI)
  letI := α.toAlgebra
  have hG' := hG (V ⧸ IsLocalRing.maximalIdeal V) (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective (fun _ => rfl)
  exact split_of_galois hL h2 h3 h4 h5 h6 aR rfl f u χ t m (j.comp g) (fun x hx => (hf x hx).map _)
    (Ideal.map_le_iff_le_comap.1 hgI hu) W (spMap gam ≫ y) (by rw [Category.assoc, hy, reassoc_of% sq])
    (V ⧸ IsLocalRing.maximalIdeal V) (Ideal.Quotient.mk _) α (Ideal.quotientMap_comp_mk _) hG'

end GlobalTheory.SplitAtTrait
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_split_of_arcData_finite_extension : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : O' →+* V) (u : V), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (χ : Sp V ⟶ Y.X) (y : Sp (FractionRing V) ⟶ Xo.XF c), y ≫ Y.j = jK V ≫ χ → ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t χ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V' → ∀ g : V →+* V', Function.Injective g → g.Finite → Y.HasArcData a (IsLocalRing.maximalIdeal V') (g.comp f) (g u) (spMap g ≫ χ) → SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  first | exact @GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | exact GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | (intros; apply GlobalTheory.SplitAtTrait.splitOver_of_hasArcData <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcSplit

open CoordToExt TorusCoord

section Unique

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem exists_coordHom (g : GtCoord I D e G) (g' : GtCoord I D e G') :
    ∃ F : thickObj R I e G ⟶ thickObj R I e G', F.left ≫ g'.pG.left = g.pG.left ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
        val (g'.t χ) (r ≫ F.left) z J = val (g.t χ) r z J := by
  obtain ⟨F, hF⟩ := (toGtPt_bijective g' (T := thickObj R I e G)).2 (toGtPt g (𝟙 _))
  have h := isPointOf_toGtPt g (𝟙 (thickObj R I e G))
  have h' := (toGtPt_eq_iff g' F _).1 hF
  refine ⟨F, h'.1.symm.trans (h.1.trans (Category.id_comp _)), fun χ Z r z J hJ => ?_⟩
  refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h'.2 χ) r).symm.trans
    ((val_corr hJ (h.2 χ) r).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun x => val (g.t χ) x z J) (Category.comp_id r)

theorem exists_iso_of_coord (hG : GlobalFnsSt) (g : GtCoord I D e G) (g' : GtCoord I D e G') :
    ∃ F : thickObj R I e G ≅ thickObj R I e G', IsMonHom F.hom := by
  obtain ⟨F, hF, vF⟩ := exists_coordHom g g'
  obtain ⟨F', hF', vF'⟩ := exists_coordHom g' g
  have him : ∀ {T} (x : T ⟶ thickObj R I e G), im g' (x ≫ F) = im g x := fun x =>
    Over.OverMorphism.ext ((Category.assoc x.left F.left _).trans (congrArg (x.left ≫ ·) hF))
  have mul : ∀ (T) (x y : T ⟶ thickObj R I e G), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro T x y
    refine Over.OverMorphism.ext (ext_of_val g' _ _ ?_ fun χ z J hJ => ?_)
    · have : im g' ((x * y) ≫ F) = im g' ((x ≫ F) * (y ≫ F)) := by
        rw [him, im_mul, im_mul, him, him]
      exact congrArg (·.left) this
    · have a := val_t_mul_points g hG χ x y z J hJ
      have a' := val_t_mul_points g' hG χ (x ≫ F) (y ≫ F) z J hJ
      have c : cubeVal g' χ z J (x ≫ F) (y ≫ F) = cubeVal g χ z J x y := by
        unfold cubeVal
        rw [him, him]
      rw [c] at a'
      refine (vF χ _ _ z J hJ).trans (mul_right_cancel (a.trans (Eq.trans ?_ a'.symm)))
      exact congrArg₂ (· * ·) (vF χ _ _ z J hJ).symm (vF χ _ _ z J hJ).symm
  refine ⟨⟨F, F', Over.OverMorphism.ext (ext_of_val g _ _ ?_ fun χ z J hJ => ?_),
    Over.OverMorphism.ext (ext_of_val g' _ _ ?_ fun χ z J hJ => ?_)⟩, ⟨?_, ?_⟩⟩
  · rw [Over.comp_left, Category.assoc, hF', hF]
    exact (Category.id_comp _).symm
  · refine (vF' χ _ _ z J hJ).trans (Eq.trans ?_ (vF χ _ _ z J hJ))
    exact congrArg (fun x => val (g'.t χ) x z J) (Category.id_comp _).symm
  · rw [Over.comp_left, Category.assoc, hF, hF']
    exact (Category.id_comp _).symm
  · refine (vF χ _ _ z J hJ).trans (Eq.trans ?_ (vF' χ _ _ z J hJ))
    exact congrArg (fun x => val (g.t χ) x z J) (Category.id_comp _).symm
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ _ ⟶ thickObj R I e G) ≫ F = 1 := mul_eq_left.1 h.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h'
  · have h := mul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end Unique

section Datum

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev bundle₀ (χ : D.X) : LB D.P.A.left := LB.LinComb D.P.L (D.Oφ (𝟙 D.P.A) χ) Oε

theorem comp_Oφ_id {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem bundle₀_add (χ χ' : D.X) :
    ∃ t : LB.Iso (bundle₀ D χ') (LB.div (bundle₀ D (χ + χ')) (bundle₀ D χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (𝟙 D.P.A))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (𝟙 D.P.A) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (𝟙 _) _ h) (congrArg (·⁻¹) (prod_O D (𝟙 _) _ h)))
    (congrArg (·⁻¹) (prod_O D (𝟙 _) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem bundle₀_zero : ∃ t : LB.Gen (bundle₀ D 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (𝟙 _) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem bundle₀_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ D.P.A (bundle₀ D χ)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (x2 D.P.A 0) (x2 D.P.A 1))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (x2 D.P.A 0) (x2 D.P.A 1) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, comp_Oφ_id]
  refine (prod_square (x2 D.P.A) (fun x => ∏ k, h (D.Oφ x χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D _ _ h) (congrArg (·⁻¹) (prod_O D _ _ h)))
    (congrArg (·⁻¹) (prod_O D _ _ h))) (prod_O D _ _ h)).trans ?_
  rw [_root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem bundle₀_rig (χ : D.X) : ∃ t : LB.Gen ((bundle₀ D χ).pull (eSec D.P.A)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ?_)
  have e₁ : η[D.P.A] = (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have e₂ : ∀ k, eSec D.P.A ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) χ k :=
    fun k => e₁ ▸ comp_Oφ_id D η[D.P.A] χ k
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  simp only [_root_.mul_one, e₂]
  refine (prod_O D _ _ h).trans ?_
  rw [_root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

def extOf : SplitExt (Spec (CommRingCat.of R)) where
  B := D.P.A
  isAbelian := D.P.isAb
  X := D.X
  O χ := ⟨bundle₀ D χ, (bundle₀_rig D χ).choose, DVR.linComb_isLB _ D.P.isLB _ _, (bundle₀_rig D χ).choose_spec⟩
  addIso := bundle₀_add D
  zeroTriv := bundle₀_zero D
  primitive := bundle₀_primitive D

variable {D} {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
  {f : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {φ : D'.P.A.left ⟶ D.P.A.left}

theorem Oφ_push (h : IsGrpPullback D'.P.A D.P.A f φ) {y : D.X} {y' : D'.X}
    (hc : (D'.c y').left ≫ φ = f ≫ (D.c y).left) (k : Fin 4) :
    D'.Oφ (𝟙 _) y' k ≫ φ = φ ≫ D.Oφ (𝟙 _) y k := by
  let ρ := pushHom h D'.P.A
  have e₁ : ρ (toUnit _ ≫ D'.c y') = toUnit _ ≫ D.c y := Over.OverMorphism.ext (by
    change (D'.P.A.hom ≫ (D'.c y').left) ≫ φ = (D'.P.A.hom ≫ f) ≫ (D.c y).left
    exact (Category.assoc _ _ _).trans ((congrArg (D'.P.A.hom ≫ ·) hc).trans (Category.assoc _ _ _).symm))
  have e₂ : (ρ (𝟙 _)).left = φ := Category.id_comp φ
  rw [← congrArg (· ≫ D.Oφ (𝟙 _) y k) e₂]
  refine Eq.trans ?_ (comp_Oφ_id D (ρ (𝟙 _)) y k).symm
  fin_cases k
  · exact congrArg (·.left) ((map_mul ρ (𝟙 _) (toUnit _ ≫ D'.c y')).trans (congrArg (ρ (𝟙 _) * ·) e₁))
  · exact congrArg (·.left) e₁
  · rfl
  · exact congrArg (·.left) (map_one ρ)

theorem nonempty_coord_pullback (hG : GlobalFnsSt) (h : IsGrpPullback D'.P.A D.P.A f φ)
    (w : LB.Iso D'.P.L (D.P.L.pull φ)) (hw : w.IsGen) (xe : D'.X ≃+ D.X)
    (hc : ∀ y, (D'.c y).left ≫ φ = f ≫ (D.c (xe y)).left) (I : Ideal R') (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (hE : (extOf D).IsGt G) :
    Nonempty (GtCoord I D' e ((Over.pullback f).obj G)) := by
  obtain ⟨d⟩ := hE
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (thick R' I e ≫ f))
    ((isGrpPullback_pullback D'.P.A (thick R' I e)).comp h)
  obtain ⟨κ, hκ, -⟩ := grpPullback_iso (isGrpPullback_pullback G (thick R' I e ≫ f))
    ((isGrpPullback_pullback ((Over.pullback f).obj G) (thick R' I e)).comp (isGrpPullback_pullback G f))
  refine nonempty_gtCoord_of_isGt hG R' I D' e _ (GtBaseChange.extBC (thick R' I e ≫ f) (extOf D)) β xe hβ
    (fun χ => ?_) (isGt_of_iso κ (GtBaseChange.isGt_extBC _ _ G d))
  refine LBIso.chartPull (chartPullOut D.P.L (D.Oφ (𝟙 _) (xe χ)) Oε _ _ fun k => ?_) (chartPullId _)
    (iso_linComb ((isGen_iff w).1 hw) _ Oε).symm
  rw [Category.assoc, Oφ_push h (hc χ) k, ← Category.assoc]
  exact congrArg (· ≫ _) ((Category.assoc _ _ _).trans hβ')

end Datum

theorem exists_iso_of_generic (h : HomExtSt) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing K] (hK : IsField K) [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback (spMap (algebraMap T K))).obj G ≅ (Over.pullback (spMap (algebraMap T K))).obj G')
    (hf : IsMonHom f.hom) : ∃ F : G ≅ G', IsMonHom F.hom := by
  letI := hK.toField
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := h T K G G' hG hG' f.hom hf
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := h T K G' G hG' hG f.inv inferInstance
  refine ⟨⟨F, F', (h T K G G hG hG (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩,
    (h T K G' G' hG' hG' (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩⟩, hF⟩
  · rw [Functor.map_comp, eF, eF']
    exact f.hom_inv_id
  · rw [Functor.map_comp, eF, eF']
    exact f.inv_hom_id

theorem mk_C_constantCoeff {A : Type} [CommRing A] {J : Ideal (PowerSeries A)} (hJ : PowerSeries.X ∈ J)
    (s : PowerSeries A) : Ideal.Quotient.mk J (PowerSeries.C (PowerSeries.constantCoeff s)) = Ideal.Quotient.mk J s := by
  refine Ideal.Quotient.eq.2 (Ideal.mem_of_dvd J (PowerSeries.X_dvd_iff.2 ?_) hJ)
  simp

theorem bijective_mk_C (K : Type) [Field K] :
    Function.Bijective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries K) ^ (0 + 1))).comp
      (PowerSeries.C (R := K))) := by
  have : Nontrivial (PowerSeries K ⧸ IsLocalRing.maximalIdeal (PowerSeries K) ^ (0 + 1)) := by
    rw [zero_add, pow_one]; infer_instance
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨_, mk_C_constantCoeff ?_ s⟩
  rw [zero_add, pow_one, PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span rfl

end GlobalTheory.ArcSplit

namespace GlobalTheory

open ArcSplit

theorem splitOver_of_hasArcData : Laws → Laws2 → Laws3 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b), IsDiscreteValuationRing O' → ∀ (χ : Sp (PowerSeries O') ⟶ Y.X) (t : SAB H (Sp (PowerSeries O'))) (_ : SABMap t Y.t χ), Y.HasArcData a (IsLocalRing.maximalIdeal (PowerSeries (FractionRing O'))) ((PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _)) PowerSeries.X (spMap (PowerSeries.map (algebraMap O' (FractionRing O'))) ≫ χ) → SplitOver t.G (Ideal.span {(PowerSeries.X : PowerSeries O')}) := by
  intro hL _ _ hExt E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a hO χ t m hA
  obtain ⟨t', m', P, φ, -, w, e, hφ, hw, -, -, hc, -⟩ := hA
  have hG := hL.globalFns
  obtain ⟨G, _, hGs, hGt⟩ := exists_isSemiAbelian_isGt hG _ (extOf a.D₀)
  have := hGs.comm
  let K' := FractionRing O'
  let I := IsLocalRing.maximalIdeal (PowerSeries K')
  let K := PowerSeries K' ⧸ I ^ (0 + 1)
  let f : O' →+* PowerSeries K' := (PowerSeries.C (R := K')).comp (algebraMap O' K')
  have hb := bijective_mk_C K'
  let ε : K' ≃+* K := RingEquiv.ofBijective _ hb
  have hK : IsField K := ε.symm.toMulEquiv.isField (Field.toIsField K')
  letI : Algebra O' K := ((Ideal.Quotient.mk (I ^ (0 + 1))).comp f).toAlgebra
  have : IsFractionRing O' K :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors O') (AlgEquiv.ofRingEquiv (f := ε) fun _ => rfl)
  have hX : PowerSeries.X ∈ I ^ (0 + 1) := by
    rw [zero_add, pow_one, show I = _ from PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  obtain ⟨g'⟩ := nonempty_coord_pullback hG hφ w hw e.symm.toAddEquiv
    (fun y => by have := hc (e.symm y); rwa [e.apply_symm_apply] at this) I 0 G hGt
  obtain ⟨F₁, hF₁⟩ := exists_iso_of_coord hG (P.U.gt 0) g'
  let ev : PowerSeries O' →+* O' := PowerSeries.constantCoeff
  let A := (Over.pullback (spMap ev)).obj t.G
  have e₁ : thick (PowerSeries K') I 0 ≫ spMap f = spMap (algebraMap O' K) := (spMap_comp _ _).symm
  have e₂ : thick (PowerSeries K') I 0 ≫ spMap (PowerSeries.map (algebraMap O' K')) =
      spMap (algebraMap O' K) ≫ spMap ev := by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap (RingHom.ext fun s => ?_)) (spMap_comp _ _))
    refine (mk_C_constantCoeff hX _).symm.trans (congrArg (fun x => Ideal.Quotient.mk _ (PowerSeries.C x)) ?_)
    rfl
  obtain ⟨F₀, hF₀, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback A (spMap (algebraMap O' K))).comp (isGrpPullback_pullback t.G (spMap ev))).comp m.cart)
    (((isGrpPullback_pullback t'.G (thick (PowerSeries K') I 0)).comp m'.cart).congr
      (by rw [← Category.assoc, e₂]) rfl)
  obtain ⟨F₂, hF₂, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (thick (PowerSeries K') I 0)).comp (isGrpPullback_pullback G (spMap f))).congr e₁ rfl)
    (isGrpPullback_pullback G (spMap (algebraMap O' K)))
  obtain ⟨F, hF⟩ := exists_iso_of_generic hExt O' K hK A G (IsSemiAbelian.pullback _ t.G t.semi) hGs
    (F₀ ≪≫ F₁ ≪≫ F₂) (inferInstanceAs (IsMonHom (F₀.hom ≫ F₁.hom ≫ F₂.hom)))
  have : IsMonHom F.symm.hom := inferInstanceAs (IsMonHom F.inv)
  obtain ⟨d⟩ := isGt_of_iso F.symm hGt
  let J : Ideal (PowerSeries O') := Ideal.span {PowerSeries.X}
  let s : O' →+* PowerSeries O' ⧸ J := (Ideal.Quotient.mk J).comp PowerSeries.C
  have e₃ : spMap s ≫ spMap ev = spMap (Ideal.Quotient.mk J) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext (mk_C_constantCoeff (Ideal.subset_span rfl))))
  obtain ⟨F₃, hF₃, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback A (spMap s)).comp (isGrpPullback_pullback t.G (spMap ev))).congr e₃ rfl)
    (isGrpPullback_pullback t.G (spMap (Ideal.Quotient.mk J)))
  exact ⟨_, isGt_of_iso F₃ (GtBaseChange.isGt_extBC (spMap s) _ A d)⟩

end GlobalTheory
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem polAt_of_point {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem admissible_maximal_ideal_of_complete_dvr_char_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) :
    admitted V (IsLocalRing.maximalIdeal V) ∧ IsPrincipalIdealRing (V ⧸ IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  exact ⟨⟨⟨inferInstance, inferInstance, inferInstance, h₂⟩, h₂, h₃, inferInstance, inferInstance⟩, inferInstance⟩

theorem cdvr_powerSeries (K : Type) [Field K] [CharZero K] : CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

theorem powerSeries_dvr_admissible_X_ideal (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal O) O) :
    admitted (PowerSeries O) (Ideal.span {PowerSeries.X}) ∧
      IsPrincipalIdealRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) := by
  have hk : Ideal.span {(PowerSeries.X : PowerSeries O)} = RingHom.ker (PowerSeries.constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) ≃+* O :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
  refine ⟨⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := O)), hk ▸ RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv e.symm⟩, IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective⟩
  infer_instance

theorem hasArcData_trait (h₁ : Laws) (h₂ : Laws2) (h₃ : Laws3) (h₄ : Laws4) (h₅ : Laws5) (h₆ : Laws6) (hE : Ega)
    (hU : USt) (hP : PelSt) (hH : HomExtSt) {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    {b : c.V W₀ →+* O'} (a : ArcIn D l (c.V W₀).subtype O' b) (hp : PushInvertible Y.t.G Y.t.PP.L)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X) (hχ : jK _ ≫ χ = y ≫ Y.j)
    (hT : TraitData Y a (RingHom.id _) y) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (φ : PowerSeries O' →+* V) (hφ : Function.Injective φ) (hX : ¬ IsUnit (φ PowerSeries.X))
    (hC : ∀ x, x ≠ 0 → IsUnit (φ (PowerSeries.C x))) :
    Y.HasArcData a (IsLocalRing.maximalIdeal V) (φ.comp (PowerSeries.C (R := O'))) (φ PowerSeries.X) (spMap φ ≫ χ) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp φ) := (IsFractionRing.injective V _).comp hφ
  let gam : FractionRing (PowerSeries O') →+* FractionRing V := IsFractionRing.lift hinj
  have hg : ∀ r, gam (algebraMap _ _ r) = algebraMap V _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ y ≫ Y.j = jK V ≫ spMap φ ≫ χ := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hg r
  obtain ⟨W, _, _, _, io, hW, hio, hfin, hA⟩ := (hT.2 V hV φ gam hg _ hsq).2 hX
  have hA' : Y.HasArcData a (IsLocalRing.maximalIdeal W) (io.comp (φ.comp (PowerSeries.C (R := O'))))
    (io (φ PowerSeries.X)) (spMap io ≫ spMap φ ≫ χ) := hA
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap φ ≫ χ) Y.t
  have hsq' : (spMap gam ≫ y) ≫ Y.j = jK V ≫ spMap φ ≫ χ := (Category.assoc _ _ _).trans hsq
  have hS := GlobalTheory.T.closedFibre_split_of_arcData_finite_extension h₁ h₂ h₃ h₄ h₅ h₆ E H D l Xo c W₀ Y O' b a V hV _ _ hC hX _ _ hsq' t m W hW io hio hfin hA'
  obtain ⟨hadm, hpid⟩ := admissible_maximal_ideal_of_complete_dvr_char_zero hV
  obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H V _ hadm hpid t (polAt_of_point Y m _ _ hsq') hS
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp V _ t m)
  have := hV.2.2
  have hloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  exact GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a V _ _ _ hadm.1
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (hφ.comp PowerSeries.C_injective) _ _ hsq' t m P hPt W hW io hio
    (IsLocalRing.map_maximalIdeal_le io) (fun h => hX (isUnit_of_map_unit io _ h)) (fun x hx => (hC x hx).map io) hA'

theorem hasArcData_of_traitData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb hp y χ hχ hT
  rcases hb with ⟨hf, -⟩ | ⟨hd, hϖ, hc⟩
  · letI := hf.toField
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT (cdvr_powerSeries O') (RingHom.id _)
      Function.injective_id PowerSeries.X_prime.not_unit (fun x hx => (IsUnit.mk0 x hx).map (PowerSeries.C (R := O')))
    have e : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp, PowerSeries.maximalIdeal_eq_span_X] at h
    exact h
  · have hi := IsFractionRing.injective O' (FractionRing O')
    have hX : ¬ IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) PowerSeries.X) := by
      rw [PowerSeries.map_X]
      exact PowerSeries.X_prime.not_unit
    have hC : ∀ x, x ≠ 0 → IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) (PowerSeries.C x)) := fun x hx => by
      rw [PowerSeries.map_C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 hx)).map _
    have hV := cdvr_powerSeries (FractionRing O')
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT hV _
      (PowerSeries.map_injective _ hi) hX hC
    obtain ⟨t, ⟨m⟩⟩ := exists_sab χ Y.t
    have hS := GlobalTheory.splitOver_of_hasArcData h₁ h₂ h₃ hH E H D l Xo c W₀ Y O' b a hd χ t m (by
      have e : (PowerSeries.map (algebraMap O' (FractionRing O'))).comp (PowerSeries.C (R := O')) =
          (PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _) := RingHom.ext fun x => PowerSeries.map_C (algebraMap O' (FractionRing O')) x
      rw [e, PowerSeries.map_X] at h
      exact h)
    obtain ⟨hadm, hpid⟩ := powerSeries_dvr_admissible_X_ideal O' (hϖ.maximalIdeal_eq ▸ hc)
    obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H _ _ hadm hpid t (polAt_of_point Y m _ _ hχ.symm) hS
      (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp _ _ t m)
    have := hadm.2.2.1
    refine GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a _ _ _ _ hadm.1 hadm.2.2.2.1.ne_top
      PowerSeries.C_injective _ _ hχ.symm t m P hPt _ hV _ (PowerSeries.map_injective _ hi) ?_ hX hC h
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hX

end GlobalTheory.ArcData
end
end
