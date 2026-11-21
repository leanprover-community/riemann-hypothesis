import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationEqOfIsLocGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

theorem locMod_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  intro E _ _ _ H Dw l Xo c _ z T iK
  refine ⟨fun h => ?_, fun M T' ψ i hψ => ?_⟩
  · have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
    let ρ : 𝓞 z.K →+* T.V := e.symm.toRingHom.comp
      ((iK.comp (algebraMap (𝓞 z.K) z.K)).codRestrict (algebraMap T.V T.Fr).range fun a => h a)
    have hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K) := by
      ext a
      exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h a⟩)
    obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ρ z.B).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ iK z.Φ.T).1
    obtain ⟨m1, h1⟩ := sab_comp_exists n' z.Φ.m _ rfl
    obtain ⟨k, hk⟩ := sab_comp_exists n' z.m' _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T.V T.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hρ])
    exact ⟨⟨ρ, hρ, G, t', n, n', m1, m2, h1, h2.trans hk⟩⟩
  · obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ψ M.G).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ i M.t').1
    obtain ⟨N, hN⟩ := sab_comp_exists n M.n _ (spectrumMap_comp M.ρ ψ)
    obtain ⟨N', hN'⟩ := sab_comp_exists n' M.n' _ (spectrumMap_comp iK i)
    obtain ⟨m1, h1⟩ := sab_comp_exists n' M.m1 (spMap (i.comp iK) ≫ z.x)
      (by rw [spectrumMap_comp, Category.assoc])
    obtain ⟨k, hk⟩ := sab_comp_exists n' M.m2 _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T'.V T'.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hψ])
    refine ⟨⟨ψ.comp M.ρ, ?_, G, t', N, N', m1, m2, ?_, ?_⟩, n, n', h1, h2.trans hk⟩
    · rw [← RingHom.comp_assoc, hψ, RingHom.comp_assoc, M.hρ, RingHom.comp_assoc]
    · rw [h1, hN', M.h1, Category.assoc]
    · rw [hN, hN', ← Category.assoc, h2, hk, Category.assoc, M.h2, Category.assoc]

end GlobalTheory.LamT
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPoint_localModel_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  atlas_forward_decl GlobalTheory.LamT.locMod_exists
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | exact GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | (intros; apply GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocGen

theorem fibre_ne_of_generates {R : Type} [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (θ : P.L.Sec)
    (h : ∀ σ : P.L.Sec, ∃ c : ∀ i, Γ(P.A.left, P.L.U i), ∀ i, σ.f i = c i * θ.f i) (s : Sp R) :
    ∃ q : P.A.left, P.A.hom q = s ∧ q ∈ Out.nonzeroLocus θ := by
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : IsPullback (𝟙 P.A.left) P.A.hom P.A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨th, hth⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨q, hq, hz⟩ := hth s
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  obtain ⟨c, hc⟩ := h ⟨fun j => (P.A.left.presheaf.map (homOfLE (fun y hy => mem_pull.2 hy :
      P.L.U j ≤ (P.L.pull (𝟙 P.A.left)).U (fun _ => j))).op).hom (th.f fun _ => j), fun j j' => fn_ext fun y hy => by
    have h₁ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j) := mem_pull.2 hy.1
    have h₂ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j') := mem_pull.2 hy.2
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat th (𝟙 _) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans ?_)
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
    rw [gm_pull_g P.L (𝟙 _) (𝟙 _) y _ _ h₁ h₂, Category.comp_id]⟩
  have hk' : q ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  refine ⟨q, hq, (mem_nonzeroLocus _ _).2 ⟨_, hk', ?_⟩⟩
  have e := congrArg (gs (𝟙 _) q _) (hc (k PUnit.unit))
  rw [gs_mul _ q _ hk'] at e
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_res (𝟙 _) q _ hk' _).symm.trans e)).mp u)

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    {v : Fin k → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin n => v (i.cast e) := by
  subst e; exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    (B : Matrix (Fin k) (Fin k) R) {v w : Fin k → (epsR R ⟶ G)} (h : ∀ i, IsLieComb (B i) v (w i)) (i : Fin n) :
    IsLieComb ((Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)) i) (fun i : Fin n => v (i.cast e))
      (w (i.cast e)) := by
  subst e; exact h i

theorem det_cast {R : Type} [CommRing R] {n k : ℕ} (e : n = k) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)).det = B.det := by
  subst e; rfl

theorem eps_sq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem stalk_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {θ : L.Sec} {θ' : (L.pull F).Sec} {σ : L'.Sec} (h : IsoMaps w σ θ') (hθ : PullSec F θ θ')
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  rw [← (TieCalc.isoMaps_iff w σ θ').1 h Z r z j k hj hk, hθ (fun _ => j) le, gs_appLE F _ _ le r z (mem_pull.2 hj)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem keyPB_of_sabMap {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {T : PAT H (Sp R)} {T' : PAT H (Sp R')}
    (m : SABMap T'.t T.t (spMap f)) {w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ)} (hw : RigIso m w) (hg : T'.g = T.g)
    {g₀ th hth v hv g₀' th' hth' v' hv'}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.t.G.left) (z : Z) j k, m.φ (r z) ∈ T.t.PP.L.U j → r z ∈ T'.t.PP.L.U k →
      gs (r ≫ m.φ) z _ (LB.Sec.f th j) = (gw w r z j k).val * gs r z _ (LB.Sec.f th' k))
    (hl : ∀ i, (v' i).left ≫ m.φ = spMap (Chart.dualMapR f) ≫ (v (i.cast hg)).left) :
    KeyPB ⟨T'.pol, g₀', T'.t.PP.rig, T'.t.PP.rigGen, th', hth', v', hv'⟩
      ⟨T.pol, g₀, T.t.PP.rig, T.t.PP.rigGen, th, hth, v, hv⟩ f := by
  have he : eSec T'.t.G ≫ m.φ = spMap f ≫ eSec T.t.G := PolBaseChange.eSec_comm m.cart
  have hr := (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm T.t.PP.L) (fun _ => rfl)).1 hw.2
  rw [m.base] at hr
  refine ⟨m.φ, he, w, hg, Chart.dualMapR f, m.cart, hw.1,
    (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig _ _ (rigPull_le m.φ _ he T.t.PP.L) (fun _ => rfl)).2 hr,
    KeyPow.appLE_eq_of_stalk _ th th' (hs _ (𝟙 _)), fun a => ?_, ?_, hl⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem eq_mul_of_secTie {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x x₀ : Sp S ⟶ Xo.X}
    {x₁ x₂ : Sp S' ⟶ Xo.X} {t : SAB H (Sp S)} {t' : SAB H (Sp S')} {m : SABMap t Xo.univ.t x}
    {m' : SABMap t' Xo.univ.t (spMap φ ≫ x)} {n : SABMap t' t (spMap φ)} (hφ : m'.φ = n.φ ≫ m.φ)
    {th : LB.Sec t.PP.L} {s₀ : LB.Sec (PPx x₀)} {s₁ : LB.Sec (PPx x₁)} {s₂ : LB.Sec (PPx x₂)} {a : S'}
    (e₀ : x₀ = x) (e₁ : x₁ = spMap φ ≫ x₀) (e₂ : x₂ = x₁) (h₀ : SecTie m th s₀) (b₁ : SecBC φ 1 x₀ x₁ s₀ s₁)
    (b₂ : SecBC (RingHom.id S') a x₁ x₂ s₁ s₂) {w : LB.Iso t'.PP.L (t.PP.L.pull n.φ)} (hw : RigIso n w)
    {th' σ : LB.Sec t'.PP.L}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j k, n.φ (r z) ∈ t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ n.φ) z _ (th.f j) = (gw w r z j k).val * gs r z _ (th'.f k))
    (h₂ : SecTie m' σ s₂) : ∀ i, σ.f i = constFn t'.G.hom _ a * th'.f i := by
  subst e₀ e₁
  have h₁ : SecTie m' th' s₁ :=
    (TieCalc.secTie_baseChange m h₀ φ m' n s₁ w (thfPull _ n.φ th) th' rfl hφ b₁ hw (fun _ _ => rfl)).2
      ((TieCalc.isoMaps_iff w _ _).2 fun Z r z j k hj hk =>
        (gs_appLE n.φ _ _ _ r z (mem_pull.2 hj) _).trans (hs Z r z j k hj hk))
  exact ((TieCalc.secTie_calc E H Dw l Xo S' _ t' m' th' s₁ h₁).1 a x₂ s₂ σ e₂ b₂).1 h₂

theorem integral_generator_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hT φ yT y' g a hφ hmap hchg hint ca hca
  obtain ⟨hobj, -, -, hx, htie, -⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := hobj
  obtain ⟨A, hA, hdet⟩ := hmod p
  obtain ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, hσ⟩ := hint
  obtain ⟨vV, bV, hV⟩ := exists_isLieBasis_locMod E H Dw l Xo c z p T iK M hT A hA
  obtain ⟨g1, -, w1, r1⟩ := (pat_pullback E H _ _ iK z.Φ.T).2 M.t' M.n' inferInstance
  obtain ⟨g2, -⟩ := (pat_pullback E H _ _ (algebraMap T.V T.Fr) M.G).2 M.t' M.m2 inferInstance
  have g3 : M.G.g = z.Φ.T.g := g2.symm.trans g1
  obtain ⟨th', hth'⟩ := sec_pull_down ((isGen_iff _).1 r1.1) z.Φ.T.t.PP.isLB M.t'.t.PP.isLB z.Φ.th
  have nz' := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hth' M.n'.cart.1 z.Φ.th_ne
  have nzθ := fibre_ne_of_generates M.G.pol θ fun τ => (hθ τ).exists.elim fun b hb => ⟨_, hb⟩
  have hσθ := stalk_of_isoMaps i2 p2
  have nzσ := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hσθ M.m2.cart.1 nzθ
  obtain ⟨v0, b0, h0⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ iK _ _ _ M.n'.cart z.Φ.T.ab.smooth _ z.Φ.v z.Φ.basis
  obtain ⟨v1, b1, h1⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ (algebraMap T.V T.Fr) _ _ _ M.m2.cart M.G.ab.smooth _ vV bV
  have hc : ∀ k, IsLieComb (iK.mapMatrix A k) v0 (v1 k) := fun k => by
    show IsLieComb (fun j => iK (A k j)) v0 (v1 k)
    obtain ⟨wK, hw, hw'⟩ := hV k
    refine Chart.comb_baseChange iK M.n'.cart hw h0 (z.m'.cart.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← M.h2, ← Category.assoc, h1, Category.assoc]
      exact hw'
    · rw [Category.assoc, Category.assoc, M.n'.cart.1.w, ← Category.assoc, Over.w, Over.w, eps_sq]
  have hσa : ∀ i, σ.f i = constFn M.t'.t.G.hom _ a * th'.f i := by
    obtain ⟨e₁, -, pm, ps, pf, hp⟩ := hmap
    rw [hφ] at e₁ pf
    refine eq_mul_of_secTie iK M.h1 hx e₁ hchg.1 htie ⟨pm, ps, pf, fun i h => ?_⟩ hchg.2.2 r1 hth' hσ
    rw [SecCalc.scal_one' z.y.x i, _root_.one_mul]
    exact hp i h
  have gp : 1 ≤ M.t'.g := g1 ▸ z.Φ.g_pos
  let x' : KeyIn T.Fr := ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, th', nz', _, isLieBasis_cast g1 b0⟩
  let xR : KeyIn T.V := ⟨M.G.pol, gp.trans g2.le, M.G.t.PP.rig, M.G.t.PP.rigGen, θ, nzθ, _, isLieBasis_cast g3 bV⟩
  have k1 : KeyPB x' z.Φ.key iK := keyPB_of_sabMap M.n' r1 g1 hth' fun i => h0 _
  have k2 : KeyPB ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, σ, nzσ, _, isLieBasis_cast g1 b1⟩ xR
      (algebraMap T.V T.Fr) := keyPB_of_sabMap M.m2 r2 g2 hσθ fun i => h1 _
  have k3 : KeyIntegral T.V x' a (iK A.det) :=
    ⟨σ, nzσ, _, isLieBasis_cast g1 b1, Matrix.of fun i j => iK.mapMatrix A (i.cast g1) (j.cast g1), xR, hσa,
      isLieComb_cast g1 (iK.mapMatrix A) hc, (det_cast g1 _).trans (RingHom.map_det iK A).symm, k2⟩
  exact KeyVal.integral_section_unit z.K z.Φ.key z.Tl z.LamL p (hloc p) T.V T.Fr iK x' a (iK A.det) ca A.det 1 hT
    k1 k3 hdet (by rw [Units.val_one, map_one, _root_.mul_one]) hca

end GlobalTheory.LamT.LocGen
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  atlas_forward_decl GlobalTheory.LamT.LocGen.integral_generator_unit
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LieIntBC

open Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg tvec_tmap fB IsUnivChart sp JetR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem flat_of_inj {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B] [Algebra A B]
    (hi : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : algebraMap A B a * x = 0 := (Algebra.smul_def a x).symm.trans hx
  have ha' : algebraMap A B a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem eig_flat {V V' : Type} [CommRing V] [IsNoetherianRing V] [CommRing V'] [Algebra V V'] [Module.Flat V V']
    {n m : ℕ} {J : Type} (L : J → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : J → V)
    (L' : J → (Fin n → V') →ₗ[V'] (Fin n → V'))
    (hL : ∀ a c, L' a (algebraMap V V' ∘ c) = algebraMap V V' ∘ L a c)
    (b : Fin m → Fin n → V) (hb : ∀ k a, L a (b k) = χ a • b k)
    (hbb : ∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ k, r k • b k)
    (w : Fin n → V') (hw : ∀ a, L' a w = algebraMap V V' (χ a) • w) :
    ∃! r : Fin m → V', w = ∑ k, r k • (algebraMap V V' ∘ b k) := by
  let M : J → Matrix (Fin n) (Fin n) V := fun a => Matrix.of fun j => L a (Pi.single j 1)
  have hM : ∀ a c, c ᵥ* M a = L a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (fun q => c k * L a q j) ?_
    funext s
    simp [Pi.single_apply, eq_comm]
  have hM' : ∀ a c, c ᵥ* (M a).map (algebraMap V V') = L' a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L' a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine (congrFun (hL a (Pi.single k 1)) j).symm.trans ?_
    refine congrArg (fun q => L' a q j) ?_
    funext s
    by_cases h : k = s <;> simp [Pi.single_apply, h, eq_comm]
  refine (GlobalTheory.commonEigenvectors_flat_baseChange V J n m M χ).1 V b (fun k a => (hM a _).trans (hb k a))
    (fun z hz => ?_) V' w (fun a => (hM' a w).trans (hw a))
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  exact hbb z fun a => (hM a z).symm.trans (hz a)

theorem univChart_iso {S : Type} [CommRing S] {G G' : Over (Spec (CommRingCat.of S))} [GrpObj G] [GrpObj G']
    (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_charts {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {G₀ : Over (Sp R)} [GrpObj G₀]
    [Smooth G₀.hom] {G : Over (Sp S)} [GrpObj G] (f : R →+* S) {φ : G.left ⟶ G₀.left}
    (h : IsGrpPullback G G₀ (spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G₀) (x' : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G),
      IsUnivChart G₀ n x ∧ IsUnivChart G n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (f ∘ c)).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (tvec (x := x) c).left := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', hc⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  refine ⟨n, x, _, hx, univChart_iso e hx', fun c => ?_⟩
  have e1 : tvec (x := fun m => x' m ≫ e.inv) (f ∘ c) = tvec (x := x') (f ∘ c) ≫ e.inv := (Category.assoc _ _ _).symm
  rw [e1, ← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
  exact hc c

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (g : R →+* S) :
    spMap (Formalism.L2.Pj.dualMap f) ≫ spMap (Formalism.L2.Pj.dualMap g) = spMap (Formalism.L2.Pj.dualMap (f.comp g)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun s => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

end GlobalTheory.LamT.LieIntBC

namespace GlobalTheory.LamT

open LieIntBC Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec tvec_tmap)

theorem lieInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  intro E _ _ _ H Dw l Xo c T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 io u hu
  obtain ⟨ub, ht, he, hb, hu⟩ := hu
  have := G.t.semi.smooth
  have : ∀ a, IsMonHom (G.t.act.act a) := G.t.act.hom
  have : ∀ a, IsMonHom (G'.t.act.act a) := G'.t.act.hom
  have hψ' : ∀ z, algebraMap T'.V T'.Fr (ψ z) = i (algebraMap T.V T.Fr z) := fun z => RingHom.congr_fun hψ z
  have hinj : Function.Injective ψ := fun a b hab =>
    IsFractionRing.injective T.V T.Fr (i.injective (by rw [← hψ', ← hψ', hab]))
  let _ := ψ.toAlgebra
  have : Module.Flat T.V T'.V := flat_of_inj hinj
  obtain ⟨N, xc, xc', hxc, hxc', hcomp⟩ := exists_charts ψ n.cart
  have hM : ∀ (a : 𝓞 E) (cc : Fin N → T.V),
      tmap hxc' (G'.t.act.act a) (ψ ∘ cc) = ψ ∘ tmap hxc (G.t.act.act a) cc := by
    intro a cc
    apply tvec_inj hxc'
    rw [tvec_tmap hxc']
    refine Over.OverMorphism.ext (n.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hcomp, tvec_tmap hxc, Over.comp_left, Over.comp_left, Category.assoc, n.act, ← Category.assoc, hcomp,
      Category.assoc]
  choose χ hχ using fun τ a => int_val c T io τ a
  have hχ' : ∀ τ a, algebraMap T'.V T'.Fr (ψ (χ τ a)) = (i.comp io) (embK c τ a) := fun τ a => by
    rw [hψ', hχ]; rfl
  have eig : ∀ τ cc, IsEigV c io G.t τ (cvV (tvec (x := xc) cc)) ↔
      ∀ a, tmap hxc (G.t.act.act a) cc = χ τ a • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc _ cc _).1 (h a _ (hχ τ a)), fun h a z hz => by
      obtain rfl : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      exact (eigV_iff hxc _ cc _).2 (h a)⟩
  have eig' : ∀ τ cc, IsEigV c (i.comp io) G'.t τ (cvV (tvec (x := xc') cc)) ↔
      ∀ a, tmap hxc' (G'.t.act.act a) cc = ψ (χ τ a) • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc' _ cc _).1 (h a _ (hχ' τ a)), fun h a z hz => by
      obtain rfl : z = ψ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (hz.trans (hχ' τ a).symm)
      exact (eigV_iff hxc' _ cc _).2 (h a)⟩
  choose b hbe using fun τ k => tan_eq_cvV hxc (ht τ k)
  obtain rfl : ub = fun τ k => cvV (tvec (x := xc) (b τ k)) := funext fun τ => funext fun k => hbe τ k
  have hbe' : ∀ τ k a, tmap hxc (G.t.act.act a) (b τ k) = χ τ a • b τ k := fun τ k => (eig τ _).1 (he τ k)
  refine ⟨fun τ k => cvV (tvec (x := xc') (ψ ∘ b τ k)), fun τ k => isTan_cvV (isTan_tvec hxc' _),
    fun τ k => (eig' τ _).2 fun a => ?_, fun τ w hw hwe => ?_, fun τ k => ?_⟩
  · rw [hM, hbe']
    funext j
    simp
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc' hw
    simp only [comb_iff hxc']
    refine eig_flat (fun a => tmap hxc (G.t.act.act a)) (χ τ) (fun a => tmap hxc' (G'.t.act.act a)) hM (b τ)
      (hbe' τ) (fun z hz => ?_) cc ((eig' τ cc).1 hwe)
    have := hb τ _ (isTan_cvV (isTan_tvec hxc z)) ((eig τ z).2 hz)
    simpa only [comb_iff hxc] using this
  · obtain ⟨u', hu1, hu2⟩ := hu τ k
    have w0 : u' ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) := by
        have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) :=
          IsLocalization.epi (nonZeroDivisors T.V) T.Fr
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)).op))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      erw [hu2]
      rw [Category.assoc, Over.w]
      exact dual_alg _
    have w1 : (spMap (Formalism.L2.Pj.dualMap i) ≫ u') ≫ t.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap i := by
      rw [Category.assoc, w0, dual_alg]
    have l1 : n'.cart.1.lift _ _ w1 ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap i) ≫ u' := n'.cart.1.lift_fst _ _ _
    have l2 := n'.cart.1.lift_snd _ _ w1
    refine ⟨n'.cart.1.lift _ _ w1, ?_, n.cart.1.hom_ext ?_ ?_⟩
    · rw [h1, ← Category.assoc, l1, Category.assoc, hu1]
    · change (_ ≫ m2'.φ) ≫ n.φ = (_ ≫ _) ≫ n.φ
      rw [Category.assoc, h2, ← Category.assoc, l1, Category.assoc, hu2, cvV_left, cvV_left, Category.assoc, hcomp,
        ← Category.assoc, ← Category.assoc, dual_comp, dual_comp, hψ]
    · rw [Category.assoc, m2'.cart.1.w, ← Category.assoc, l2, Category.assoc, Over.w]
      exact (dual_alg _).symm

end GlobalTheory.LamT
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eigenbasis_baseChange_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  atlas_forward_decl GlobalTheory.LamT.lieInt_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem secInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  intro E _ _ _ H Dw l Xo T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hb
  rintro ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, tie⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨wn, gn, rn, -⟩ := n.lin
  obtain ⟨wn', gn', rn', -⟩ := n'.lin
  obtain ⟨w2', g2', r2', -⟩ := m2'.lin
  have Rn : RigIso n wn := ⟨gn, rn⟩
  have Rn' : RigIso n' wn' := ⟨gn', rn'⟩
  have R2' : RigIso m2' w2' := ⟨g2', r2'⟩
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff wn).1 gn) G.t.PP.isLB G'.t.PP.isLB θ
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2').1 g2') G'.t.PP.isLB t'.PP.isLB θ'
  have nz : ∀ y : Sp T.V, ∃ z : G.t.G.left, G.t.G.hom z = y ∧ z ∈ Out.nonzeroLocus θ := fun y => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hS G.pol
    obtain ⟨z, hz, hm⟩ := hb y
    obtain ⟨a, ha, -⟩ := hθ b
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    rw [ha k, Scheme.basicOpen_mul] at hk
    exact ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk.2⟩⟩
  have nz' := SectionBaseChange.fibre_nonzero_of_pull G'.t.PP.isLB hθ' n.cart.1 nz
  refine ⟨θ', SectionBaseChange.generates hS G.pol n.cart.1 G'.t.PP.isLB ⟨wn, gn⟩ θ' nz', w2', σ',
    thfPull G'.t.PP.L m2'.φ θ', R2', ?_, fun _ _ => rfl, ?_⟩
  · refine (TieCalc.isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_
    exact (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans (hσ' Z r z j k hj hk)
  · refine (TieCalc.secTie_baseChange m1 tie i m1' n' s' wn' (thfPull t.PP.L n'.φ σ) σ' hx h1 hb Rn'
      (fun _ _ => rfl)).2 ((TieCalc.isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_)
    have hbase : spMap (algebraMap T'.V T'.Fr) ≫ spMap ψ = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    obtain ⟨N, hN⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m2'
    have hN' : N.φ = m2'.φ ≫ n.φ := hN
    obtain ⟨wa, ra, Ta⟩ := GlobalTheory.LiftBaseChange.rigIso_comp n m2' N rfl hN' Rn R2'
    obtain ⟨wb, rb, Tb⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m2 n' N hbase (hN'.trans h2) r2 Rn'
    have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m2'.cart.1 G'.ab.proper
    have hab : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩
    obtain rfl : wa = wb := iso_unique_of_rig GlobalTheory.globalFns_holds t'.G hab t'.PP.isLB G.t.PP.isLB ra.1 rb.1 ra.2 rb.2
    obtain ⟨a, ha⟩ := exists_chart G.t.PP.isLB (m2.φ (n'.φ (r z)))
    obtain ⟨b, hb'⟩ := exists_chart G'.t.PP.isLB (m2'.φ (r z))
    have ha' : n.φ (m2'.φ (r z)) ∈ G.t.PP.L.U a := (congrArg (fun q => q (r z) ∈ G.t.PP.L.U a) h2).mpr ha
    have e1 := hθ' Z (r ≫ m2'.φ) z a b ha' hb'
    have e2 := hσ' Z r z b k hb' hk
    have le : (G.t.PP.L.pull m2.φ).U (fun _ => a) ≤ m2.φ ⁻¹ᵁ G.t.PP.L.U a := fun q hq => mem_pull.1 hq
    have e3 := (TieCalc.isoMaps_iff _ _ _).1 i2 Z (r ≫ n'.φ) z a j ha hj
    rw [p2 (fun _ => a) le, gs_appLE m2.φ _ _ le (r ≫ n'.φ) z (mem_pull.2 ha), Category.assoc, ← h2,
      ← Category.assoc, e1, e2, ← _root_.mul_assoc, ← Units.val_mul, ← Ta Z r z a b k ha' hb' hk,
      Tb Z r z a j k ha hj hk, Units.val_mul, _root_.mul_assoc] at e3
    exact (gs_appLE n'.φ _ _ _ r z (mem_pull.2 hj) _).trans ((Units.mul_right_inj _).1 e3).symm

end GlobalTheory.LamT
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_generator_baseChange_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  atlas_forward_decl GlobalTheory.LamT.secInt_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

noncomputable section

namespace GlobalTheory.LamT

theorem mem_range_of_nval_nonneg {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ Formalism.L2.Pj.nval V e x) :
    x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [map_zero, hx]⟩
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ vV V x := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  have h3 : valV V x ≤ 1 := by
    refine (WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero).1 ?_
    simp only [WithZero.log_one]
    simp only [vV] at h2
    omega
  exact IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K') h3

theorem evR_mem_range_of_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c F hF T io hT y hy
  let := io.toAlgebra
  obtain ⟨la, e, ho⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T io hT
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T.Fr y
  have h := hF la _ ⟨PtV.mk (cls := algCls Xo c) la ho ⟨y, ht, hy⟩ hT () trivial, rfl⟩
  exact mem_range_of_nval_nonneg ho.1 h

end GlobalTheory.LamT
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  atlas_forward_decl GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocClause

theorem exists_isLocGen {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨π ^ FractionalIdeal.count K p I, (GlobalTheory.LamF.isLocGen_iff_valuation_eq p _ _).2 ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

theorem map_evalFr {B : Type} {m : B → ℕ} {R S : Type} [CommRing R] [CommRing S] (κ : R →+* S)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    κ (evalFr P Y) = evalFr (MvPolynomial.map κ P) (fun b => (Y b).map κ) := by
  unfold evalFr
  induction P using MvPolynomial.induction_on <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem secBC_one_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {y' : FrPt Xo c T} (h : FrMap φ y y') : SecBC φ.toRingHom 1 y.x y'.x y.s y'.s := by
  obtain ⟨-, -, pm, h₁, h₂, h₃⟩ := h
  refine ⟨pm, h₁, h₂, fun i hi => Eq.trans (congrArg _ ?_) (h₃ i hi)⟩
  have h1 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
    (by simp [spMap]) (by simp [spMap])).2.2.2 1 1 i).2.2
  rw [h1, _root_.one_mul]

theorem evR_scale {S : Type} [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c}
    (hF : F ∈ sec Xo c a n) (s : Sˣ) {y y' : FrPt Xo c S} (h : FrChg (fun _ => 1) (s : S) y y') :
    evR Xo c F y' = (s : S) ^ n * evR Xo c F y := by
  let t : Ix Dw → Sˣ := fun i => i.elim s (fun _ => 1)
  have hb : FrBor t y y' := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], h⟩
  rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S inferInstance a n F hF t y y' hb]
  congr 1
  simp [wchar, Fintype.prod_option, t, ex]

theorem integral_of_eq (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    y.x = x → ∀ (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro h
  subst h
  exact integral_of T io y

theorem secInt_baseChange (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr))
    {x x₁ : Sp T.Fr ⟶ Xo.X} {x' x₁' : Sp T'.Fr ⟶ Xo.X} {G : PAT H (Sp T.V)} {G' : PAT H (Sp T'.V)}
    {t : SAB H (Sp T.Fr)} {t' : SAB H (Sp T'.Fr)} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ))
    (n' : SABMap t' t (spMap i)) (hx : x' = spMap i ≫ x) (h1 : m1'.φ = n'.φ ≫ m1.φ)
    (h2 : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (e : x₁ = x) (e' : x₁' = x') (s : LB.Sec (PPx x₁)) (s' : LB.Sec (PPx x₁'))
    (hs : SecBC i 1 x₁ x₁' s s') (h : SecInt T m1 m2 s) : SecInt T' m1' m2' s' := by
  subst e e'
  exact GlobalTheory.T.integral_generator_baseChange_valuationRing E H Dw l Xo T T' ψ i hψ _ _ G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hs h

theorem integral_baseChange_chg [StarRing (𝓞 E)] (z : CMPt Xo c) (T T' : CDVR) (iK : z.K →+* T.Fr)
    (M : LocMod z T iK) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr)) (io : c.F →+* T.Fr) :
    letI := io.toAlgebra
    letI := (i.comp io).toAlgebra
    ∀ (iA : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' w : FrPt Xo c T'.Fr)
      (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T'.V),
      iA.toRingHom = i → y.x = spMap iK ≫ z.x → LieInt T io M.m1 M.m2 y.u → SecInt T M.m1 M.m2 y.s →
      FrMap iA y y' → (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T'.V T'.Fr)) 1 y' w →
      Integral T' (i.comp io) w := by
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  intro iA y y' w X hi hy hL hS hm hX hw
  obtain ⟨M', n, n', h1, h2⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).2 M T' ψ i hψ
  have hx : spMap (i.comp iK) ≫ z.x = spMap i ≫ spMap iK ≫ z.x := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]
  have hy' : y'.x = spMap (i.comp iK) ≫ z.x := by rw [hm.1, hi, hy, hx]
  have hL' : LieInt T' (i.comp io) M'.m1 M'.m2 y'.u := by
    have := GlobalTheory.T.integral_eigenbasis_baseChange_dvr E H Dw l Xo c T T' ψ i hψ _ _ M.G M'.G M.t'.t M'.t'.t M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2
      io y.u hL
    have hu : y'.u = fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ y.u τ k := by
      funext τ k
      rw [hm.2.1 τ k, hi]
    rw [hu]
    exact this
  have hLw : LieInt T' (i.comp io) M'.m1 M'.m2 w.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T' (i.comp io) M'.G.t M'.t'.t _ M'.m1 M'.m2 y' hy').2 hL' X 1 w hX hw
  have hs1 : SecBC i 1 y.x y'.x y.s y'.s := by
    have := secBC_one_of_frMap hm
    rwa [hi] at this
  have hs2 : SecBC i 1 y.x w.x y.s w.s := by
    have := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo _ _ _ i (RingHom.id _) y.x y'.x w.x
      (by rw [hm.1, hi]) (by rw [hw.1]; simp [spMap])).1 1 _ _ _ hs1).1 hw.2.2
    rwa [RingHom.id_comp] at this
  have hwx : w.x = spMap (i.comp iK) ≫ z.x := hw.1.trans hy'
  exact integral_of_eq T' (i.comp io) w hwx M'.m1 M'.m2 hLw
    (secInt_baseChange T T' ψ i hψ M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2 hy hwx _ _ hs2 hS)

theorem evR_chg {K S : Type} [Field K] [Algebra c.F K] [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {y₀ : FrPt Xo c K} {G : MvPolynomial (FrVar Dw.mult) K}
    (hG : IsFrPoly F y₀ G) (φ : K →ₐ[c.F] S) {y y' w : FrPt Xo c S} (hy : FrMap φ y₀ y)
    {g X Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S} {s : S} (hs : s ≠ 0)
    (hY : ∀ b, IsUnit (Y b).det) (hXY : ∀ b, (Y b).transpose = X b * g b)
    (h : FrChg g s y y') (hw : FrChg X 1 y' w) :
    evR Xo c F w = s ^ n * evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact hY b
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S w₀ (fun _ => 1) (Units.mk0 s hs)
    (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' w).2 _ _ _ _ h hw
  have e : w₁ = w := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) (Units.mk0 s hs) hYt).unique
      ?_ ?_
    · simpa using c1
    · simpa [hXY] using c2
  rw [← e, evR_scale hF _ hw₁, hG S φ y w₀ Y hY hy hw₀]
  rfl

theorem step5Loc_cmPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F hF hv G hG p
  obtain ⟨ca, hca⟩ := exists_isLocGen p z.Tl.I
  obtain ⟨cd, hcd⟩ := exists_isLocGen p z.LamL.I
  choose cl hcl using fun j => exists_isLocGen p (z.ℓ j).I
  refine ⟨ca⁻¹, cd, cl, isLocGen_inv hca, hcd, hcl,
    GlobalTheory.LamF.letters_det_valuation_le E H l c _ _ f z.obj La hz.1 z.letters hz.2.1 p cd cl hcd hcl, ?_⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS ca hca
  refine ⟨T.V, T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iK,
    fun b => (g b)⁻¹, inferInstance, hT, hiK, fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero,
    fun b j k => GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j k _ (hcl _), ?_⟩
  intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
  have hinj : Function.Injective (algebraMap T.V W) := by
    intro x y h
    apply IsFractionRing.injective T.V T.Fr
    apply fW.injective
    rw [hfW, hfW, h]
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let T' : CDVR := ⟨W⟩
  let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
  have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
    (FractionRing.algEquiv W KW).symm.commutes w
  let i : T.Fr →+* T'.Fr := κ.comp fW
  have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
    ext x
    show _ = κ (fW _)
    rw [hfW, hκ]
    rfl
  letI := (i.comp io).toAlgebra
  let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
  obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g s hy' hyW).1 hy''
  have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
    rw [Matrix.det_transpose]; exact hX b
  have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
    have := (hXt b).map (algebraMap T'.V T'.Fr)
    rwa [RingHom.map_det] at this
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
  have hint := integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
    (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
  have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
    rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hg b)]
    simp
  have hYX' : ∀ b, ((Y b).map κ).transpose =
      ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
    rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
    congr 1
    ext j k
    exact hκ _
  have hYu : ∀ b, IsUnit ((Y b).map κ).det := fun b => by
    rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
    refine (hXu b).mul ?_
    have := (hg b).map i
    rwa [RingHom.map_det] at this
  have hval := evR_chg hF hG (iA.comp φ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW)
    ((map_ne_zero iA).2 s.ne_zero) hYu hYX' hc hw
  refine ⟨algebraMap T.V W ↑u⁻¹ ^ n * w₀, κ.injective ?_⟩
  have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.map iK G)) =
      MvPolynomial.map (iA.comp φ).toRingHom G := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    rfl
  have hsn : (iA s : T'.Fr) ≠ 0 := (map_ne_zero iA).2 s.ne_zero
  have hu' : κ (fW (iK ca⁻¹)) * κ (algebraMap W KW (algebraMap T.V W ↑u⁻¹)) * iA s = 1 := by
    rw [← hfW]
    show i _ * i _ * i _ = 1
    rw [← map_mul, ← map_mul, hu, map_inv₀, _root_.mul_mul_mul_comm, inv_mul_cancel₀ ((map_ne_zero iK).2 hca.1),
      ← map_mul, Units.inv_mul, map_one, _root_.one_mul, map_one]
  rw [map_evalFr, hP]
  simp only [map_mul, map_pow]
  rw [hκ w₀, hw₀, hval, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow, hu', one_pow, _root_.one_mul]

end GlobalTheory.LamT.LocClause
end
