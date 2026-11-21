import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LiftValuationIntegralNorm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.GenericFibre

theorem lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem unif_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ∧
      LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) ∧
      (letI := H.starRing; ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
        P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left) := by
  letI := H.starRing
  have := P.U.gen_hom
  refine ⟨?_, ?_, fun a => ?_⟩
  · have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
      have h := P.U.ext
      rw [P.bundle] at h
      exact h
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (Geo.Tor.chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (Geo.Tor.chartPullUnpull P.A.L _ hgi)
      (Geo.Tor.chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  · have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem fibre_eq_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c O _ β Y R _ _ I t χ m P F _ _ y hy o φ₀ hφ₀ hL₀ ha₀
  letI := H.starRing
  obtain ⟨g₁, l₁, a₁⟩ := unif_generic P
  set ψ := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hψ
  have g₂ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (ψ ≫ m.φ) := g₁.comp m.cart
  have g₃ : IsGrpPullback o.P.A Y.t.G (jFK (R := R) F ≫ jK R ≫ χ) (φ₀ ≫ Y.m.φ) :=
    (hφ₀.comp Y.m.cart).congr hy rfl
  have w₁ : (φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = (o.P.A.hom ≫ jFK (R := R) F) ≫ jK R ≫ χ :=
    g₃.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨φ, e₁, e₂⟩ : ∃ φ : o.P.A.left ⟶ P.A.A.left, φ ≫ ψ ≫ m.φ = φ₀ ≫ Y.m.φ ∧
      φ ≫ P.A.A.hom = o.P.A.hom ≫ jFK (R := R) F :=
    ⟨g₂.1.lift _ _ w₁, g₂.1.lift_fst _ _ _, g₂.1.lift_snd _ _ _⟩
  have lm : LBIso t.PP.L (Y.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have lY : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := by
    obtain ⟨w, hw, -⟩ := Y.m.lin
    exact ⟨w, hw⟩
  have l₂ : LBIso P.A.L (Y.t.PP.L.pull (ψ ≫ m.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) l₁ (lbIso_pull lm ψ rfl)
  have l₃ : LBIso o.P.L (Y.t.PP.L.pull (φ₀ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL₀ (lbIso_pull lY φ₀ rfl)
  refine ⟨φ, g₂.cancel (g₃.congr rfl e₁.symm) e₂,
    LBIso.trans o.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB P.A.isLB _) l₃ (lbIso_pull l₂ φ e₁.symm).symm,
    fun x => g₂.1.hom_ext ?_ ?_, ?_⟩
  · have a₂ : (P.oA.act x).left ≫ ψ = ψ ≫ (t.act.act x).left := (a₁ x).trans (Category.assoc _ _ _).symm
    have a₃ : (P.oA.act x).left ≫ ψ ≫ m.φ = (ψ ≫ m.φ) ≫ (Y.t.act.act x).left := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) a₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (ψ ≫ ·) (m.act x)).trans (Category.assoc _ _ _).symm)))
    have a₄ : (o.oa.act x).left ≫ φ₀ ≫ Y.m.φ = (φ₀ ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
      rw [← Category.assoc, ha₀ x, Category.assoc, Category.assoc]
      exact congrArg _ (Y.m.act x)
    rw [Category.assoc, e₁, a₄, Category.assoc φ, a₃, ← Category.assoc φ, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [← e₁, hψ, Category.assoc]

end GlobalTheory.Ex.GenericFibre
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  first | exact @GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | exact GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | (intros; apply GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem exists_pelUnif_baseChange : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  intro h1 h3 h4 h5 E _ _ _ H R R' _ _ _ _ I I' hR hR' g hg hI t P
  obtain ⟨t', m₀, P', hD, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5
    hR hR' t P g hg hI
  have := hD.e_hom
  exact ⟨t', m₀, P', hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g),
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback P.D.toPre.P.A (specOf g))).congr
      (Category.id_comp _) rfl⟩

end GlobalTheory.Ex.Trait
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_baseChange_admissible : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  atlas_forward_decl GlobalTheory.Ex.Trait.exists_pelUnif_baseChange
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_extension_torsion_rational : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  first | exact @GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | exact GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | (intros; apply GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.IsoValCocycle
open GlobalTheory.TorusExt GlobalTheory.IsoValConst

theorem exists_th_ne_zero (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type}
    [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) {n : ℕ} (hn : 2 ≤ n)
    (hF : (n : F) ≠ 0) (a : N.A) : ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0 := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  obtain ⟨th, ρ, hth, hv⟩ := ThetaInValues.exists_th ν y
  obtain ⟨x, hx, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P (jFK (R := R) F ≫ jK R) hn hF th
    (ThetaCoset.ne_zero_of_isGenSec hL₂.secBaseChangeAny D.P _ hth) (ν.eA a)
  obtain ⟨t, rfl⟩ := ν.eA.surjective x
  refine ⟨t, ν.eA.injective (by rw [map_pow, map_one]; exact hx), fun h => ?_⟩
  have q := hu y ν.J (ThetaInValues.good ν y)
  have e := hv (a * t)
  rw [h, MulZeroClass.zero_mul, map_zero, map_mul] at e
  exact not_isUnit_zero ((congrArg IsUnit e).mp q)

theorem cocycle_eq_val : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  intro hL hL₂ R O' _ _ _ _ _ _ f P D₀ C _ _ _ _ _ hf N' N ν' ν ψ w I gp hw he
  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) C).hom ≫ spMap f = (TF (R := O') C).hom := ArcTransport.base_comm fun r => (hf r).symm
  have hp : ∀ x : N.A, ArcTransport.pushF gp hT (ν'.eA (I.φ x)) = ν.eA x := fun x => Over.OverMorphism.ext (he x)
  have hW : ∀ x : N'.A, stalkConst z (wVal ν' ν w x) = (ArcTransport.wVal w z ν.J ν'.J (ν'.eA x)).val := fun x =>
    toStk_valF (ν'.eA x).left ((D₀.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA x).left ≫ ψ)) ⊓ P.P.L.U (ν'.J (ν'.eA x).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA x).left ≫ ψ)), hJ' _⟩ _
  refine ⟨fun x h => ?_, ?_⟩
  · have := hW x
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  let Ω : N.A → ((Sp C).presheaf.stalk z)ˣ := fun x => ArcTransport.wVal w z ν.J ν'.J (ν'.eA (I.φ x))
  have hΩ : ∀ x, stalkUnits z (I.h x) * Ω x = stalkUnits z (I.h 1) * Ω 1 := by
    refine const_of_cube (fun x => stalkUnits z (I.h x) * Ω x) (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ 2
      (fun x => ?_) (exists_th_ne_zero hL hL₂ ν le_rfl (Nat.cast_ne_zero.2 two_ne_zero))
    · have e := ArcTransport.thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ hJ' (ν'.eA (I.φ a)) (ν'.eA (I.φ b))
        (ν'.eA (I.φ c))
      rw [hp, hp, hp, ← map_one ν'.eA, ← map_one I.φ, ← stalk_θ, ← stalk_θ] at e
      simp only [← map_mul ν'.eA, ← map_mul I.φ] at e
      have e₁ : stalkUnits z (N.θ a b c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
        Ω c * (Ω 1)⁻¹ * stalkUnits z (N'.θ (I.φ a) (I.φ b) (I.φ c)) := e
      have e₂ := congrArg (stalkUnits z) (I.θ_eq a b c)
      rw [I.h_one, map_one]
      clear_value Ω
      apply Additive.ofMul.injective
      replace e₁ := congrArg Additive.ofMul e₁
      replace e₂ := congrArg Additive.ofMul e₂
      simp only [map_mul, ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
      linear_combination (norm := abel) -e₁ - e₂
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 P.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D₀.P.A.left) (h := ψ) hw D₀.P.isLB P.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν.th
      obtain ⟨κ, hκ⟩ := sval_eq ν' z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 →
          ρ.val = (stalkUnits z (I.h a) * Ω a).val * (κ * stalkConst z I.lam * ρ'.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp C ⟶ _ from (ν'.eA (I.φ a)).left) hJ hJ'
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp C).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ.val = (Ω a).val * (κ * (stalkConst z (N'.th (I.φ a)) * ρ'.val)) :=
          (hρ a).trans ((congrArg (fun q => sval (Z := Sp C) ν.th q z ν.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ' _).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        rw [I.th_eq, Units.val_mul, Units.val_mul, stalkUnits_val, map_mul, map_mul]
        ring
      intro a b ha hb
      have hu : IsUnit (κ * stalkConst z I.lam * ρ'.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
    · obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D₀.P (jFK (R := O') C ≫ jK O') (ν.eA x) one_le_two
      exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  intro x
  apply (stalkConst z).injective
  have e := congrArg Units.val (hΩ x)
  rw [I.h_one, map_one, _root_.one_mul, Units.val_mul, stalkUnits_val] at e
  rw [map_mul, hW, hW, ← map_one I.φ]
  exact e

end GlobalTheory.IsoValCocycle
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  atlas_forward_decl GlobalTheory.IsoValCocycle.cocycle_eq_val
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.ActPt

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem equiv_parts {k : ℕ} {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') :
    ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g.b = p.g.b * DegPre.cF D F z := by
  obtain ⟨z, h₁, g, h₂, h₃⟩ := h
  exact ⟨z, h₁, by rw [h₃.1, h₂.1]; rfl⟩

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)

theorem mul_cF_act (x : O) (b : TF (R := R) F ⟶ D.P.A) (z : D.X) :
    (b * DegPre.cF D F z) ≫ oa.onB.act x = (b ≫ oa.onB.act x) * DegPre.cF D F (x • z) := by
  have := oa.onB.hom x
  rw [MonObj.mul_comp, DegPre.cF, DegPre.cF, oa.c_lin, Category.assoc]

theorem act_parts {k : ℕ} {x : O} {p p' : QkPt D F k} (h : QkAct oa x p p') :
    ∃ z : D.X, p'.y = x • p.y + k • z ∧ p'.g.b = (p.g.b ≫ oa.onB.act x) * DegPre.cF D F z := by
  obtain ⟨q, h₁, h₂, h₃⟩ := h
  obtain ⟨z, e₁, e₂⟩ := equiv_parts h₃
  exact ⟨z, by rw [e₁, h₁], by rw [e₂, h₂.1]⟩
end

theorem exists_image {C : Type} [CommRing C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, (TateInh.homOfIso J).Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  have e := hp k
  rw [N.mem_QT.1 p.2] at e
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), (h₁ _).unique e (h₃ _)⟩, rfl, hg⟩

theorem main : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  intro hL hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT k hk hlab hlin x y y' hy hy'
  letI := H.starRing
  obtain ⟨-, -, -, -, B⟩ := hB O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨t, t₁, -, t₃, -, t₅, -⟩ := hT C k hk
  have im : ∀ w : D.La, ∃ p' : QkPt M.P.D.toPre C k, (t p').left = (o.I.ev k w).left ≫ M.φ ∧
      p'.y = ν'.eX (J.e (A.q k w).1.1.toAdd) ∧ p'.g.b = ν'.eA (J.φ (A.q k w).1.2.b) := fun w => by
    obtain ⟨p, hp, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k w)
    obtain ⟨q, q₁, q₂⟩ := exists_image J p
    obtain ⟨p', hp'⟩ := (B' k).2.1 q
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev k w).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (t₁ _ _).1 (hlab w p q p' z hp q₁ q₂ hp' rfl)
    refine ⟨p', by rw [← hz]; rfl, ?_, ?_⟩
    · rw [← hp'.1, q₁, hp.1]; rfl
    · rw [← hp'.2.1, q₂.1]; exact congrArg (fun s => ν'.eA (J.φ s)) hp.2.1
  obtain ⟨gm, hγ, hγ'⟩ := QStr.root_over A.N hk.ne' 1 y hy
  obtain ⟨p₀, hp₀⟩ := (B k).2.1 ⟨(1, gm), hγ'.trans A.N.io_zero.symm⟩
  obtain ⟨v, hv⟩ := A.I.onto k hk p₀
  obtain ⟨z₀, -, e₀⟩ := equiv_parts hv
  obtain ⟨z₁, d₁, e₁⟩ := act_parts a.oa (A.I.lin k hk x v)
  obtain ⟨p₁, a₁, b₁, c₁⟩ := im v
  obtain ⟨p₂, a₂, b₂, c₂⟩ := im (x • v)
  obtain ⟨p₃, h₃⟩ := qkAct_exists hL.1.globalFns M.P.D.tau_bimult M.P.oD x p₁
  have e₃ : t p₃ = t p₂ := by
    rw [t₅ _ _ _ h₃]
    ext1
    rw [a₂, o.I.lin, Over.comp_left, Over.comp_left, a₁, Category.assoc, Category.assoc, M.act]
  have h₂ : QkAct M.P.oD x p₁ p₂ :=
    (TorusExt.qkAct_iff_of_equiv M.P.D.tau_bimult hL.1.globalFns M.P.oD (qk_equiv_refl M.P.D.tau_bimult p₁) h₃).2
      ((t₃ _ _).1 e₃)
  obtain ⟨z₂, d₂, e₂⟩ := act_parts M.P.oD h₂
  obtain ⟨w₀, rfl⟩ := A.ν.eX.surjective z₀
  obtain ⟨w₁, rfl⟩ := A.ν.eX.surjective z₁
  rw [← (A.hq k v).1, ← (A.hq k (x • v)).1] at d₁
  rw [← (A.hq k v).2.1, ← (A.hq k (x • v)).2.1] at e₁
  rw [← (A.hq k v).2.1, ← hp₀.2.1] at e₀
  rw [b₁, b₂] at d₂
  rw [c₁, c₂] at e₂
  generalize (A.q k v).1.1.toAdd = s₁ at d₁ d₂
  generalize (A.q k (x • v)).1.1.toAdd = s₂ at d₁ d₂
  generalize (A.q k v).1.2.b = β₁ at e₀ e₁ e₂
  generalize (A.q k (x • v)).1.2.b = β₂ at e₁ e₂
  let e : A.N.X ≃+ N'.X := J.e
  let φ : A.N.A ≃* N'.A := J.φ
  have hc : ∀ χ, N'.c (e χ) = φ (A.N.c χ) := J.c_eq
  let act : A.N.X → A.N.X := fun s => A.ν.eX.symm (x • A.ν.eX s)
  have hl : ∀ s, ν'.eX (e (act s)) = x • ν'.eX (e s) := hlin x
  have ha : ∀ s, A.ν.eX (act s) = x • A.ν.eX s := fun s => A.ν.eX.apply_symm_apply _
  change ν'.eX (e s₂) = x • ν'.eX (e s₁) + k • z₂ at d₂
  change ν'.eA (φ β₂) = ν'.eA (φ β₁) ≫ _ * _ at e₂
  change ν'.eA (φ y') = ν'.eA (φ y) ≫ _
  have g₁ : s₂ = act s₁ + k • w₁ := A.ν.eX.injective (by rw [d₁, map_add, map_nsmul, ha])
  have g₂ : z₂ = ν'.eX (e w₁) := by
    rw [g₁, map_add, map_add, map_nsmul, map_nsmul, hl, add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at d₂
    exact (smul_right_injective _ (Int.natCast_ne_zero.2 hk.ne') d₂).symm
  have g₀ : y = β₁ * A.N.c w₀ := A.ν.eA.injective (by rw [map_mul, A.ν.c_eq, ← e₀, hγ])
  have g₃ : y' * A.N.c w₁ = β₂ * A.N.c (act w₀) := A.ν.eA.injective (by
    rw [map_mul, map_mul, hy', g₀, map_mul, A.ν.c_eq, A.ν.c_eq, A.ν.c_eq, mul_cF_act, e₁, ha, mul_right_comm])
  have g₄ := congrArg (fun s => ν'.eA (φ s)) g₃
  simp only [map_mul, ← hc, ν'.c_eq, hl, e₂, ← g₂] at g₄
  rw [mul_right_comm, mul_left_inj] at g₄
  rw [g₄, g₀, map_mul, map_mul, ← hc, ν'.c_eq, mul_cF_act]

end GlobalTheory.Ex.ActPt
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  atlas_forward_decl GlobalTheory.Ex.ActPt.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem eq_of_comp_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g h.symm
  haveI : IsSeparated (Over.mk s).hom := ‹IsSeparated s›
  let d' : Over.mk (d ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  exact congrArg CommaMorphism.left ((cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g'))

theorem schemeDominant_spec_of_injective {A B : Type} [CommRing A] [CommRing B] [_root_.IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem act_comm_of_torsion : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  intro hL h₂ E _ _ _ H R _ _ _ S s B B₀ ρ ρ₀ ψ hψ hw C _ _ _ _ n hn x h
  letI := H.starRing
  obtain ⟨ρ', hρ'⟩ := polOActPull _ _ s B₀ B ψ hψ hw.symm (𝓞 E) ρ₀
  obtain ⟨P, g, hg, -, hm, ht⟩ := hL.polBaseChange _ _ (TF (R := R) C).hom B
  have gp : IsGrpPullback P.A B.A (TF (R := R) C).hom g := ⟨hg, fun T a b a₀ b₀ ha hb => by
    have e₁ : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
    have e₂ : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
    rw [e₁, e₂, ← hm]; rfl⟩
  obtain ⟨σ, hσ⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ
  obtain ⟨σ', hσ'⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ'
  obtain ⟨c, hc⟩ := exists_starNormLE_of_isCMField E (fun a => H.bar_eq a) x
  set j := 4 ^ P.g * P.g.factorial * (2 * c) with hj
  have hlt : j < (n ^ j) ^ 2 := (Nat.lt_pow_self hn).trans_le (Nat.le_self_pow two_ne_zero _)
  have key := h₂ P.g c (n ^ j) hlt C (Nat.cast_ne_zero.2 (by positivity)) P P rfl rfl (Iso.refl _)
    (ThetaPtDet.isPolIso_refl P) _ σ σ' x hc fun y hy => by
      let u : TF (R := R) C ⟶ Over.mk ((baseOver (Sp C)).hom ≫ (TF (R := R) C).hom) :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let z : TF (R := R) C ⟶ B.A := u ≫ pushHom gp _ y
      have hz : z.left = y.left ≫ g := Category.id_comp _
      have hz' : z ^ n ^ j = 1 := by
        rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
      have e := h j z hz'
      rw [← hρ', ← Category.assoc, ← Over.comp_left] at e
      have e' : (z ≫ ρ.act x).left = (z ≫ ρ'.act x).left := hψ.1.hom_ext e (by rw [Over.w, Over.w])
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left _ _ _ z, Over.comp_left _ _ _ z, hz] at e'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, hσ']
      simpa only [Category.assoc] using e'
  rw [Iso.refl_hom, Category.comp_id, Category.id_comp] at key
  haveI : IsSchemeTheoreticallyDominant (jK R) := schemeDominant_spec_of_injective _ (IsFractionRing.injective R _)
  haveI : IsSchemeTheoreticallyDominant (jFK (R := R) C) := schemeDominant_spec_of_injective _ (RingHom.injective _)
  haveI : IsSchemeTheoreticallyDominant (TF (R := R) C).hom := by
    show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI := B.isAb.proper
  haveI := B.isAb.smooth
  haveI : QuasiCompact (TF (R := R) C).hom := by
    show QuasiCompact (spMap (algebraMap (FractionRing R) C) ≫ spMap (algebraMap R (FractionRing R))); infer_instance
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  rw [← hρ', eq_of_comp_schemeDominant B.A.hom ((Over.w (ρ.act x)).trans (Over.w (ρ'.act x)).symm) g
    (by rw [← hσ, ← hσ', key])]

end GlobalTheory.Ex.Trait
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_pullback_line_bundle : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  atlas_forward_decl GlobalTheory.Ex.Trait.act_comm_of_torsion
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.FitMatch
open GlobalTheory.ArcPull GlobalTheory.ArcDataDescent

section General
variable {F F' : Type} [Field F] [Field F'] {B B₀ Y Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

theorem genRel_of_gauge {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) (hp : ∀ k, pt k ≫ φ = pt₀ k) (z : Sp F) {J J'} (hJ : Good M₀ z J)
    (hJ' : Good M z J')
    (H : (∏ k, om w z J J' (pt k) ^ ε k) * val t (𝟙 _) z J' = Units.map (toStk z).toMonoidHom x * val t₀ (𝟙 _) z J) :
    GenRel w t t₀ (x : F) := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H
  have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, Category.id_comp] at a
  have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
      Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀) := by
    rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul H
    simp only [om, ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact congrArg Units.val key

theorem genRel_ext_iff (hM : M.IsLB) (hM₀ : M₀.IsLB) (w : LB.Iso M (M₀.pull φ)) {K : Type} [Fintype K]
    {pt : K → (Y ⟶ B)} {pt₀ : K → (Y₀ ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (σ : F →+* F') (r : Sp F ⟶ Y) (r₀ : Sp F ⟶ Y₀)
    {s : Sp F' ⟶ Y} {s₀ : Sp F' ⟶ Y₀} (h : s = spMap σ ≫ r) (h₀ : s₀ = spMap σ ≫ r₀) (x : F) :
    GenRel w (LB.pullGen _ _ _ t s) (LB.pullGen _ _ _ t₀ s₀) (σ x) ↔
      GenRel w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x := by
  subst h h₀
  refine Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)
  have p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k := funext fun _ => Category.assoc _ _ _
  have p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k := funext fun _ => Category.assoc _ _ _
  refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r))
    (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀))
    (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ))
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) _)
    (DVR.pullGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₀ _) _)
    (fun y J hJ => ?_) (fun y J hJ => ?_) _ <;>
  rw [val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]

theorem toStk_vF {K : Type} [Fintype K] {pt : K → (Y ⟶ B)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (r : Sp F ⟶ Y)
    {z : Sp F} {J} (hJ : Good M z J) : toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem pt r) _
end General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}
  {f : R →+* R'} {C : Type} [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing R') C]

theorem tf_comp (hf : Along f C) : (TF (R := R') C).hom ≫ spMap f = (TF (R := R) C).hom :=
  (congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
    ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))

theorem c_of_field (hf : Along f C) {ψ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap f) ψ)
    (x : D'.X) (y : D.X) (h : (DegPre.cF D' C x).left ≫ ψ = (DegPre.cF D C y).left) :
    (D'.c x).left ≫ ψ = spMap f ≫ (D.c y).left := by
  have := D.P.isAb.proper
  let g : R' →+* C := (algebraMap (FractionRing R') C).comp (algebraMap R' _)
  have hg : Function.Injective g := (algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)
  have e : spMap g = (TF (R := R') C).hom := Geo.Tor.spMap_comp _ _
  refine ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
    D.P.A.hom ?_ ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))
  · rw [e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]
    exact h

theorem genRel_field (hf : Along f C) {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')
    {ψ : D'.P.A.left ⟶ D.P.A.left} (he : eSec D'.P.A ≫ ψ = spMap f ≫ eSec D.P.A) {w : LB.Iso D'.P.L (D.P.L.pull ψ)}
    (hw : w.IsGen) (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf ψ (spMap f) he D.P.L D.rig)) (x : N'.X) (y : N.X) (h s : Cˣ)
    (hc : (DegPre.cF D' C (ν'.eX x)).left ≫ ψ = (DegPre.cF D C (ν.eX y)).left)
    (hψ : N'.ψ x * h = N.ψ y * s) (hh : (h : C) * wVal ν' ν w (N'.c x) = wVal ν' ν w 1) :
    GenRel w (LB.pullGen _ _ _ (D'.psi (ν'.eX x)) (jFK (R := R') C)) (LB.pullGen _ _ _ (D.psi (ν.eX y)) (jFK (R := R) C))
      (s : C) := by
  have z : Sp C := (default : PrimeSpectrum C)
  have hJ : Good D.P.L z ν.J := fun p => (top_le_iff_mem _ _ z).1 (ν.good p)
  have hJ' : Good D'.P.L z ν'.J := fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)
  have hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val := fun a =>
    toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _
  have c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R := R) C ≫ D.xK a := fun a => Category.assoc _ _ _
  have c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R := R') C ≫ D'.xK a := fun a => Category.assoc _ _ _
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have e := pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at e
  replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e
  have a₀ := (congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))
  have a₁ := (congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))
  have a₂ := congrArg (toStk z) hh
  rw [map_mul, hv, hv, ν'.c_eq, c₁, map_one] at a₂
  let U := Units.map (toStk z).toMonoidHom
  have b₀ : U (N.ψ y) = _ * (_ * _) := Units.ext a₀
  have b₁ : U (N'.ψ x) = _ * _ := Units.ext a₁
  have b₂ : U h * _ = om w z ν.J ν'.J ((TF (R := R') C).hom ≫ eSec D'.P.A) := Units.ext a₂
  have b₃ := congrArg U hψ
  rw [map_mul, map_mul, b₀, b₁, ← b₂] at b₃
  refine genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s
    (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_
  rw [Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]
  have e' := congrArg Additive.ofMul b₃
  apply Additive.ofMul.injective
  simp only [U, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem match_of_fit : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  intro _ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e
    ⟨gp, hw, hp, hx, _, hh⟩ hr ha
  have hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left :=
    fun χ => by
      rw [← ν'.c_eq, ← A.ν.c_eq]
      exact (congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)
  have inj : Function.Injective f := fun x y h => IsFractionRing.injective O' (FractionRing O')
    ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))
  refine ⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    rw [hx]
    exact c_of_field hf gp _ _ (hc χ)
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    have k := genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ)
      ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))
    have lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L →
        jFK (R := O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h =>
      (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x =>
        (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans
        (Geo.Tor.spMap_comp _ _)
    have t := fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) =>
      genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ))
        (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK (R := M.W) L) (Category.comp_id _).symm (lift L h)
        (algebraMap M.W _ u₀ ^ (A.be.be χ χ / 2))
    rw [Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀] at k
    have k' := (t F fun x => (hF x).symm).2 ((t C hf).1 k)
    rw [hx, huF, ← A.be_eq, ← map_zpow₀]
    exact k'

end GlobalTheory.FitMatch
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  atlas_forward_decl GlobalTheory.FitMatch.match_of_fit
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait.LevelFour

theorem exists_image {C : Type} [Field C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, J.Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, hg⟩
  have a := hp k
  rw [N.mem_QT.1 p.2] at a
  exact (h₁ _).unique a (h₃ _)

theorem ev_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2)
    {g : N.Gt} {g' : N'.Gt} (hg : J.Rel g g') :
    N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun χ => (H χ).2 g g' hg

theorem labels_of_four_le : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  intro hL hE hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT hR n hn h3 hl k hk
    x p q' p' z hp e₁ e₂ hq hz
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  choose pt hpt using fun i : D.La => (existsUnique_twRel A.be u (r (n ^ 2)) (hr.pow hn2) (A.q (n ^ 2) i)).exists
  choose qt hq₁ hq₂ using fun i => exists_image J (pt i)
  choose pp hpp using fun i => (B.2.2.2.2 (n ^ 2)).2.1 (qt i)
  have hA : ∀ i, M.P.ToA C (n ^ 2) (pp i) (e (o.I.ev (n ^ 2) i)) := fun i =>
    hl i (pt i) (qt i) (pp i) _ (hpt i) (hq₁ i) (hq₂ i) (hpp i) (he _)
  obtain ⟨F, hF, -⟩ := hT C k (by omega)
  obtain ⟨y, hy⟩ := e.surjective (F p')
  have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' n hn D.La pp qt _ hA hpp
    k hk p' q' (F p') ((hF _ _).2 rfl) hq
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have ht : ∀ i, o.I.ev (n ^ 2) i ^ (n ^ 2) = 1 := fun i => (o.I.onto _ hn2 _).2 ⟨i, rfl⟩
  have Q₁ : IsCoordPt o.P n (T := baseOver (Sp C)) (o.I.ev (n ^ 2)) y fun i => fnOf (N'.ev n (qt i) q'.1.2) :=
    FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (he _)) ht (z := y)
      ((Category.id_comp _).trans ((congrArg (fun w => w.left) hy).symm.trans (he _))) Q
  have Q₂ := ((hR.2.2.2 n hn pt hpt).2.2 k (by omega) x p hp).2
  obtain ⟨-, s₂, -, s₄⟩ := CoordSep.coord_exists_unique_separate hL.1 C (Sp C) o.P (𝟙 _) n hn
    (Nat.cast_ne_zero.2 hn.pos.ne') D.La (o.I.ev (n ^ 2)) ht
  have Q₃ := (s₂ _ _ (fun i => N'.ev n (qt i) q'.1.2) Q₂).2
    ⟨J.lam * J.h p.1.2.b ^ (n ^ 2), funext fun i => ev_iso J hn (hq₁ i) (hq₂ i) e₂⟩
  obtain rfl := (s₄ h3 (fun w hw => (o.I.onto _ hn2 w).1 hw) _ _ _ Q₃ Q₁).1
  exact (hF _ _).2 ((Over.OverMorphism.ext (hz.trans (he _).symm)).trans hy)

end GlobalTheory.Ex.Trait.LevelFour
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedLabels_match_of_level_ge_four : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  atlas_forward_decl GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.LabelsAllLevels

section Values
variable {O : Type} [CommRing O] {N N' : NumD O}

def lower {k m : ℕ} (p : N.QT (k * m)) : N.QT k :=
  ⟨(p.1.1, p.1.2 ^ m), (pow_mul' _ k m).symm.trans p.2⟩

private theorem twist_theta' {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).θ = N.θ := rfl

private theorem twist_c {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).c = N.c := rfl

theorem qEq_twist {j k m : ℕ} (β : N.Form j) {u r r' : Oˣ} (h₁ : r' ^ m = r) (h₂ : r ^ k = u)
    {q' : N.QT (k * m)} {q : N.QT k} {p' : (N.twist β u).QT (k * m)} {p : (N.twist β u).QT k}
    (t' : TwRel β u r' q' p') (t : TwRel β u r q p) (e : N.QEq (lower q') q) :
    (N.twist β u).QEq (lower p') p := by
  obtain ⟨z, hy, hg⟩ := e
  obtain ⟨ty', tb', ts'⟩ := t'
  obtain ⟨ty, tb, ts⟩ := t
  refine ⟨z, ?_, ?_⟩
  · have e1 : (lower p').1.1 = (lower q').1.1 := ty'
    rw [ty, e1]
    exact hy
  · show p.1.2 = p'.1.2 ^ m * (N.twist β u).io z
    have hg' : q.1.2 = q'.1.2 ^ m * N.io z := hg
    apply NumD.Gt.ext
    · rw [tb, hg', NumD.Gt.mul_b, NumD.Gt.mul_b, NumD.Gt.pow_b, NumD.Gt.pow_b, tb', NumD.io_b]
      rfl
    · refine funext fun (χ : N.X) => ?_
      have A1 := ts χ
      have A2 := NumD.Gt.mul_s (q'.1.2 ^ m) (N.io z) χ
      rw [NumD.io_s, NumD.io_b, ← hg'] at A2
      have A3 := NumD.Gt.pow_s q'.1.2 m χ
      have A4 : (p'.1.2 ^ m).s χ * cubN N.θ m 1 q'.1.2.b (N.c χ) = p'.1.2.s χ ^ m := by
        have A4' := NumD.Gt.pow_s p'.1.2 m χ
        rw [tb'] at A4'
        exact A4'
      have Bq : (p'.1.2 ^ m).b = (q'.1.2 ^ m).b := by
        rw [NumD.Gt.pow_b, NumD.Gt.pow_b, tb'] <;> rfl
      have A5 := ts' χ
      have A6 := N.twist_τ β u z χ
      have hy' : β.be q.1.1.toAdd χ = β.be q'.1.1.toAdd χ + k * β.be z χ := by
        rw [show q.1.1.toAdd = q'.1.1.toAdd + k • z from hy, map_add, map_nsmul, LinearMap.add_apply,
          LinearMap.smul_apply, nsmul_eq_mul]
      rw [hy'] at A1
      rw [NumD.Gt.mul_s (p'.1.2 ^ m) ((N.twist β u).io z) χ, NumD.io_s (N.twist β u) z χ,
        NumD.io_b (N.twist β u) z, Bq, twist_theta' β u, twist_c β u, A6]
      subst h₁ h₂
      apply Additive.ofMul.injective
      replace A1 := congrArg Additive.ofMul A1
      replace A2 := congrArg Additive.ofMul A2
      replace A3 := congrArg Additive.ofMul A3
      replace A4 := congrArg Additive.ofMul A4
      replace A5 := congrArg Additive.ofMul A5
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_pow] at A1 A2 A3 A4 A5 ⊢
      rw [A1, A2, eq_sub_of_add_eq A3, eq_sub_of_add_eq A4, A5]
      clear hy hg hg' hy' ty ty' tb tb' ts ts' A6 A1 A2 A3 A4 A5
      module

theorem rel_pow (J : NumD.Iso N N') {g : N.Gt} {g' : N'.Gt} (h : J.Rel g g') (n : ℕ) : J.Rel (g ^ n) (g' ^ n) :=
  (NumD.Hom.ofIso_rel J _ _).1 (((NumD.Hom.ofIso_rel J _ _).2 h).pow n)

theorem exists_image (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := N.mem_QT.1 p.2
  have h1 : I.Rel (p.1.2 ^ k) (I.img p.1.2 ^ k) := (I.rel_img p.1.2).pow k
  have h2 : I.Rel (p.1.2 ^ k) (N'.io (I.e p.1.1.toAdd)) := by
    rw [hp]
    exact I.rel_io _
  have h3 : I.img p.1.2 ^ k = N'.io (J.e p.1.1.toAdd) :=
    ((I.rel_iff _ _).1 h1).trans ((I.rel_iff _ _).1 h2).symm
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), N'.mem_QT.2 h3⟩, rfl,
    (NumD.Hom.ofIso_rel J _ _).1 (I.rel_img _)⟩

theorem qEq_image (J : NumD.Iso N N') {k m : ℕ} {p' : N.QT (k * m)} {p : N.QT k} {q' : N'.QT (k * m)} {q : N'.QT k}
    (a' : q'.1.1.toAdd = J.e p'.1.1.toAdd) (b' : J.Rel p'.1.2 q'.1.2) (a : q.1.1.toAdd = J.e p.1.1.toAdd)
    (b : J.Rel p.1.2 q.1.2) (e : N.QEq (lower p') p) : N'.QEq (lower q') q := by
  obtain ⟨z, hy, hg⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, ?_, ?_⟩
  · show q.1.1.toAdd = q'.1.1.toAdd + k • J.e z
    have hy' : p.1.1.toAdd = p'.1.1.toAdd + k • z := hy
    rw [a, a', hy', map_add, map_nsmul]
  · show q.1.2 = q'.1.2 ^ m * N'.io (J.e z)
    have hg' : p.1.2 = p'.1.2 ^ m * N.io z := hg
    have r1 : I.Rel p.1.2 q.1.2 := (NumD.Hom.ofIso_rel J _ _).2 b
    have r2 : I.Rel p.1.2 (q'.1.2 ^ m * N'.io (J.e z)) := by
      rw [hg']
      exact (((NumD.Hom.ofIso_rel J _ _).2 b').pow m).mul (I.rel_io z)
    exact ((I.rel_iff _ _).1 r1).trans ((I.rel_iff _ _).1 r2).symm

private theorem pow_left_of_isGrpPullback' {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (z : Over.mk (T.hom ≫ f) ⟶ G) (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero =>
    let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w])
    have ho : o * o = o := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 o o rfl rfl, _root_.mul_one]
      rfl
    have h1 : o = 1 := mul_left_cancel (a := o) (by rw [_root_.mul_one]; exact ho)
    rw [pow_zero, pow_zero, ← h1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih e
end Values

theorem pow_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x : baseOver S' ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  let w : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') (by simp)
  have h1 : (w ≫ z).left = x.left ≫ φ := by
    rw [Over.comp_left, e]
    simp [w]
  have h2 := pow_left_of_isGrpPullback' h x (w ≫ z) h1 n
  rw [← comp_pow, Over.comp_left] at h2
  simpa [w] using h2

theorem labels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  intro hL hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hR _ hT h4 k hk
  intro x p q' p' z hTw hqy hqg hQ hz
  have hK : 0 < k * 4 := by omega
  obtain ⟨p₁, hp₁, -⟩ := existsUnique_twRel A.be u (r (k * 4)) (hR.pow hK) (A.q (k * 4) x)
  obtain ⟨q₁, hq₁y, hq₁g⟩ := exists_image J p₁
  obtain ⟨-, -, -, -, hQk⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨p₁', hp₁'⟩ := (hQk (k * 4)).2.1 q₁
  have hw : ((o.I.ev (k * 4) x).left ≫ M.φ) ≫ M.P.A.A.hom = (Out.TFK (R := M.W) C).hom := by
    rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
    simp
  let z₁ : Out.TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev (k * 4) x).left ≫ M.φ) hw
  have t₁ : M.P.ToA C (k * 4) p₁' z₁ := h4 (k * 4) (by omega) x p₁ q₁ p₁' z₁ hp₁ hq₁y hq₁g hp₁' rfl
  obtain ⟨p₂, hp₂⟩ := (hQk k).2.1 (lower q₁)
  have hy₂ : p₂.y = p₁'.y := hp₂.1.symm.trans hp₁'.1
  have hn₂ : GtPtF.IsNsmul 4 p₁'.g p₂.g := (GtValues.isNsmul_val ν' 4 hp₁'.2 hp₂.2).2 rfl
  haveI := M.admissible_base_of_complete_dvr.2
  have t₂ : M.P.ToA C k p₂ (z₁ ^ 4) :=
    (GlobalTheory.LevelCompat.qkToAkU_level hL M.W (IsLocalRing.maximalIdeal M.W) M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi
      M.P.U C k 4 (k * 4) hk (by norm_num) rfl p₂ p₁' z₁).2 hy₂ hn₂ t₁
  obtain ⟨hgA, -, -, -, hQA⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₀, hq₀y, hq₀n, hq₀e⟩ := A.I.tower k 4 hk (by norm_num) x
  have hqA := A.hq (k * 4) x
  obtain ⟨c₀, hc₀, -⟩ := hgA q₀.g
  have hc : c₀ = (A.q (k * 4) x).1.2 ^ 4 := (GtValues.isNsmul_val A.ν 4 hqA.2 hc₀).1 hq₀n
  have hQP : A.ν.QPt q₀ (lower (A.q (k * 4) x)) := by
    refine ⟨hqA.1.trans hq₀y.symm, ?_⟩
    show A.ν.Pt q₀.g ((A.q (k * 4) x).1.2 ^ 4)
    rw [← hc]
    exact hc₀
  have hE1 : A.N.QEq (lower (A.q (k * 4) x)) (A.q k x) :=
    ((hQA k).2.2 q₀ (A.I.ev k x) _ _ hQP (A.hq k x)).1 hq₀e
  have hE0 := qEq_twist A.be (hR.2 k 4 hk (by norm_num)) (hR.pow hk) hp₁ hTw hE1
  have hE : Out.QkPt.Equiv M.P.D.toPre C p₂ p' :=
    ((hQk k).2.2 p₂ p' _ _ hp₂ hQ).2 (qEq_image J hq₁y hq₁g hqy hqg hE0)
  obtain ⟨F, hF1, -, hF3, -, -, -⟩ := hT C k hk
  have e3 : z = z₁ ^ 4 := by
    apply Over.OverMorphism.ext
    rw [hz, pow_left M.cart (o.I.ev (k * 4) x) z₁ rfl 4, o.I.tower k 4 hk (by norm_num) x]
  exact (hF1 p' z).2 (e3.trans (((hF1 p₂ _).1 t₂).trans ((hF3 p₂ p').2 hE)))

end GlobalTheory.Ex.LabelsAllLevels
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedLabels_all_levels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  atlas_forward_decl GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait.LevelClause

theorem qEq_twist {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {u r : Oˣ} {j : ℕ} (h : r ^ j = u)
    {p q : N.QT j} {p' q' : (N.twist β u).QT j} (e : N.QEq p q) (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩
  · rw [hp.1, hq.1]; exact h1
  · rw [hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]; rfl
  · have e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ := N.twist_τ β u z χ
    have e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ := by
      rw [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul,
        zpow_natCast, h]
    have e₃ : (p'.1.2 * (N.twist β u).io z).s χ =
        p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z) := rfl
    refine (hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)
    rw [h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem exists_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩
  have a := (I.rel_img p.1.2).pow k
  rw [hp] at a
  exact (I.rel_existsUnique _).unique a (I.rel_io _)

theorem qEq_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (e : N.QEq p q) (hp : p'.1.1.toAdd = J.e p.1.1.toAdd) (hp' : J.Rel p.1.2 p'.1.2)
    (hq : q'.1.1.toAdd = J.e q.1.1.toAdd) (hq' : J.Rel q.1.2 q'.1.2) : N'.QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, by rw [hq, hp, h1, map_add, map_nsmul], ?_⟩
  have a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z)) := NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)
  rw [← h2] at a
  exact (I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a

theorem genRel_of_gauge {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (ht₀ : t₀.IsGen) (x : F) (hpt : ∀ k, pt k ≫ φ = pt₀ k)
    (J : (Sp F ⟶ B₀) → M₀.ι) (J' : (Sp F ⟶ B) → M.ι) (gJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M₀.U (J ψ)) (gJ' : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M.U (J' ψ))
    (hv : (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) * vF t (𝟙 _) J' = x * vF t₀ (𝟙 _) J) :
    GenRel w t t₀ x := by
  obtain rfl : pt₀ = fun k => pt k ≫ φ := funext fun k => (hpt k).symm
  have z : Sp F := (default : PrimeSpectrum F)
  rw [genRel_iff w t t₀ x z]
  refine ⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩
  have hJ := fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)
  have hJ' := fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)
  have hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ _
  have hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k)) := Set.mem_iInter.2 fun k => hJ' _
  have P1 := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'
  have G1 := gen_trans ht (𝟙 _) z hq hq'
  have G0 := gen_trans ht₀ (𝟙 _) z hp hp'
  have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) =
      (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val := fun k =>
    toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _
  have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) =
      (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val := by
    simp only [pw, Category.id_comp]
    rw [map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0 := fun h0 => by
      have := a₃ k
      rw [h0, map_zero] at this
      exact Units.ne_zero _ this.symm
    have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _ := Units.ext (a₃ k)
    rw [← e, ← map_zpow]
    show _ = toStk z _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e' := congrArg (toStk z) hv
  rw [map_mul, map_mul, a₄] at e'
  have b₁ : toStk z (vF t (𝟙 _) J') = _ := toStk_valF _ _ z hq' _
  have b₀ : toStk z (vF t₀ (𝟙 _) J) = _ := toStk_valF _ _ z hp' _
  rw [b₁, b₀, ← Units.val_mul] at e'
  have hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j := by
    simp only [pw, Category.id_comp]
  have step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d) := fun a b c d => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]
  exact mul_left_comm _ _ _

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) (b : N.A) (χ : N.X) (i : Fin 4) :
    DegPre.gtφ D F (ν.eA b) (ν.eX χ) i = (ν.eA (![N.c χ * b, N.c χ, b, 1] i)).left := by
  fin_cases i
  · show _ = (ν.eA (N.c χ * b)).left
    rw [map_mul, ν.c_eq]; rfl
  · show _ = (ν.eA (N.c χ)).left
    rw [ν.c_eq]; rfl
  · rfl
  · show _ = (ν.eA 1).left
    rw [map_one]; rfl

theorem level_clause : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  intro _ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz
  obtain ⟨-, hw, hA, hX, hne, hh⟩ := hF
  have hrk := hr.pow hk
  obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C)
    (RingHom.ext fun _ => rfl) p₀
  obtain ⟨-, -, -, -, B₀⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B₁⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨v₀, hv₀, -⟩ := (B₀ k).1 q₀
  have e₀ := ((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_twRel A.be u (r k) hrk v₀
  obtain ⟨t₁, ht₁, -⟩ := existsUnique_twRel A.be u (r k) hrk (A.q k v)
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_image J t₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_image J t₁
  obtain ⟨q, hq⟩ := (B₁ k).2.1 s₀
  obtain ⟨p', hp'⟩ := (B₁ k).2.1 s₁
  have e₁ := ((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')
  refine ⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩
  · rw [← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]
    rfl
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective χ
    have hb : q.g.b = ν'.eA (J.φ v₀.1.2.b) := by rw [← hq.2.1, hs₀'.1, ht₀.2.1]
    have hc : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
    have g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i =
        (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left := fun i => by
      rw [hb, hX, gtφ_eq, hc]
      fin_cases i
      · exact congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm
      · rfl
      · rfl
      · exact congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm
    refine genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_
    · rw [g₁, hA, ← hv₀.2.1, gtφ_eq]
    · have g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _
          (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ),
            ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val =
          wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i)) := fun i =>
        congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)
      have g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C) :=
        (congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm
      have g₄ := (hv₀.2.2 χ).symm
      have g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ) := by
        rw [← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
          mul_comm, A.be.div_mul hkM]
      have g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) =
          v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b := by
        have := hs₀'.2 χ
        rw [ht₀.2.1, ht₀.2.2] at this
        exact this
      have g₇ := congrArg Units.val g₆
      simp only [Units.val_mul] at g₇
      refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)
      rw [Fin.prod_univ_four]
      have alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W →
          w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ →
          w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀ := by
        intro S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄
        subst a₃
        simp only [zpow_neg, zpow_one]
        field_simp
        refine mul_left_cancel₀ nW ?_
        linear_combination (-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ +
          (S₀ * ρ * w₀ * w₃) * a₂
      exact alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _)
        (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇
  · obtain ⟨g, hg, -, hge, -⟩ := hTI C k hk
    exact (hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)

end GlobalTheory.Ex.Trait.LevelClause
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_valuedField_twistedUniformisation : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  atlas_forward_decl GlobalTheory.Ex.Trait.LevelClause.level_clause
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section

namespace GlobalTheory.LevelField

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcDataDescent

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt pt' : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (hp : pt = pt') (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x)
    (z : Sp F) {J} (hJ : Good M z J) : val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  subst hp
  choose J₀ hJ₀ using fun χ : Sp F ⟶ B₀ => exists_chart hM₀ (χ z)
  have e := ((genRel_iff w t t₀ x z).1 h).2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  have e' := ((genRel_iff w t' t₀ x z).1 h').2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t' _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact mul_left_cancel (Units.ext (e.trans e'.symm))

variable {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {D : DegPre R} {D₀ : DegPre O'}
  {ψ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull ψ)} {k : ℕ}

theorem genRel_ext {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing O') F] [Algebra (FractionRing O') F'] {σ : F →+* F'}
    (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hσ₀ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')
    {q : QkPt D F k} {q' : QkPt D F' k} {q₀ : QkPt D₀ F k} {q₀' : QkPt D₀ F' k} (h : QkExt σ q q')
    (h₀ : QkExt σ q₀ q₀') {χ : D.X} {χ₀ : D₀.X} {x : F} (H : GenRel w (q.g.s χ) (q₀.g.s χ₀) x) :
    GenRel w (q'.g.s χ) (q₀'.g.s χ₀) (σ x) :=
  (genRel_congr D.P.isLB D₀.P.isLB w (gtφ_ext hσ h χ) (gtφ_ext hσ₀ h₀ χ₀) (q'.g.isGen _)
    (pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
    (fun _ _ hJ => val_corr hJ (h.2.2 χ) _) (fun _ _ hJ => val_corr hJ (h₀.2.2 χ₀) _) _).2
    ((genRel_pull_iff σ w _ _ x).2 H)

theorem eq_of_genRel {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {f : O' →+* R}
    (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) ψ) (e : D₀.X ≃+ D.X) {q q' : QkPt D F k} {q₀ : QkPt D₀ F k}
    {x : D₀.X → F} (hy : q.y = q'.y) (H : ∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (x χ))
    (H' : ∀ χ, GenRel w (q'.g.s (e χ)) (q₀.g.s χ) (x χ)) : q = q' := by
  have hb : q.g.b = q'.g.b :=
    Over.OverMorphism.ext (gp.1.hom_ext (((H 0).1 2).trans ((H' 0).1 2).symm) (by rw [Over.w, Over.w]))
  refine TorusExt.qk_ext hy (TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_)
  obtain ⟨χ, rfl⟩ := e.surjective χ
  exact val_eq_of_genRel D₀.P.isLB (by rw [hb]) (H χ) (H' χ) y hJ

theorem toA_of_toA : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  intro hL E _ _ _ H R O' _ _ _ _ _ I _ t P D₀ hB f ψ w e gp _ k hk p₀ s x₀ C _ _ _ _ hC q₀ q x h₀ hy hg hx hA
    F _ _ _ _ hF q₀' q' x' h₀' hy' hg' hx'
  obtain ⟨F', _, _, σ, τ, hστ⟩ := exists_common_field (algebraMap (FractionRing R) C) (algebraMap (FractionRing R) F)
  letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap _ C)).toAlgebra
  letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap _ C)).toAlgebra
  have hσ : σ.comp (algebraMap (FractionRing R) C) = algebraMap (FractionRing R) F' := rfl
  have hσ₀ : σ.comp (algebraMap (FractionRing O') C) = algebraMap (FractionRing O') F' := rfl
  have hτ : τ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := hστ.symm
  have hτ₀ : τ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' :=
    IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun a =>
      (congrArg τ (hF a).symm).trans ((RingHom.congr_fun hστ _).symm.trans (congrArg σ (hC a))))
  obtain ⟨r, hr, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ hσ q
  obtain ⟨r', hr', -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult τ hτ q'
  obtain ⟨r₀, hr₀, -⟩ := TorusExt.existsUnique_qkExt hB σ hσ₀ q₀
  obtain ⟨r₀', hr₀', -⟩ := TorusExt.existsUnique_qkExt hB τ hτ₀ q₀'
  have a := qkExt_trans h₀ hr₀
  have a' := qkExt_trans h₀' hr₀'
  rw [hσ₀] at a
  rw [hτ₀] at a'
  obtain rfl : r₀ = r₀' :=
    (TorusExt.existsUnique_qkExt hB (algebraMap (FractionRing O') F') (RingHom.ext fun _ => rfl) p₀).unique a a'
  obtain rfl : r = r' := eq_of_genRel gp e (q₀ := r₀) (x := fun χ => algebraMap (FractionRing R) F' (s χ))
    (by rw [hr.1, hr'.1, hy, hy', h₀.1, h₀'.1]) (fun χ => genRel_ext hσ hσ₀ hr hr₀ (hg χ))
    (fun χ => by
      have b := genRel_ext hτ hτ₀ hr' hr₀' (hg' χ)
      rwa [show τ (algebraMap (FractionRing R) F (s χ)) = algebraMap (FractionRing R) F' (s χ) from
        RingHom.congr_fun hτ _] at b)
  letI : Algebra C F' := σ.toAlgebra
  letI : Algebra F F' := τ.toAlgebra
  haveI : IsScalarTower (FractionRing R) C F' := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq' hτ.symm
  have hj : spMap σ ≫ jFK (R := R) C = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  have hj' : spMap τ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hτ)
  have ex : TorsionExt.fieldMap (R := R) C F' ≫ x = TorsionExt.fieldMap (R := R) F F' ≫ x' := by
    refine Over.OverMorphism.ext ?_
    show spMap σ ≫ x.left = spMap τ ≫ x'.left
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hj, hj']
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr' x').2 ?_
  rw [← ex]
  exact (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr x).1 hA

end GlobalTheory.LevelField
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_of_one_algClosed_field : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  first | exact @GlobalTheory.LevelField.toA_of_toA | exact GlobalTheory.LevelField.toA_of_toA | (intros; apply GlobalTheory.LevelField.toA_of_toA <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait

theorem exists_odd_prime (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ 3 ≤ n ∧ ‖(n : C)‖ = 1 := by
  by_cases h : ‖((3 : ℕ) : C)‖ = 1
  · exact ⟨3, Nat.prime_three, by decide, le_rfl, h⟩
  refine ⟨5, Nat.prime_five, by decide, by decide, ?_⟩
  by_contra h'
  have h3 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 3) h
  have h5 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 5) h'
  have e : (1 : C) = ((3 : ℕ) : C) + ((3 : ℕ) : C) + -((5 : ℕ) : C) := by push_cast; ring
  have := IsUltrametricDist.norm_add_le_max (((3 : ℕ) : C) + ((3 : ℕ) : C)) (-((5 : ℕ) : C))
  rw [← e, norm_one, norm_neg] at this
  have h6 := (IsUltrametricDist.norm_add_le_max ((3 : ℕ) : C) ((3 : ℕ) : C)).trans_lt (by rwa [max_self])
  exact absurd this (not_le.2 (max_lt h6 h5))

theorem admissible_base_of_complete_dvr {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) :
    AdmBase V (IsLocalRing.maximalIdeal V) :=
  haveI := hV.1
  ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mono_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) :=
    IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

set_option maxHeartbeats 1000000 in

theorem hasArcData_of_model (hV : HV) (h6 : Laws6) (hU : GlobalTheory.LN.UDvrSt) (hH : GlobalTheory.LN.HomExtSt) (hT : ThetaPtDeterminesSt)
    (hE : EndDeterminedOnTorsionSt) (hTU : ThetaUnifAV) {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype)
    {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'} {ϖ : O'}
    (a : ArcIn D l (c.V W₀).subtype O' b) (hB : GlobalTheory.LN.ArcBase O' ϖ) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C)
    {u : Cˣ} {r : ℕ → Cˣ} {o : Full D C} (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W) (hI : A.ν.IntN)
    (hR : Realises o A.arc A.be u r) (hu₁ : ‖(u : C)‖ < 1)
    (hu : (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀)) (hf : Along f C) {χ : Sp M.W ⟶ Y.X}
    (m : SABMap M.t Y.t χ) {y : Sp (FractionRing M.W) ⟶ Xo.XF c} (hy : y ≫ Y.j = jK M.W ≫ χ)
    {φ₀ : o.P.A.left ⟶ Y.oF.t.G.left}
    (hφ : M.φ ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ = φ₀ ≫ Y.m.φ)
    (hA : ∀ v, (o.I.ev l.A v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.etaA v).left)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o.I.ev l.M v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.eta v).left)
    (t₁ : RatTors M.P.D.toPre.P C 3)
    (t₂ : ∀ (B : PolAV (Sp M.W)) ψ, IsGrpPullback B.A a.D₀.P.A (spMap f) ψ → RatTors B C 3) :
    Y.HasArcData a (IsLocalRing.maximalIdeal M.W) f u₀ χ := by
  letI := H.starRing
  have hLL := hV.1
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have hGt : BrGtSt := GlobalTheory.T.torus_torsion_points_correspond_values
  have : IsNoetherianRing O' := by
    rcases hB with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have := M.cdv.1
  have := M.cdv.2.2
  have tors := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2 E H M.W _ (admissible_base_of_complete_dvr M.cdv) M.t M.P
  obtain ⟨n, hn, hno, hn3, hn1⟩ := exists_odd_prime C
  obtain ⟨N', ν', J, hlin, hlab, DW, _, oW, φ, he, w₀, e₀, νW, hm, -, hpt, Φ, wΦ, -, hΦ, hwΦ, hΦpt, -⟩ :=
    GlobalTheory.T.lift_valuation_integral_norm hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y O' b ϖ a hB C A u r o M f u₀ hI hR.1 hu₁ hu hf n hn hno hn1
      fun j => ⟨hR.2.2.1 _ (pow_pos hn.pos j), fun p hp => (hR.2.2.2 _ hno.pow p hp).2.1⟩
  obtain ⟨Ψ, hΨ, lΨ, pΨ⟩ := GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion hL hL2 hH M.W M.cdv C DW.P M.P.D.toPre.P (t₂ _ _ hm.1) t₁ Φ
    (νW.eA.symm.trans (J.φ.trans ν'.eA))  hΦ
    (fun x => by obtain ⟨x, rfl⟩ := νW.eA.surjective x; simpa using hΦpt x) ⟨wΦ, hwΦ⟩
  set ψ := Ψ.hom.left ≫ φ with hψ
  have gψ : IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ :=
    ((isGrpPullback_of_iso Ψ).comp hm.1).congr (Category.id_comp _) rfl
  have lψ : LBIso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ) :=
    LBIso.trans M.P.D.toPre.P.isLB (pull_isLB DW.P.isLB _) (pull_isLB a.D₀.P.isLB _) lΨ
      (LBIso.chartPull (Geo.Tor.chartPullPull DW.P.L _ _ rfl)
        (chartPullSame a.D₀.P.L _ (fun _ : PUnit => φ) _ Ψ.hom.left fun _ => rfl) ⟨w₀, hm.2.1⟩)
  have pψ : ∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left := fun x => by
    have e : ν'.eA (J.φ x) ≫ Ψ.hom = νW.eA x :=
      (congrArg (fun z => ν'.eA (J.φ z) ≫ Ψ.hom) (νW.eA.symm_apply_apply x)).symm.trans (pΨ (νW.eA x))
    rw [hψ, ← Category.assoc, ← Over.comp_left]
    exact (congrArg (fun z => CommaMorphism.left z ≫ φ) e).trans (hpt x)
  have heψ := GlobalTheory.PolBaseChange.eSec_comm gψ
  obtain ⟨w, hw, hrig⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A M.P.D.toPre.P.A ψ heψ
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩
    ⟨M.P.D.toPre.P.L, M.P.D.toPre.rig, M.P.D.toPre.P.isLB, M.P.D.toPre.rig_gen⟩ lψ
  let e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X :=
    { A.ν.eX.symm.trans (J.e.trans ν'.eX) with
      map_smul' := fun x y => by
        obtain ⟨y, rfl⟩ := A.ν.eX.surjective y
        exact (hlin x y).trans (congrArg (fun z => x • ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y).symm) }
  have fit : Fit A u M f ν' J ψ w e :=
    ⟨gψ, hw, pψ, fun y => congrArg (fun z => ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y),
      GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value hL hL2 M.W O' f _ _ C hf N' A.N ν' A.ν ψ w J.toIso gψ hw pψ⟩
  have act : ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left := fun x => by
    refine GlobalTheory.T.polarized_abelian_pullback_line_bundle hL hE E H M.W _ _ _ _ M.P.oD.onB a.oa.onB ψ gψ lψ C n hn.two_le x fun j z hz => ?_
    obtain ⟨z, rfl⟩ := (J.φ.trans ν'.eA).surjective z
    have hz' : (z : A.N.A) ^ n ^ j = 1 := (J.φ.trans ν'.eA).injective (by rw [map_pow, map_one]; exact hz)
    have e₁ := GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors _ (pow_pos hn.pos j) (hlab j) hlin x z
      (A.ν.eA.symm (A.ν.eA z ≫ a.oa.onB.act x)) hz' (A.ν.eA.apply_symm_apply _)
    refine (congrArg (fun z => CommaMorphism.left z ≫ ψ) e₁.symm).trans ((pψ _).trans ?_)
    rw [MulEquiv.apply_symm_apply, Over.comp_left]
    exact (congrArg (· ≫ _) (pψ z).symm).trans (Category.assoc _ _ _)
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆⟩ := GlobalTheory.T.modelIso_of_valued_agreement_over_field hLL E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf u₀ hu ψ heψ w e fit hrig act
  have lab := GlobalTheory.T.twistedLabels_all_levels_of_four_le hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
    (GlobalTheory.T.twistedLabels_match_of_level_ge_four hLL (GlobalTheory.T.torsionCoordinates_eq_degenerationSeries hV hGt (GlobalTheory.T.families_values_correspond hL hL2)) hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
      hR n hno hn3 (hlab 2))
  refine ⟨M.t, m, M.P, ψ, heψ, w, e, s₁, s₂, s₃, s₄, s₅, fun F _ _ _ _ uF hF huF => ⟨s₆ F uF hF huF, ?_⟩⟩
  intro yF hyF k p₀ σ hσ q₀ q x h₀ hq hg hx
  have := mono_j Y
  obtain rfl : yF = jFK (R := M.W) F ≫ y := by rw [← cancel_mono Y.j, hyF, Category.assoc, hy]
  obtain ⟨hk, hkM, v, hv, hev⟩ : 0 < k ∧ k ∣ l.M' ∧ ∃ v, (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) ∧
      (o.I.ev k v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ σ.left := by
    rcases hσ with ⟨rfl, v, h, rfl⟩ | ⟨rfl, v, hv, h, rfl⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.A_pos, Nat.dvd_lcm_right _ _, v, A.levA v, hA v⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.odd.pos, Nat.dvd_lcm_left _ _, v, A.levM v hv, hM v hv⟩
  have := M.P.U.gen_hom
  have gp : IsPullback (M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ) M.P.A.A.hom Y.t.G.hom (jK M.W ≫ χ) := by
    have : IsMonHom M.P.U.gen.symm.hom := by show IsMonHom M.P.U.gen.inv; infer_instance
    exact (((isGrpPullback_of_iso M.P.U.gen.symm).comp ((isGrpPullback_pullback M.t.G (jK M.W)).comp m.cart)).congr
      (Category.id_comp _) rfl).1
  have hσw : (y ≫ σ.left ≫ Y.m.φ) ≫ Y.t.G.hom = 𝟙 _ ≫ jK M.W ≫ χ := by
    have e₁ : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    rw [Category.assoc, Category.assoc, Y.m.cart.1.w, reassoc_of% e₁, Category.id_comp, ← hy]; rfl
  let x₀ := gp.lift _ _ hσw
  have hx₀ : ∀ (K : Type) [Field K] [Algebra (FractionRing M.W) K] (z : Sp K ⟶ M.P.A.A.left),
      z ≫ M.P.A.A.hom = jFK (R := M.W) K → z ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ =
        (jFK (R := M.W) K ≫ y) ≫ σ.left ≫ Y.m.φ → z = jFK (R := M.W) K ≫ x₀ := fun K _ _ z h₁ h₂ => by
    apply gp.hom_ext
    · rw [h₂, Category.assoc, Category.assoc (jFK (R := M.W) K), gp.lift_fst]
    · rw [h₁, Category.assoc, gp.lift_snd]; exact (Category.comp_id _).symm
  have hzw : ((o.I.ev k v).left ≫ M.φ) ≫ M.P.A.A.hom = jFK (R := M.W) C := by
    have e₁ : (o.I.ev k v).left ≫ o.P.A.hom = 𝟙 _ := Over.w _
    rw [Category.assoc, M.cart.1.w, reassoc_of% e₁]
  obtain ⟨q₁, q₂, a₁, a₂, a₃, a₄⟩ := GlobalTheory.T.levelCondition_valuedField_twistedUniformisation hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors ψ w e fit k hk hkM
    (lab k hk) p₀ v hv (Over.homMk ((o.I.ev k v).left ≫ M.φ) hzw) rfl
  refine GlobalTheory.T.levelCondition_of_one_algClosed_field hLL E H M.W O' _ (admissible_base_of_complete_dvr M.cdv) M.t M.P a.D₀ a.bimult f ψ w e.toAddEquiv s₁ s₂ k hk p₀
    (fun z => algebraMap M.W _ u₀ ^ (a.be p₀.y z / k)) x₀ C hf q₁ q₂ _ a₁ a₂ (fun z => ?_) ?_ a₄ F (fun x => (hF x).symm) q₀ q x
    h₀ hq (fun z => ?_) (hx₀ F _ (Over.w x) hx)
  · rw [map_zpow₀, ← hu, ← a₁.1]; exact a₃ z
  · refine hx₀ C _ hzw ?_
    change ((o.I.ev k v).left ≫ M.φ) ≫ _ = _
    rw [Category.assoc, hφ, ← Category.assoc, hev, Category.assoc]
  · rw [map_zpow₀, ← huF, ← h₀.1]; exact hg z

theorem eq_of_generic {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {R : Type} [CommRing R] [IsDomain R]
    (C : Type) [Field C] [Algebra (FractionRing R) C] {x x' : Sp R ⟶ Y.X}
    (h : jFK (R := R) C ≫ jK R ≫ x = jFK (R := R) C ≫ jK R ≫ x') : x = x' := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot ((algebraMap (FractionRing R) C).comp (algebraMap R _))).1
      ((algebraMap (FractionRing R) C).injective.comp (IsFractionRing.injective R (FractionRing R)))).trans_le bot_le)⟩
  refine ext_of_isDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) ?_
  rw [spMap_comp, Category.assoc, Category.assoc]
  exact h

theorem hasArcData_at_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → RealAt Y a g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → ¬ IsUnit (φ (g PowerSeries.X)) → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Y.HasArcData a (IsLocalRing.maximalIdeal W') (io.comp (φ.comp (g.comp (PowerSeries.C (R := O'))))) (io (φ (g PowerSeries.X))) (spMap io ≫ χ) := by
  intro hV h6 hU hH hT hE hTU E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB R₁ _ _ g y₁ hg _ _ hR hs W _ _ _ hW φ gam hgam χ hχ hu
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have := hW.1
  have := hW.2.2
  have hφ : Function.Injective φ := fun x y h => IsFractionRing.injective R₁ (FractionRing R₁) (gam.injective (by
    rw [hgam, hgam, h]))
  obtain ⟨C, _, _, _, _, _, -, -, hext⟩ := exists_complete_isAlgClosed_cExt W (FractionRing W)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective
  set f₀ := φ.comp (g.comp (PowerSeries.C (R := O'))) with hf₀
  have inj₀ : Function.Injective f₀ := hφ.comp (hg.comp PowerSeries.C_injective)
  have injW : Function.Injective ((algebraMap (FractionRing W) C).comp (algebraMap W _)) :=
    (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  have injC : Function.Injective (((algebraMap (FractionRing W) C).comp (algebraMap W _)).comp f₀) := injW.comp inj₀
  letI : Algebra (FractionRing O') C := (IsFractionRing.lift (K := FractionRing O') injC).toAlgebra
  have al₀ : Along f₀ C := fun x => (IsFractionRing.lift_algebraMap injC x).symm
  have hu0 : algebraMap (FractionRing W) C (algebraMap W _ (φ (g PowerSeries.X))) ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hg (hφ (injW (h.trans (by simp)))))
  have hu1 := hext.2 _ ((IsLocalRing.mem_maximalIdeal _).2 hu)
  obtain ⟨A, r, o, hI, -, hF, hRe⟩ := hR.2 C ((algebraMap (FractionRing W) C).comp gam) (Units.mk0 _ hu0)
    (fun x => (al₀ x).symm.trans (congrArg _ (hgam _).symm)) (fun x => by
      rw [RingHom.comp_apply, hgam]; exact hext.1 _) (congrArg _ (hgam _).symm) hu1
  rw [spMap_comp, Category.assoc] at hF
  have sq : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp φ _))
  obtain ⟨M, f₁, χ₁, m₁, fin₁, al₁, hχ₁, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y C W hW hext
    (FractionRing W) (algebraMap _ C) (fun _ => rfl) (spMap gam ≫ y₁) (f₀.comp b) (by
      have e : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
      rw [e, Category.id_comp, Category.assoc, hs, reassoc_of% sq, hf₀, spMap_comp, spMap_comp, spMap_comp]
      simp only [Category.assoc]) o hF
  have inj₁ : Function.Injective f₁ := fun x y h => injW ((al₁ x).symm.trans (h ▸ al₁ y))
  obtain ⟨W₂, _, _, _, _, io, hW₂, inj₂, fin₂, loc₂, al₂, ext₂, t₁, t₂⟩ := GlobalTheory.T.exists_completeDVR_extension_torsion_rational hL M.W M.cdv C M.ext 3 (by decide)
    _ _ (𝟙 _) (spMap (f₁.comp f₀)) M.P.D.toPre.P a.D₀.P
  have := hW₂.1
  have := hW₂.2.2
  obtain ⟨t, m₀, P, ψ, gψ⟩ := GlobalTheory.T.exists_linearUniformisation_baseChange_admissible hL hL3 hL4 hL5 E H M.W W₂ _ _ (admissible_base_of_complete_dvr M.cdv) (admissible_base_of_complete_dvr hW₂) io inj₂
    (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit io x hx) M.t M.P
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₀
  have al : Along (io.comp f₁) C := fun x => (al₂ _).trans (al₁ x)
  have inj : Function.Injective ((algebraMap W₂ (FractionRing W₂)).comp (io.comp f₁)) :=
    (IsFractionRing.injective W₂ _).comp (inj₂.comp inj₁)
  let δ : FractionRing W →+* FractionRing W₂ := IsFractionRing.lift inj
  have hδ : ∀ x, δ (algebraMap W _ x) = algebraMap W₂ _ (io (f₁ x)) := IsFractionRing.lift_algebraMap inj
  have sq₂ : spMap δ ≫ jK W = jK W₂ ≫ spMap (io.comp f₁) :=
    (spMap_comp _ δ).symm.trans ((congrArg spMap (RingHom.ext hδ)).trans (spMap_comp _ _))
  have jδ : jFK (R := W₂) C ≫ spMap δ = spMap (algebraMap (FractionRing W) C) :=
    (spMap_comp δ _).symm.trans (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun x =>
      (congrArg (algebraMap (FractionRing W₂) C) (hδ x)).trans (al x))))
  have jio : jFK (R := W₂) C ≫ jK W₂ ≫ spMap io = jFK (R := M.W) C ≫ jK M.W :=
    ((congrArg (_ ≫ ·) (spMap_comp _ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun x => al₂ x)).trans (spMap_comp _ _))
  have hy : (spMap δ ≫ spMap gam ≫ y₁) ≫ Y.j = jK W₂ ≫ spMap (io.comp f₁) ≫ χ := by
    rw [Category.assoc, Category.assoc, hχ, reassoc_of% sq₂]
  have eχ : spMap io ≫ χ₁ = spMap (io.comp f₁) ≫ χ := by
    refine eq_of_generic Y C ?_
    rw [← hy, reassoc_of% jio, hχ₁, Category.assoc (spMap δ), reassoc_of% jδ]
  obtain ⟨φ₀, g₀, l₀, a₀, hA, hM, -⟩ := hF
  have ey : spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ = jFK (R := W₂) C ≫ spMap δ ≫ spMap gam ≫ y₁ := by
    rw [reassoc_of% jδ]
  rw [ey] at g₀ hA hM
  rw [← eχ] at hy
  obtain ⟨φ₂, g₂, l₂, a₂, e₂⟩ := GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre E H D l Xo c _ _ Y W₂ _ t _ m P C _ (by rw [Category.assoc, hy]) o φ₀ g₀ l₀ a₀
  let M₂ : Mdl o := ⟨W₂, hW₂, ext₂, t, P, φ₂, g₂, l₂, a₂⟩
  refine ⟨W₂, _, _, _, io.comp f₁, hW₂, inj₂.comp inj₁, fin₂.comp fin₁, ?_⟩
  rw [← eχ]
  exact hasArcData_of_model hV h6 hU hH hT hE hTU Y a hB A M₂ ((io.comp f₁).comp f₀) _ hI hRe hu1 (al _).symm
    (fun x => (al _).trans (al₀ x)) m hy e₂ hA hM (t₁ _ ψ (gψ.congr (Category.comp_id _).symm rfl))
    fun B ψ' h => t₂ B ψ' (h.congr (spMap_comp (f₁.comp f₀) io) rfl)

end GlobalTheory.Ex.Trait
end
end
