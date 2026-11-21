import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_pullback_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χZ : Sp R ⟶ Z.X) (χY : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo.XF c), Out.jK R ≫ χZ = y ≫ Z.j → Out.jK R ≫ χY = y ≫ Y.j →
      ∃ (t : SAB H (Sp R)) (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY),
        ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
          g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
          g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  first | exact @GlobalTheory.TriplesAlong.main | exact GlobalTheory.TriplesAlong.main | (intros; apply GlobalTheory.TriplesAlong.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_arc_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b' : c.V W →+* O') (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
    (∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) →
    ∃ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j := by
  first | exact @GlobalTheory.PolArc.generic_factors_open | exact GlobalTheory.PolArc.generic_factors_open | (intros; apply GlobalTheory.PolArc.generic_factors_open <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ n : ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n} := by
  first | exact @GlobalTheory.ArcOrder.main | exact GlobalTheory.ArcOrder.main | (intros; apply GlobalTheory.ArcOrder.main <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.DRFlag (basPull basPull_apply basPull_repr tanPull_tanPull exists_affine_basis)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitGen

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_basis_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] {x' : Sp S ⟶ X'} {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x' t'.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x t.G), ∀ i, (tv (b' i)).left = (tv (b i)).left ≫ m.φ := by
  subst e
  exact ⟨b.map (tanEquiv m.cart x'), fun i => tanPush_left m.cart x' (b i)⟩

theorem exists_basis_lift {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] (x' : Sp S ⟶ X') {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x t.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x' t'.G), ∀ i, (tv (b' i)).left ≫ m.φ = (tv (b i)).left := by
  subst e
  refine ⟨b.map (tanEquiv m.cart x').symm, fun i => (tanPush_left m.cart x' _).symm.trans ?_⟩
  exact congrArg (fun v => (tv v).left) ((tanEquiv m.cart x').apply_symm_apply (b i))

theorem tv_hom {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} (v : TanM x t.G) :
    (tv v).left ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x := Over.w (tv v)

theorem exists_basis_extends {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {Z : Scheme.{0}} {t : SAB H (Sp R)}
    {tC : SAB H Z} {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u tC x) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (FractionRing R) (TanM x tC.G)),
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ (χ : Sp V ⟶ Z) (h : spMap gam ≫ x = jK V ≫ χ), ∃ b' : Module.Basis (Fin n) V (TanM χ tC.G), ∀ i,
        tanPull gam h (b i) = tanPull (algebraMap V (FractionRing V)) rfl (b' i) := by
  obtain ⟨U, n, hU, hb⟩ := exists_affine_basis t (closedPoint R)
  obtain ⟨bR⟩ := hb R (𝟙 _) ((IsLocalRing.closed_point_mem_iff (U := U)).1 hU).ge
  obtain ⟨bu, hbu⟩ := exists_basis_lift aT (𝟙 _) (Category.id_comp _)
    (basPull (algebraMap R (FractionRing R)) (Category.comp_id _) bR)
  obtain ⟨b, hb⟩ := exists_basis_push aC (Category.id_comp _) bu
  refine ⟨n, b, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨Dd, tW, c0, mm, a1, a3, -, e₁, e₂⟩ := exists_trait_map hu aT aC hV ψ gam hg χ h
  obtain ⟨bw, hbw⟩ := exists_basis_lift a1 (𝟙 _) (Category.id_comp _) (basPull ψ (Category.comp_id _) bR)
  obtain ⟨b', hb'⟩ := exists_basis_push a3 (Category.id_comp _) bw
  refine ⟨b', fun i => tan_ext_left ?_⟩
  simp only [basPull_apply, tanPull_left] at hbu hbw
  rw [tanPull_left, tanPull_left, hb, hb']
  have w : (spMap (dualMap gam) ≫ (tv (bu i)).left) ≫ u.G.hom =
      spMap (algebraMap _ (DualNumber (FractionRing V))) ≫ spMap gam := by
    rw [Category.assoc, tv_hom, Category.comp_id, spMap_comp', spMap_comp', PullbackSections.dualMap_comp_alg]
  obtain ⟨ρ, ρ₁, ρ₂⟩ : ∃ ρ : Sp (DualNumber (FractionRing V)) ⟶ Dd.G.left,
      ρ ≫ c0.φ = spMap (dualMap gam) ≫ (tv (bu i)).left ∧
      ρ ≫ Dd.G.hom = spMap (algebraMap _ (DualNumber (FractionRing V))) :=
    ⟨c0.cart.1.lift _ _ w, c0.cart.1.lift_fst _ _ w, c0.cart.1.lift_snd _ _ w⟩
  have hc : gam.comp (algebraMap R _) = (algebraMap V _).comp ψ := RingHom.ext hg
  have k : ρ ≫ mm.φ = spMap (dualMap (algebraMap V (FractionRing V))) ≫ (tv (bw i)).left := by
    apply a1.cart.1.hom_ext
    · rw [Category.assoc, ← e₁, reassoc_of% ρ₁, hbu, Category.assoc, hbw, ← Category.assoc, ← Category.assoc,
        spMap_comp', spMap_comp', ← FlagMod.dualMap_comp, ← FlagMod.dualMap_comp, hc]
    · rw [Category.assoc, mm.cart.1.w, reassoc_of% ρ₂, Category.assoc, tv_hom, Category.comp_id, spMap_comp',
        spMap_comp', PullbackSections.dualMap_comp_alg]
  rw [← reassoc_of% ρ₁, e₂, reassoc_of% k]

end Lie

theorem gm_eq_of_ev {F : Type} [Field F] {X X' : Scheme.{0}} (r : Sp F ⟶ X) (r' : Sp F ⟶ X') (z : Sp F) {U : X.Opens}
    {U' : X'.Opens} (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ r' ⁻¹ᵁ U') {a : Γ(X, U)ˣ} {a' : Γ(X', U')ˣ}
    (e : ev r U h a.val = ev r' U' h' a'.val) : gm r z U a = gm r' z U' a' := by
  have e' : (r.appLE U ⊤ h).hom a.val = (r'.appLE U' ⊤ h').hom a'.val :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1 e
  apply Units.ext
  rw [gm_val r z U (h trivial), gm_val r' z U' (h' trivial)]
  exact ((Sp F).presheaf.germ_res_apply (homOfLE h) z trivial _).symm.trans
    ((congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e').trans
      ((Sp F).presheaf.germ_res_apply (homOfLE h') z trivial _))

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {S : Type} [CommRing S]

theorem exists_spMap {T : Type} [CommRing T] (z : Sp T ⟶ Sp S) : ∃ φ : S →+* T, spMap φ = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem exists_unit_chart (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) (M : MChart Z) :
    ∃ u : Γ(Sp S, y ⁻¹ᵁ M.U)ˣ, ∀ (T : Type) [CommRing T] (φ : S →+* T) (h : ⊤ ≤ spMap φ ⁻¹ᵁ (y ⁻¹ᵁ M.U))
      (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x) (h' : ⊤ ≤ x ⁻¹ᵁ M.U),
      ev (spMap φ) _ h u.val = rdet ((basPull φ e b).toMatrix (lieBasis M x h')) := by
  have ha : IsAffineOpen (y ⁻¹ᵁ M.U) := by
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
    have h := isAffineOpen_inf_preimage Z.s y M.hU (isAffineOpen_top (Sp S))
    rwa [top_inf_eq] at h
  obtain ⟨τ, hτ⟩ := exists_spMap (tau ha)
  have h₀ : ⊤ ≤ (spMap τ ≫ y) ⁻¹ᵁ M.U := by rw [hτ]; exact le_preimage_map y le_rfl (tau_le _ le_rfl)
  refine ⟨(isUnit_rdet_toMatrix (basPull τ rfl b) (lieBasis M (spMap τ ≫ y) h₀)).unit, fun T _ φ h x e h' => ?_⟩
  have e₀ : spMap (ev (spMap φ) _ h) ≫ spMap τ = spMap φ := by rw [hτ]; exact spMap_ev _ ha h
  have e₁ : spMap (ev (spMap φ) _ h) ≫ spMap τ ≫ y = x := by rw [reassoc_of% e₀, e]
  have e₂ : (ev (spMap φ) _ h).comp τ = φ :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_comp' _ _).symm.trans e₀))
  have e₃ : basPull φ e b = basPull _ e₁ (basPull τ rfl b) := Module.Basis.eq_of_apply_eq fun i => by
    rw [basPull_apply, basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [e₂, e])]
    apply tan_ext_left
    rw [tanPull_left, tanPull_left, e₂]
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [e₃, Module.Basis.toMatrix_apply, ← tanPull_lieBasis M _ e₁ h₀ h', basPull_repr]
  rfl

theorem exists_gen_basis (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) :
    ∃ g : LB.Gen ((detOm Z).pull y), g.IsGen ∧ ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (g.s j).val = rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := by
  choose u hu using exists_unit_chart y b
  have le : ∀ j : PUnit → MChart Z, ((detOm Z).pull y).U j ≤ y ⁻¹ᵁ (j PUnit.unit).U := fun j =>
    LB.wchart_le (detOm Z) (fun _ : PUnit => y) j PUnit.unit
  have v : ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (res (le j) (u (j PUnit.unit))).val =
        rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := fun j T _ φ h x e h' =>
    (ev_res _ (le j) h (le_preimage_mono (le j) h) _).trans (hu _ T φ _ x e h')
  refine ⟨⟨fun j => res (le j) (u (j PUnit.unit))⟩, fun i j => Units.ext (ext_ev fun T _ z hz => ?_), v⟩
  obtain ⟨φ, rfl⟩ := exists_spMap z
  have hi := le_preimage_mono inf_le_left hz
  have hj := le_preimage_mono inf_le_right hz
  have hi' := le_preimage_map y (le i) hi
  have hj' := le_preimage_map y (le j) hj
  have g := ev_pull_g (detOm Z) y (spMap φ) i j hz (le_preimage_inf hi' hj')
  have d := ev_detChg (i PUnit.unit) (j PUnit.unit) _ hi' hj' (le_preimage_inf hi' hj')
  have o : ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') ((detOm Z).g (i PUnit.unit) (j PUnit.unit)).val *
      ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') (detChg (i PUnit.unit) (j PUnit.unit)).val = 1 :=
    (map_mul _ _ _).symm.trans ((congrArg _ (detChg (i PUnit.unit) (j PUnit.unit)).inv_mul).trans (map_one _))
  refine ((ev_res _ _ hz hi _).trans (v i T φ hi _ rfl hi')).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) g ((ev_res _ _ hz hj _).trans (v j T φ hj _ rfl hj')))).symm)
  rw [← rdet_toMatrix_mul _ (lieBasis (i PUnit.unit) _ hi') (lieBasis (j PUnit.unit) _ hj'), ← d, _root_.mul_left_comm]
  exact (_root_.mul_one _).symm.trans (congrArg _ o.symm)

theorem exists_detOm_gen_extAt {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z.X} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u Z.t x) :
    ∃ e : LB.Gen ((detOm Z).pull x), e.IsGen ∧ ExtAt (detOm Z) x e := by
  obtain ⟨n, b, hb⟩ := exists_basis_extends hu aT aC
  obtain ⟨e, he, ve⟩ := exists_gen_basis x b
  refine ⟨e, he, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨b', hb'⟩ := hb V hV ψ gam hg χ h
  obtain ⟨e', he', ve'⟩ := exists_gen_basis χ b'
  refine ⟨e', he', fun z J hJ => ?_⟩
  have top : ∀ {X : Scheme.{0}} (r : Sp (FractionRing V) ⟶ X) (U : X.Opens), r z ∈ U → ⊤ ≤ r ⁻¹ᵁ U := fun r U hz p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) p z]
    exact hz
  have h₀ := top _ _ (hJ (jK V ≫ χ))
  have h₁ : ⊤ ≤ spMap gam ⁻¹ᵁ ((detOm Z).pull x).U fun _ => J (jK V ≫ χ) :=
    top _ _ (mem_pull.2 (show (spMap gam ≫ x) z ∈ _ by rw [h]; exact hJ _))
  have h₂ : ⊤ ≤ jK V ⁻¹ᵁ ((detOm Z).pull χ).U fun _ => J (jK V ≫ χ) := top _ _ (mem_pull.2 (hJ (jK V ≫ χ)))
  rw [val_of e _ z J (fun _ => J (jK V ≫ χ)) (fun _ => by rw [h]), val_of e' _ z J (fun _ => J (jK V ≫ χ)) (fun _ => rfl)]
  refine gm_eq_of_ev _ _ z h₁ h₂ ((ve _ _ gam h₁ _ h h₀).trans (Eq.trans ?_ (ve' _ _ _ h₂ _ rfl h₀).symm))
  rw [show basPull gam h b = basPull (algebraMap V (FractionRing V)) rfl b' from
    Module.Basis.eq_of_apply_eq fun i => by rw [basPull_apply, basPull_apply, hb']]

end Gen

theorem exists_detOm_gen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ _ _ _ O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx
  have : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.toField.instIsLocalRing
    · infer_instance
  obtain ⟨tR, ⟨mt⟩⟩ := exists_sabPull χ₀ Y.t
  obtain ⟨u, ⟨n₀⟩⟩ := exists_sabPull x₀ Z.oF.t
  obtain ⟨aC, -⟩ := LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl
  obtain ⟨n₁, -⟩ := LevelCover.sab_comp n₀ Z.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl
  obtain ⟨n₃, -⟩ := LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := LevelCover.sab_cancel mt n₃ (jK _) hx
  have hu : IsProper u.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  exact exists_detOm_gen_extAt hu aT aC

end GlobalTheory.TraitGen
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_polarization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  first | exact @GlobalTheory.TraitGen.exists_detOm_gen_extends | exact GlobalTheory.TraitGen.exists_detOm_gen_extends | (intros; apply GlobalTheory.TraitGen.exists_detOm_gen_extends <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y Z : Scheme.{0}}

theorem tensGen_le₁ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (A.pull f).U (fun _ => (j PUnit.unit).1) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).1

theorem tensGen_le₂ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (B.pull f).U (fun _ => (j PUnit.unit).2) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).2

def tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) :
    LB.Gen ((GlobalTheory.CechPic.tens A B).pull f) where
  s j := res (tensGen_le₁ A B f j) (a.s _) * res (tensGen_le₂ A B f j) (b.s _)

theorem gm_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (j : PUnit → A.ι × B.ι) (hj : r z ∈ ((GlobalTheory.CechPic.tens A B).pull f).U j) :
    gm r z _ ((tensGen A B f a b).s j) =
      gm r z ((A.pull f).U (fun _ => (j PUnit.unit).1)) (a.s _) *
      gm r z ((B.pull f).U (fun _ => (j PUnit.unit).2)) (b.s _) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _) (gm_res r z _ hj _))

theorem tensGen_isGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f))
    (ha : a.IsGen) (hb : b.IsGen) : (tensGen A B f a b).IsGen := by
  refine (GlobalTheory.CechPic.isGen_iff_germ _).2 fun y i j hi hj => ?_
  have hi' := mem_pull.1 hi
  have hj' := mem_pull.1 hj
  have ai : y ∈ (A.pull f).U (fun _ => (i PUnit.unit).1) := mem_pull.2 hi'.1
  have aj : y ∈ (A.pull f).U (fun _ => (j PUnit.unit).1) := mem_pull.2 hj'.1
  have bi : y ∈ (B.pull f).U (fun _ => (i PUnit.unit).2) := mem_pull.2 hi'.2
  have bj : y ∈ (B.pull f).U (fun _ => (j PUnit.unit).2) := mem_pull.2 hj'.2
  rw [gm_tensGen A B f a b (𝟙 Y) y i hi, gm_tensGen A B f a b (𝟙 Y) y j hj,
    gm_pull_g (GlobalTheory.CechPic.tens A B) f (𝟙 Y) y i j hi hj, GlobalTheory.CechPic.gm_tens A B (𝟙 Y ≫ f) y _ _ hi' hj',
    (GlobalTheory.CechPic.isGen_iff_germ a).1 ha y _ _ ai aj,
    (GlobalTheory.CechPic.isGen_iff_germ b).1 hb y _ _ bi bj,
    gm_pull_g A f (𝟙 Y) y _ _ ai aj, gm_pull_g B f (𝟙 Y) y _ _ bi bj]
  exact mul_mul_mul_comm _ _ _ _

theorem val_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → A.ι × B.ι) (hJ : Good (GlobalTheory.CechPic.tens A B) z J) :
    val (L := GlobalTheory.CechPic.tens A B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) (tensGen A B f a b) r z J =
      val (L := A) (φ := fun _ : PUnit => f) (ε := fun _ => 1) a r z (fun ψ => (J ψ).1) *
      val (L := B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) b r z (fun ψ => (J ψ).2) :=
  gm_tensGen A B f a b r z _ (hJ.mem _ r)

theorem exists_tens_extAt : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  intro X A B R _ _ x eA eB hA hB hxA hxB
  refine ⟨tensGen A B x eA eB, tensGen_isGen A B x eA eB hA hB, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨a', ha', hva⟩ := hxA V hV ψ gam hg χ hχ
  obtain ⟨b', hb', hvb⟩ := hxB V hV ψ gam hg χ hχ
  refine ⟨tensGen A B χ a' b', tensGen_isGen A B χ a' b' ha' hb', fun z J hJ => ?_⟩
  have hJA : Good A z (fun ψ => (J ψ).1) := fun ψ => (hJ ψ).1
  have hJB : Good B z (fun ψ => (J ψ).2) := fun ψ => (hJ ψ).2
  rw [val_tensGen A B x eA eB _ z J hJ, val_tensGen A B χ a' b' _ z J hJ, hva z _ hJA, hvb z _ hJB]

end GlobalTheory.TraitGen
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_tensor : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  first | exact @GlobalTheory.TraitGen.exists_tens_extAt | exact GlobalTheory.TraitGen.exists_tens_extAt | (intros; apply GlobalTheory.TraitGen.exists_tens_extAt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y : Scheme.{0}}

theorem powPull_le (L : LB X) (m : ℕ) (χ : Y ⟶ X) (j : ((lbPow L m).pull χ).ι) :
    ((lbPow L m).pull χ).U j ≤ (L.pull χ).U (fun _ => j PUnit.unit PUnit.unit) := fun _ hy =>
  Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) PUnit.unit

def powPull (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) : LB.Gen ((lbPow L m).pull χ) where
  s j := res (powPull_le L m χ j) (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m

theorem gm_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (j : ((lbPow L m).pull χ).ι) (h : r z ∈ ((lbPow L m).pull χ).U j) :
    gm r z _ ((powPull L m χ e).s j) = gm r z _ (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m :=
  (map_pow _ _ _).trans (congrArg (· ^ m) (gm_res r z _ h _))

theorem gm_powPull_g {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j j' : ((lbPow L m).pull χ).ι) (hj : r z ∈ ((lbPow L m).pull χ).U j)
    (hj' : r z ∈ ((lbPow L m).pull χ).U j') :
    gm r z _ (((lbPow L m).pull χ).g j j') =
      trF (L := L) (fun _ : PUnit => χ) (fun _ => 1) r z (fun _ => j PUnit.unit PUnit.unit)
        (fun _ => j' PUnit.unit PUnit.unit) ^ m := by
  refine (gm_pull_g (lbPow L m) χ r z j j' hj hj').trans ?_
  refine (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (m : ℤ)) (r ≫ χ) z (j PUnit.unit) (j' PUnit.unit)
    (Set.mem_iInter.1 hj PUnit.unit) (Set.mem_iInter.1 hj' PUnit.unit)).trans ?_
  simp only [trF, Fintype.prod_unique, Category.comp_id, zpow_natCast, zpow_one]

theorem powPull_isGen (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (he : e.IsGen) :
    (powPull L m χ e).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have hj := powPull_le L m χ j hy.1
  have hj' := powPull_le L m χ j' hy.2
  have ht := gen_trans (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (t := e) he (𝟙 Y) y hj hj'
  refine (gm_res _ y _ hy _).trans ?_
  refine (gm_powPull L m χ e (𝟙 Y) y j hy.1).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  rw [gm_powPull_g L m χ (𝟙 Y) y j j' hy.1 hy.2, gm_res _ y _ hy, gm_powPull L m χ e (𝟙 Y) y j' hy.2, ← mul_pow]
  exact congrArg (· ^ m) ht

theorem val_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → (lbPow L m).ι) (hJ : Good (lbPow L m) z J) :
    val (L := lbPow L m) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (powPull L m χ e) r z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e r z (fun ψ => J ψ PUnit.unit) ^ m :=
  gm_powPull L m χ e r z _ (hJ.mem (fun _ : PUnit => χ) r)

theorem extAt_lbPow (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ) (he : e.IsGen) (hx : GlobalTheory.TraitGen.ExtAt L x e) :
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  refine ⟨powPull L m x e, powPull_isGen L m x e he, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨e₁, h₁, hv⟩ := hx V hV ψ gam hg χ hχ
  refine ⟨powPull L m χ e₁, powPull_isGen L m χ e₁ h₁, fun z J hJ => ?_⟩
  rw [val_powPull L m x e _ z J hJ, val_powPull L m χ e₁ _ z J hJ]
  exact congrArg (· ^ m) (hv z (fun ψ => J ψ PUnit.unit) fun ψ => Set.mem_iInter.1 (hJ ψ) PUnit.unit)

end GlobalTheory.TraitGen
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_power : ∀ (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ), e.IsGen → GlobalTheory.TraitGen.ExtAt L x e →
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  first | exact @GlobalTheory.TraitGen.extAt_lbPow | exact GlobalTheory.TraitGen.extAt_lbPow | (intros; apply GlobalTheory.TraitGen.extAt_lbPow <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_along_dvr_arcs : ∀ (X : Scheme.{0}) (BD : GlobalTheory.EffCartierData X) (R : Type) [CommRing R] [IsDomain R] (u : R), u ≠ 0 →
    ∀ (x : Sp (FractionRing R) ⟶ X) (n : ℕ),
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ u ^ n}) →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.dual BD.lb).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.dual BD.lb) x e := by
  first | exact @GlobalTheory.TraitGen.exists_dual_gen_extAt | exact GlobalTheory.TraitGen.exists_dual_gen_extAt | (intros; apply GlobalTheory.TraitGen.exists_dual_gen_extAt <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitGen

theorem exists_polGen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ n : ℕ, (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n}) →
  ∃ e : LB.Gen ((polOf Z m BD).pull (x₀ ≫ Z.j)), e.IsGen ∧
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → ∃ e' : LB.Gen ((polOf Z m BD).pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good (polOf Z m BD) z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => x₀ ≫ Z.j) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hB hC x₀ hx₀ n hn
  obtain ⟨e₁, he₁, hx₁⟩ := GlobalTheory.T.pullback_model_arc_polarization E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv O' b' ϖ a χ₀ hB hC x₀ hx₀
  obtain ⟨e₂, he₂, hx₂⟩ := GlobalTheory.T.generator_extends_power _ _ _ _ e₁ m he₁ hx₁
  obtain ⟨e₃, he₃, hx₃⟩ := GlobalTheory.T.ideal_along_dvr_arcs Z.X BD (PowerSeries O') PowerSeries.X PowerSeries.X_ne_zero (x₀ ≫ Z.j) n hn
  obtain ⟨e, he, hx⟩ := GlobalTheory.T.generator_extends_tensor _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃
  exact ⟨e, he, hx⟩

end GlobalTheory.TraitGen
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_limit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ n : ℕ, (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n}) →
  ∃ e : LB.Gen ((polOf Z m BD).pull (x₀ ≫ Z.j)), e.IsGen ∧
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → ∃ e' : LB.Gen ((polOf Z m BD).pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good (polOf Z m BD) z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => x₀ ≫ Z.j) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J := by
  atlas_forward_decl GlobalTheory.TraitGen.exists_polGen_extends
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArcExtend

theorem powerSeries_props (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') (h : IsArcBase O' ϖ) :
    ∃ (_ : IsLocalRing (PowerSeries O')), IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
  rcases h with ⟨hF, -⟩ | ⟨hD, -, -⟩
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩

theorem spMap_jK' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨_, _, _⟩ := powerSeries_props O' ϖ hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have := isProper_toroidalModel_structureMap Z
  have : CompactSpace Z.X := hpol.2.compactSpace
  have : QuasiSeparatedSpace Z.X := quasiSeparatedSpace_of_quasiSeparated Z.s
  have eF : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    ext x
    exact congrArg (fun y : c.F => (y : ℂ)) (hbV x).symm
  have hZs : x₀ ≫ Z.j ≫ Z.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    have hY : x₀ ≫ Y.j ≫ Y.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
      rw [← Category.assoc, ← hx₀, Category.assoc, hχ₀.1]
    rw [Model.j_s] at hY ⊢
    rw [eF]
    simp only [← Category.assoc] at hY ⊢
    rw [hY]
  obtain ⟨n, hn⟩ := GlobalTheory.T.pullback_model_arc_period E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ a
    χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨e, he, htr⟩ := GlobalTheory.T.pullback_model_arc_limit E H D l Xo c p W hp hpW Z Y bV hbV f t m₁ m₂ hfs hgen huniv φ m BD hhom hpol O' b' ϖ
    a χ₀ hO hχ₀ x₀ hx₀ n hn
  refine GlobalTheory.T.generic_section_extends_normal Z.X (polOf Z m BD) hpol.2.isLB (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) (PowerSeries O')
    (x₀ ≫ Z.j) e he fun V _ _ _ hV ψ gam hg => ?_
  have := hV.1
  obtain ⟨χ, hχ, -⟩ := val_exists Z.s (spMap gam ≫ x₀ ≫ Z.j)
    (spMap ψ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK' hg, Category.assoc])
  exact ⟨χ, hχ.symm, htr V hV ψ gam hg χ hχ.symm⟩

end GlobalTheory.PolArcExtend
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  atlas_forward_decl GlobalTheory.PolArcExtend.extend
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.PolArcExist

theorem j_s {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

instance isDominant_jK (R : Type) [CommRing R] [IsDomain R] : IsDominant (Out.jK R) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hz : (Out.jK R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R (FractionRing R)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (Out.jK R) := ⟨_, hz⟩
  exact closure_mono (Set.singleton_subset_iff.2 hmem)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal R) ≤ y.asIdeal from bot_le))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∃ χV : Sp (PowerSeries O') ⟶ pullback Z.s (spMap bV),
          χV ≫ f = χ₀ ∧ χV ≫ pullback.snd Z.s (spMap bV) = spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ h1 h2 h3 φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hbase hχ₀
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.power_series_arc_abelian_locus E H D l Xo c W Y O' b' χ₀ hχ₀.1 hχ₀.2.1
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.pullback_model_arc_torus E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ h1 h2 h3 φ m BD hhom hpol O' b' ϖ a χ₀
    hbase hχ₀ x₀ hx₀
  have hsub : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← spMap_comp]
    congr 1
    exact RingHom.ext fun x => hbV x

  have hgen : Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' =
      x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype := by
    rw [← hχ₀.1, ← Category.assoc, hx₀, Category.assoc, j_s]
  have hs : χ ≫ Z.s = (spMap (PowerSeries.C (R := O')) ≫ spMap b') ≫ spMap bV := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, j_s, ← hsub]
    simp only [← Category.assoc] at hgen ⊢
    rw [← hgen]
  let aj : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) (by rw [j_s, Category.assoc, hsub])
  have haj : aj ≫ f = Y.j := h2 aj (pullback.lift_fst _ _ _)
  refine ⟨pullback.lift χ _ hs, ?_, pullback.lift_snd _ _ _⟩
  have := isProper_toroidalModel_structureMap Y
  refine ext_of_isDominant_of_isSeparated Y.s ?_ (Out.jK (PowerSeries O')) ?_
  · rw [Category.assoc, h1, pullback.lift_snd, hχ₀.1]
  · have e : Out.jK (PowerSeries O') ≫ pullback.lift χ _ hs = x₀ ≫ aj := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hχ, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hgen]
    rw [← Category.assoc, e, Category.assoc, haj, hx₀]
end GlobalTheory.PolArcExist
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

theorem exists_sab_comp_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t' (𝟙 S')) : ∃ m' : SABMap t'' t f, m'.φ = n.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_comp m n
  exact ⟨Category.id_comp f ▸ m', (sabMap_cast_φ (Category.id_comp f) m').trans hm'⟩

theorem isArcChart_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)),
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j → IsArcChart Z a ϖ χ := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀ χ hχ
  have hPS : IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
    rcases hO with ⟨hF, -⟩ | ⟨hD, -, -⟩
    · letI := hF.toField
      exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
    · exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  haveI := hPS.1
  haveI := hPS.2
  obtain ⟨t, m₁, m₂, hc⟩ := GlobalTheory.T.integral_point_pullback_comparison E H D l Xo c W Z Y bV hbV (PowerSeries O') χ χ₀ x₀ hχ hx₀
  haveI := GlobalTheory.PolArcData.mono_spMap_incl bV hbV
  have eF := GlobalTheory.PolArcData.spMap_algebraMap_eq bV hbV
  haveI : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [eF]
    haveI := mono_spMap_subtype (c.V W)
    infer_instance
  have hZj : Mono Z.j := GlobalTheory.ThetaShiftProofs.mono_j Z inferInstance
  have hab : ∀ x, χ x ∈ abLocus Z.t.G ↔ χ₀ x ∈ abLocus Y.t.G := fun x =>
    (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 x).trans (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 x).symm

  have h1 : χ ≫ Z.s = spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV) := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK (PowerSeries O')) ?_
    have e1 : Out.jK (PowerSeries O') ≫ χ ≫ Z.s = x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
      rw [← Category.assoc, hχ, Category.assoc, Model.j_s, eF]
    have e2 : Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV) =
        x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
      calc Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap (b'.comp bV)
          = (Out.jK (PowerSeries O') ≫ χ₀) ≫ Y.s ≫ spMap bV := by
            rw [spMap_comp, Category.assoc, ← Category.assoc χ₀, hχ₀.1]; simp only [Category.assoc]
        _ = x₀ ≫ pullback.snd _ _ ≫ spMap (c.V W).subtype ≫ spMap bV := by
            rw [hx₀, Category.assoc, ← Category.assoc Y.j, Model.j_s]; simp only [Category.assoc]
    rw [e1, e2]

  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Z.t.G ↔ PowerSeries.X ∉ x.asIdeal := fun x =>
    (hab x).trans (hχ₀.2.1 x)

  have h3 : ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Z.j := by
    intro x hx
    obtain ⟨q, hq⟩ := hχ₀.2.2.1 x hx
    have hab' : χ x ∈ abLocus Z.t.G := (hab x).2 (hq ▸ GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y q)
    have k1 : (χ ≫ Z.s) x = (χ₀ ≫ Y.s ≫ spMap bV) x := by
      rw [h1, ← Category.assoc, hχ₀.1, spMap_comp, Category.assoc]
    have k2 : (Y.j ≫ Y.s ≫ spMap bV) q = (pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)) q := by
      rw [← Category.assoc, Model.j_s, eF, Category.assoc]
    have hs : Z.s (χ x) ∈ Set.range (spMap (algebraMap (𝓞 c.F) c.F)) := by
      refine ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) q, ?_⟩
      simp only [Scheme.Hom.comp_apply] at k1 k2
      rw [← k2, hq, k1]
    obtain ⟨r, hr⟩ : χ x ∈ Set.range (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
      rw [Scheme.Pullback.range_fst]; exact hs
    have hr' : r ∈ Set.range Z.jQ := by
      rw [← Z.ab_gen, Set.mem_preimage, hr]; exact hab'
    obtain ⟨z, rfl⟩ := hr'
    exact ⟨z, by rw [Model.j, Scheme.Hom.comp_apply, hr]⟩

  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := hχ₀.2.2.2
  obtain ⟨n, hn⟩ := exists_sab_cancel_id m₂ m'
  obtain ⟨mZ, hmZ⟩ := exists_sab_comp_id m₁ n
  refine ⟨t', mZ, P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
    ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
  have hyx : yF = Out.jFK (R := PowerSeries O') F ≫ x₀ := by
    rw [← cancel_mono Z.j, hyF, Category.assoc, hχ]
  have hyY : yF ≫ Y.j = Out.jFK (R := PowerSeries O') F ≫ Out.jK (PowerSeries O') ≫ χ₀ := by
    rw [hyx, Category.assoc, ← hx₀]
  have go : ∀ σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK (PowerSeries O')) ≫ m'.φ = yF ≫ σY.left ≫ Y.m.φ := by
    intro σY h0
    have b₁ : σ.left ≫ Z.oF.t.G.hom = 𝟙 _ := Over.w σ
    have b₂ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
    have := hc _ (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK (PowerSeries O')) ≫ n.φ)
      (yF ≫ σ.left) (yF ≫ σY.left) (by rw [hmZ] at e4; simpa only [Category.assoc] using e4)
      (by rw [Category.assoc, h0, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂])
    rw [hn]; simpa only [Category.assoc] using this
  rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
  · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
  · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
      (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))

end GlobalTheory.ArcChartExt
end
end
