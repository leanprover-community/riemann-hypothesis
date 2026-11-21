import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds

section
namespace GlobalTheory


end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagExpZero

open GlobalTheory.FrameTwistCompare (lin quad)
open MvPowerSeries (constantCoeff pderiv)

section Flat

variable {S : Type} [CommRing S] {σ : Type}

def Flat (f : MvPowerSeries σ S) : Prop := constantCoeff f = 1 ∧ ∀ v, lin v f = 0

theorem flat_one : Flat (1 : MvPowerSeries σ S) := ⟨map_one _, fun v => by simp [lin]⟩

theorem quad_one (v w : σ) : quad v w (1 : MvPowerSeries σ S) = 0 := by simp [quad]

theorem Flat.mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) : Flat (f * g) := by
  refine ⟨by rw [map_mul, hf.1, hg.1, _root_.mul_one], fun v => ?_⟩
  have h1 := hf.2 v
  have h2 := hg.2 v
  unfold lin at h1 h2 ⊢
  simp [Derivation.leibniz, h1, h2]

theorem Flat.quad_mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) (v w : σ) :
    quad v w (f * g) = quad v w f + quad v w g := by
  have h1 := hf.2 v
  have h2 := hg.2 v
  have h3 := hf.2 w
  have h4 := hg.2 w
  unfold lin at h1 h2 h3 h4
  simp [quad, Derivation.leibniz, h1, h2, h3, h4, hf.1, hg.1, add_comm]

theorem Flat.pow {f : MvPowerSeries σ S} (hf : Flat f) (q : ℕ) :
    Flat (f ^ q) ∧ ∀ v w, quad v w (f ^ q) = q * quad v w f := by
  induction q with
  | zero => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | succ q ih =>
    refine ⟨by rw [pow_succ]; exact ih.1.mul hf, fun v w => ?_⟩
    rw [pow_succ, ih.1.quad_mul hf, ih.2]
    push_cast
    ring

theorem flat_finprod {J : Type} (s : Finset J) {f : J → MvPowerSeries σ S} (hf : ∀ i, Flat (f i)) :
    Flat (∏ i ∈ s, f i) ∧ ∀ v w, quad v w (∏ i ∈ s, f i) = ∑ i ∈ s, quad v w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | insert a s ha ih =>
    refine ⟨by rw [Finset.prod_insert ha]; exact (hf a).mul ih.1, fun v w => ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (hf a).quad_mul ih.1, ih.2]

theorem quad_eq_zero {f : MvPowerSeries σ S}
    (h : ∀ e : σ →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e (f - 1) = 0) (v w : σ) : quad v w f = 0 := by
  have h1 : quad v w (f - 1) = 0 := by
    simp only [quad, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    rw [h _ (by simp)]
    simp
  simpa [quad] using h1

end Flat

open GlobalTheory.FrameTwistCompare in
theorem flat_ev_twist {S : Type} [CommRing S] [Algebra ℚ S] {n d : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S)
    {a : Fin 2 → Pt S n d} (ha : TB.LogPf.CZ a) : Flat (ev a (expP (-bilL G c))) := by
  refine ⟨cc_ev_twist G c ha, fun v => ?_⟩
  have h0 := cc_comp1_log G (ha 0)
  have h1 := cc_comp1_log G (ha 1)
  rw [ev_expP G c ha, ev_bilL_eq G c ha, bilLog_eq_bil, lin_exp]
  · have := lin_bil (c := c) h0 h1 v
    unfold lin at this ⊢
    rw [map_neg, map_neg, this, neg_zero]
  · rw [map_neg, cc_bil h0, neg_zero]

theorem form_eq_zero_of_diag_exp : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (d : ℕ) (G : FGLaw S d) (w w' : Pt S 1 d), (∀ i, MvPowerSeries.constantCoeff (w i) = 0) → dLin w + dLin w' = 1 → ∀ c : Fin d → Fin d → S, (∀ i j, c i j = c j i) → Matrix.transpose (dLin w) * Matrix.of c = Matrix.of c * dLin w' → ∀ (n q : ℕ), 1 ≤ n → 1 ≤ q → (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e ((∏ i : Fin n, ev (n := n) ![pt S d i, comp1 w (pt S d i)] (expP (-bilL G c)) ^ q) - 1) = 0) → c = 0 := by
  intro S _ _ d G w w' hw hsum c hsym hbal n q hn hq h
  have hz : ∀ i : Fin n, TB.LogPf.CZ (![pt S d i, comp1 w (pt S d i)] : Fin 2 → Pt S n d) := by
    intro i j k
    fin_cases j
    · exact FrameTwistCompare.cc_pt i k
    · exact TB.WickVanishing.cc_comp1 _ _ hw (FrameTwistCompare.cc_pt i) k
  have hfl := fun i => flat_ev_twist G c (hz i)
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hu : IsUnit (q : S) := by
    have := (IsUnit.mk0 (q : ℚ) (by exact_mod_cast (by omega : q ≠ 0))).map (algebraMap ℚ S)
    rwa [map_natCast] at this
  have key : ∀ a b, (Matrix.of c * dLin w) a b + (Matrix.of c * dLin w) b a = 0 := by
    intro a b
    have h2 := quad_eq_zero h (i₀, a) (i₀, b)
    rw [(flat_finprod _ fun i => ((hfl i).pow q).1).2, Finset.sum_eq_single i₀, ((hfl i₀).pow q).2,
      hu.mul_right_eq_zero, FrameTwistCompare.quad_ev_twist G c (hz i₀), neg_eq_zero] at h2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        FrameTwistCompare.lin_comp1 _ (FrameTwistCompare.cc_pt _), FrameTwistCompare.lin_pt] at h2
      simp only [Matrix.mul_apply, Matrix.of_apply]
      simpa [mul_add, Finset.sum_add_distrib] using h2
    · intro i _ hi
      rw [((hfl i).pow q).2, FrameTwistCompare.quad_ev_twist G c (hz i)]
      simp [FrameTwistCompare.lin_pt, hi.symm]
    · simp
  have ht : (Matrix.of c).transpose = Matrix.of c := Matrix.ext fun i j => hsym j i
  have h3 : Matrix.of c * dLin w + Matrix.of c * dLin w' = 0 := by
    rw [← hbal]
    have e : (dLin w).transpose * Matrix.of c = (Matrix.of c * dLin w).transpose := by
      rw [Matrix.transpose_mul, ht]
    rw [e]
    exact Matrix.ext fun a b => key a b
  rw [← Matrix.mul_add, hsum, Matrix.mul_one] at h3
  exact h3

end GlobalTheory.DiagExpZero
end
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermRatio
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

theorem clause_along {X' Y Y₁ Z : Scheme.{0}} {M' : LB X'} (g : Y₁ ⟶ X') (z : Y ⟶ Y₁) (q : ℤ)
    (σ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => g) (fun _ => q))) (a : Γ(Y, ⊤))
    (τ : LB.Gen (LB.LinComb M' (K := PUnit.{1}) (fun _ => z ≫ g) (fun _ => q)))
    (H : ∀ j : Fin 1 → M'.ι, (Y.presheaf.map (homOfLE (ExpBijectiveUniformisation.wchart_comp_le M' g z j)).op).hom ((z.app _).hom (σ.f j)) =
      (Y.presheaf.map (homOfLE le_top).op).hom a * (τ.s (fun _ => j 0)).val) (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M' y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ r y J).val := by
  have hy : r y ∈ LB.wchart M' (fun _ : PUnit.{1} => z ≫ g) (fun _ => J (r ≫ z ≫ g)) := hJ.mem _ r
  have e := congrArg (gs r y _) (H (fun _ => J (r ≫ z ≫ g)))
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc])]
  exact ((gs_res _ y _ hy _).trans (gs_pull r z y _ (ExpBijectiveUniformisation.wchart_comp_le M' g z (fun _ => J (r ≫ z ≫ g)) hy) _)).symm.trans
    (e.trans ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]

theorem val_cast_prod_along (t : SAB H (Sp V)) {n : ℕ}
    (L : LB t.G.left) (h : t.PP.L = L) {Y Y₀ Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y₀ ⟶ t.G.left)) (ε : K → ℤ)
    (e : LB.Gen (LB.LinComb t.PP.L φ ε)) (q : ℕ) (r : Fin n → (Y ⟶ Y₀)) (ρ : Z ⟶ Y) (y : Z) (J) (hJ : Good L y J) :
    val (genCast h _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i))) ρ y J = ∏ i, val (genCast h _ _ e) (ρ ≫ r i) y J ^ q := by
  subst h
  show val (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
      LB.pullGen t.PP.L _ _ (genPowG t _ _ e q) (r i)) ρ y J = ∏ i, val e (ρ ≫ r i) y J ^ q
  rw [val_finProd _ _ _ _ _ hJ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [val_pull hJ, GermD.val_genPowG]

theorem val_eL_ratio {t : SAB H (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {FT : Fin d → PS V 2 d}
    {act : 𝓞 E → Fin d → PS V 1 d} {tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)} {uv : Fin d → Fin d → V}
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (wP : PrimTyG t) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m)
    (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (hU : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (e m)))
    (L : LB t.G.left) (h : t.PP.L = L) {Z : Scheme.{0}} (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (y : Z) (J)
    (hJ : Good L y J) :
    val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP (m + 1))) (r ≫ (GermD.ρT (𝟙 (Sp V)) d m).left) y J =
      gm (r ≫ (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left) y ⊤ (unitΓ U) *
        val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) r y J := by
  subst h
  have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (homAt (𝟙 (Sp V)) (GermD.sL (m + 1) (act H.w0))).left =
      (homAt (𝟙 (Sp V)) (GermD.sL m (act H.w0))).left ≫
        (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, GermD.homAt_comp, GermD.homAt_comp, GermD.sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (val_mul hJ _ _ _).symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun s => val wP s y J)
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hx))).trans (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun s => val (e (m + 1)) s y J)
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.assoc _ _ _).symm))).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ hU _).trans
        ((GermB.val_scale t _ _ _ _ _ y J hJ).trans (congrArg (_ * ·) (val_pull hJ (e m) _ _).symm)))))

theorem trunc_jcN (F : Type) [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m) ≫ jcN V F d n (m + 1) i =
      jcN V F d n m i ≫ (GermD.ρT (𝟙 (Sp V)) d m).left := by
  rw [← coef_cpy, ← coef_cpy, ← Category.assoc, GermBasic.spMap_comp_eq, JetTr.jetCoef_trunc,
    ← GermBasic.spMap_comp_eq, Category.assoc, trunc_cpy, Category.assoc]
  rfl

theorem cst_prod_pow {A : Type} [CommRing A] {Z : Scheme.{0}} (r : Z ⟶ Sp A) (y : Z) {n : ℕ} (a : Fin n → A) (q : ℕ) :
    cst r y (∏ i, a i ^ q) = ∏ i, cst r y (a i) ^ q := by
  simp only [cst, gs_eq r y ⊤ trivial, map_prod, map_pow]

section Germ

variable [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} {P : PELUnif I t} {d : ℕ}
  {xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS V 1 d} {eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m} {wPT : PrimTyG t}
  {n : ℕ} {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)}
  [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' t.G n}
  {U' : Unif I D' A' G'} {PU : UnifPowOf pD pA pG U' P.U}
  {F : Type} [Field F] [Algebra (FractionRing V) F] [Algebra V F] {q : ℕ} {σ' : U'.toUnifPre.SecGF F q} {f : PS F n d}

theorem val_of_germ (h : IsGermN P xT act eT wPT pG PU F q σ' f) (m : ℕ) :
    ∃ z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
        spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
      (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J → Good U'.LG.L y J' →
        (om (pr := fun i => (pG.pr i).left) PU.wL y J J' ((r ≫ z) ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val *
          sval σ' (r ≫ z) y J' =
          cst r y (psJet m f) * (∏ i, val (genCast (congrArg RigLB.L P.bundle).symm _ _
            (eLG t (𝟙 (Sp V)) d xT act eT wPT m)) (r ≫ jcN V F d n m i) y J ^ q).val := by
  obtain ⟨z, τ, b, h₀, h₁, h₂, h₃, h₄⟩ := h m
  refine ⟨z, h₀, h₁, fun Z r y J J' hJ hJ' => ?_⟩
  have e₁ := mapsAt_val (pr := fun i => (pG.pr i).left) PU.wL _ _ τ b h₂ r y hJ hJ'
  have e₂ := (val_corr hJ ((corr_genCast _ _ _).1 h₃) r).trans (val_cast_prod_along t _ _ _ _ _ q _ r y J hJ)
  rw [clause_along _ z _ σ' _ τ h₄ r y J' hJ', mul_left_comm, e₂.symm.trans e₁, Category.assoc, zpow_natCast,
    Units.val_mul]
  rfl

omit [IsCommMonObj G'] in
theorem gFK_hom : UnifPre.gFK (R := V) (G := G') F ≫ G'.hom =
    (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left ≫
      (TFK (R := V) F).hom ≫ jK V := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, Over.w]
  exact congrArg (· ≫ jK V) (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G')))

end Germ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (t : SAB H (Sp V)) (P : PELUnif I t) (d n : ℕ) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V), IsChartG t (𝟙 (Sp V)) d FT act tg uv xT → ∀ (wPT : PrimTyG t), IsPrimG t wPT → ∀ (D' : DegData V I) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif I D' A' G') (PU : UnifPowOf pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n d) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m), (∀ m, (eT m).IsGen) → IsGermN P xT act eT wPT pG PU F q σ' h → ∀ (m : ℕ) (U : (Jet V (Fin 2 × Fin d) m)ˣ), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (eT (m + 1)) (homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _)).left) (scaleGenG t _ _ (unitΓ U) (eT m)) → psJet m h * ∏ i : Fin n, (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q = psJet m h := by
  intro E _ _ _ H V _ _ I t P d n xT FT act tg uv hch wPT _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ q σ' h eT _ hg m U hU
  obtain ⟨z₁, a₁, b₁, c₁⟩ := val_of_germ hg (m + 1)
  obtain ⟨z₀, a₀, b₀, c₀⟩ := val_of_germ hg m
  let ρ := spMap ((jetTrunc : Jet F (Fin n × Fin d) (m + 1) →ₐ[F] Jet F (Fin n × Fin d) m) :
        Jet F (Fin n × Fin d) (m + 1) →+* Jet F (Fin n × Fin d) m)
  have hf : (ρ ≫ z₁) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      (𝟙 _ ≫ z₀) ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left := by
    rw [Category.assoc, a₁, Category.id_comp, a₀]
    exact spMap_comp_alg _
  have hz : ρ ≫ z₁ = 𝟙 _ ≫ z₀ := by
    refine GermBasic.gf_ext hf (pow_ext pG _ _ ?_ fun i => ?_)
    · rw [Category.assoc, Category.assoc _ (UnifPre.gFK (R := V) (G := G') F), gFK_hom, ← Category.assoc, hf,
        Category.assoc]
    · have hx : (GermD.ρT (𝟙 (Sp V)) d m).left ≫ (xT (m + 1)).left = (xT m).left := by
        rw [← Over.comp_left, hch.trunc m]
      rw [Category.id_comp, Category.assoc, Category.assoc, b₁, Category.assoc, b₀, jptN, jptN, ← Category.assoc,
        trunc_jcN, Category.assoc, hx]
  refine H1.cst_ext fun y => ?_
  obtain ⟨J, hJ⟩ := exists_good_at P.U.LG.isLB y
  obtain ⟨J', hJ'⟩ := exists_good_at U'.LG.isLB y
  have e₁ := c₁ _ ρ y J J' hJ hJ'
  have e₀ := c₀ _ (𝟙 _) y J J' hJ hJ'
  rw [hz, e₀] at e₁
  have k : cst ρ y (psJet (m + 1) h) = cst (𝟙 _) y (psJet m h) :=
    (H1.gs_spec _ y _).trans (congrArg (cst (𝟙 _) y) (FrRatio.psJet_trunc m h))
  have l := fun i => (congrArg (fun s => val (genCast (congrArg RigLB.L P.bundle).symm _ _
      (eLG t (𝟙 (Sp V)) d xT act eT wPT (m + 1))) s y J) (trunc_jcN F d n m i)).trans
    (val_eL_ratio hch wPT eT m U hU _ (congrArg RigLB.L P.bundle).symm (jcN V F d n m i) y J hJ)
  rw [k, Finset.prod_congr rfl fun i _ => congrArg (· ^ q) (l i)] at e₁
  simp only [Category.id_comp, mul_pow, Finset.prod_mul_distrib, Units.val_mul, ← _root_.mul_assoc] at e₁
  refine Eq.trans ?_ ((Units.mul_left_inj _).1 e₁).symm
  rw [H1.cst_mul, cst_prod_pow, Units.coe_prod]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  rw [Units.val_pow_eq_pow_val]
  refine congrArg (· ^ q) (Eq.trans ?_ (gs_unit _ y ⊤ trivial _))
  exact ((ExpansionValueZero.cst_comp (jcN V F d n m i) _ y _).trans (H1.gs_spec _ y _)).symm

end GlobalTheory.GermRatio
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEventually

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

section Jets

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem mk_eq_zero_iff (p : MvPolynomial ι R) :
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, show orig R ι = MvPolynomial.idealOfVars ι R from rfl,
    MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE [Fintype ι] [DecidableEq ι] (e : ι →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]

theorem coeff_eq_of_psJet_eq [Fintype ι] [DecidableEq ι] {f g : MvPowerSeries ι R} (h : psJet m f = psJet m g)
    (e : ι →₀ ℕ) (he : e.degree ≤ m) : MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by
  rw [← sub_eq_zero, psJet, psJet, ← map_sub, mk_eq_zero_iff] at h
  have := h e he
  rwa [coeff_sub, coeff_psTrunc, coeff_psTrunc, if_pos he, if_pos he, sub_eq_zero] at this

theorem psJet_prod [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α] (S : Finset α) (g : α → MvPowerSeries ι R) :
    psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]

theorem psJet_pow [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

variable {K : Type} [CommRing K] (f : R →+* K)

theorem jetCoef_injective (hf : Function.Injective f) : Function.Injective (jetCoef f ι m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [JetTr.jetCoef_mk, mk_eq_zero_iff] at ha
  rw [mk_eq_zero_iff]
  intro e he
  apply hf
  rw [map_zero, ← ha e he, coeff_map]

theorem map_psIn {d n n' : ℕ} (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) R) :
    MvPolynomial.map f (psIn d m r g) = psIn d m r (MvPowerSeries.map f g) := by
  rw [psIn, psIn, map_rename, JetTr.psTrunc_map]

theorem jetCoef_subst2 {d : ℕ} {κ : Type} (u v : Fin d → MvPolynomial κ R) (u' v' : Fin d → MvPolynomial κ K)
    (hu : ∀ j, MvPolynomial.map f (u j) = u' j) (hv : ∀ j, MvPolynomial.map f (v j) = v' j)
    (a : Jet R (Fin 2 × Fin d) m) :
    jetCoef f κ m (jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) a) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2)
        (jetCoef f (Fin 2 × Fin d) m a) := by
  have e : (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2) =
      fun p : Fin 2 × Fin d => MvPolynomial.map f ((![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) := by
    funext ⟨i, j⟩
    fin_cases i
    · exact (hu j).symm
    · exact (hv j).symm
  rw [e]
  exact RingHom.congr_fun (JetTr.jetCoef_substP f m _) a

end Jets

section Rat

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem jetCopy_psJet {n : ℕ} (m : ℕ) (i : Fin n) (g : PS S 1 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (psJet m g) =
      psJet m (ev (n := n) ![pt S d i] g) := by
  rw [← jetSubstP_psJet m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) ![pt S d i]
    (fun ⟨a, j⟩ => by fin_cases a; exact cc_pt' i j) (fun p => by simp)
    (fun ⟨a, j⟩ => by fin_cases a; exact mk_X_psJet m (i, j))]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  simp only [jetCopy, jetSubstP, GermD.jetMap_mk, aeval_X, constantCoeff_X, map_zero, sub_zero]

theorem jetCopy_graph {n : ℕ} (m : ℕ) (i : Fin n) (w : Pt S 1 d) (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0)
    (g : PS S 2 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m)
      (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (w j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) (psJet m g)) =
      psJet m (ev (n := n) ![pt S d i, comp1 w (pt S d i)] g) := by
  have hr : (![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) = fun i => pt S d ((![0] : Fin 1 → Fin 1) i) := by
    funext i; fin_cases i; rfl
  have ha : ∀ a j, MvPowerSeries.constantCoeff
      ((![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) a j) = 0 := by
    intro a j; fin_cases a
    · exact cc_pt' _ j
    · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_comp1 _ _ hw (fun i => cc_pt' _ i) j
  have hb : ∀ a j, MvPowerSeries.constantCoeff ((![pt S d i] : Fin 1 → Pt S n d) a j) = 0 := by
    intro a j; fin_cases a; exact cc_pt' _ j
  rw [jetSubstP_psJet m _ (![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) (fun p => ha p.1 p.2)
      (fun ⟨a, j⟩ => by
        fin_cases a
        · simp
        · show constantCoeff (psIn d m ![0] (w j)) = 0
          rw [FBIdPh.cc_psIn, hw])
      (fun ⟨a, j⟩ => by
        fin_cases a
        · exact mk_X_psJet m _
        · show _ = psJet m (ev ![pt S (n := 1) d 0] (w j))
          rw [hr]
          exact mk_psIn_psJet m _ _),
    jetCopy_psJet, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_ev _ _ ha hb]
  congr 2
  funext a j
  fin_cases a
  · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_X _ hb 0 j
  · exact ev_at _ hb 0 (w j)

end Rat

theorem unit_eq_one {V F : Type} [CommRing V] [Field F] [CharZero F] [Algebra V F]
    (hf : Function.Injective (algebraMap V F)) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (bar : O → O) (w0 : O) (hw : w0 + bar w0 = 1) {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (h : PS F n d) (k : ℕ)
    (hk : ∀ (m : ℕ) (u : PS F n d), (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e (h * u) = 0) →
      ∀ e : Fin n × Fin d →₀ ℕ, e.degree + k ≤ m → MvPowerSeries.coeff e u = 0)
    (m : ℕ) (hm : k + 2 ≤ m) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (h1 : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (B.G.F j),
        fun j => X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2)
        (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hs : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) = U)
    (hb : ∀ a, jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act (bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hrel : psJet m h * ∏ i : Fin n,
      (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m)
        (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d =>
          (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (B.A.act w0 j)] :
            Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q =
      psJet m h) : U = 1 := by
  set f := algebraMap V F with hfd
  let BF : FB F d O := FBMap.mapFB f B
  let UF : (Jet F (Fin 2 × Fin d) m)ˣ := Units.map (jetCoef f (Fin 2 × Fin d) m).toMonoidHom U
  have hUF : (UF : Jet F (Fin 2 × Fin d) m) = jetCoef f (Fin 2 × Fin d) m U := rfl
  have hX : ∀ {r : ℕ} (i : Fin r) (j : Fin d),
      MvPolynomial.map f (X (i, j) : MvPolynomial (Fin r × Fin d) V) = X (i, j) := fun i j => map_X _ _
  obtain ⟨c, hcs, hcb, hc⟩ := CIndFrExp3.fixExp BF.G BF.A.act BF.A.const bar m UF
    (by
      have e := congrArg (jetCoef f (Fin 3 × Fin d) m) h1
      rw [map_mul, jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 2),
        jetCoef_subst2 f _ _ _ _ (hX 0) (hX 2), jetCoef_subst2 f _ _ _ _ (hX 1) (hX 2)] at e
      exact e)
    (by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) hs
      rw [jetCoef_subst2 f _ _ _ _ (hX 1) (hX 0)] at e
      exact e)
    (fun a => by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) (hb a)
      rw [jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 1),
        jetCoef_subst2 f _ _ _ _ (hX 0) (fun j => map_psIn f _ _)] at e
      exact e)
  have hc0 : c = 0 := by
    refine GlobalTheory.DiagExpZero.form_eq_zero_of_diag_exp F d BF.G (BF.A.act w0) (BF.A.act (bar w0)) (BF.A.const w0) ?_ c hcs (hcb w0) n q hn hq ?_
    · have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add F B w0 (bar w0)
      rw [hw, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one] at e
      exact e.symm
    · intro e he
      refine hk m _ (fun e' he' => ?_) e (by omega)
      rw [jetCoef_subst2 f _ _ (fun j => X ((0 : Fin 1), j)) (fun j => psIn d m ![0] (BF.A.act w0 j)) (hX 0)
        (fun j => map_psIn f _ _), ← hUF, hc] at hrel
      simp only [jetCopy_graph m _ _ (BF.A.const w0)] at hrel
      simp only [← psJet_pow] at hrel
      rw [← psJet_prod, ← FBIdJet.psJet_mul] at hrel
      rw [mul_sub, mul_one, map_sub, coeff_eq_of_psJet_eq hrel e' he', sub_self]
  rw [hc0, CIndFrFix2c.twist_zero, FBIdJet.psJet_one, hUF] at hc
  exact Units.ext (jetCoef_injective f hf (by rw [hc, Units.val_one, map_one]))

end GlobalTheory.FrameEventually

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


end GlobalTheory
end
end
