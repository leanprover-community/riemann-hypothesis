import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqOneOfMultilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermBoxProductEqProdGerms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpBijFOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic

section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof pt)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.FieldBaseChange
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGermExist

theorem exists_linear_extension {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra R K]
    [IsFractionRing R K] [Algebra K F] {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module F P] (ρ : M →ₛₗ[algebraMap R K] N) (hρ : Function.Injective ρ)
    (a : N →ₛₗ[algebraMap K F] P) (ha : IsExtension a) {κ : Type} (g : M →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : P →ₗ[F] MvPowerSeries κ F, ∀ x, Λ (a (ρ x)) =
      MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x) := by
  classical
  let T₁ := Finsupp.linearCombination F fun x : M => a (ρ x)
  let T₂ := Finsupp.linearCombination F fun x : M =>
    MvPowerSeries.map ((algebraMap K F).comp (algebraMap R K)) (g x)
  have hk : LinearMap.ker T₁ ≤ LinearMap.ker T₂ := fun c hc => by
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    ext mo
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) c.support (fun x => ℓ (c x))
    choose! m hm using hr
    have h₁ : ∑ x ∈ c.support, m x • x = 0 := hρ (by
      have := congrArg (fun z => (algebraMap R K r) • Λ z) hc
      simp only [map_sum, map_zero, smul_zero, Finset.smul_sum] at this
      rw [map_zero, ← this, map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hΛ, map_smulₛₗ, hm x hx, smul_smul, Algebra.smul_def])
    have h₂ := congrArg (fun z => algebraMap R K (MvPowerSeries.coeff mo (g z))) h₁
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, map_mul] at h₂
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
    refine mul_left_cancel₀ hr0 ?_
    rw [mul_zero, ← h₂, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hm x hx, map_smul, MvPowerSeries.coeff_map, smul_eq_mul, RingHom.comp_apply, mul_comm (c x),
      ← Algebra.smul_def (A := F), map_smul, Algebra.smul_def (r : R) (ℓ (c x)), smul_eq_mul]
    ring
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend
    ((LinearMap.ker T₁).liftQ T₂ hk ∘ₗ T₁.quotKerEquivRange.symm.toLinearMap)
  refine ⟨Λ, fun x => ?_⟩
  have e := LinearMap.congr_fun hΛ ⟨T₁ (Finsupp.single x 1), LinearMap.mem_range_self _ _⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at e
  simpa only [T₁, T₂, Finsupp.linearCombination_single, one_smul] using e

theorem exists_serHom (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt) (hex : JetSer.SerExSt)
    {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)}
    (hx : Chart.IsUnivChart G d x) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) :
    ∃ τ : FnOver G.hom U →ₐ[R] PS R 1 d, ∀ f g, JetSer.IsSer1 x U f g ↔ g = τ f := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  have hc := (h3 _ y hy).1
  have e : ∀ r : PS R 1 d, ev (n := 1) ![pt R (n := 1) d 0] r = r := fun r => by
    have : (![pt R d 0] : Fin 1 → Germ.Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  have hs : ∀ f g, JetSer.IsSer1 x U f g → JetSer.HasSer (fun m => (y m).left) U f g := fun f g h => by
    have := h 1 _ y hy
    rwa [e] at this
  have ex := (hex R G d x hx).1 U hU
  have hm : ∀ m, ⊤ ≤ (y m).left ⁻¹ᵁ U := fun m => (hs _ _ (ex 0).exists.choose_spec m).1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hm 0)
  refine ⟨⟨τ, fun c => Eq.symm ((hτ _ _).1 fun m => ⟨hm m, ?_⟩)⟩, fun f g => ⟨fun h => (hτ f g).1 (hs f g h), ?_⟩⟩
  · obtain ⟨t, ht, -⟩ := (halg R (Fin 1 × Fin d)).1 m
    rw [← ht, AlgHom.commutes]
    have h₁ := (JetSer.fnVal_comp (y m).left G.hom U ⊤ le_top (hm m)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)).2
    refine Eq.trans (Eq.symm h₁) ?_
    rw [Over.w (y m)]
    have h₂ := JetSer.fnVal_specMap (algebraMap R (Chart.JetR R (Fin 1 × Fin d) m)) (𝟙 _) ⊤ le_top
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
    rw [Category.comp_id] at h₂
    refine h₂.trans (congrArg _ ?_)
    rw [JetSer.fnVal_eq_fnValHom _ _ le_top]
    simp [JetSer.fnValHom, Scheme.Hom.appLE]
  · rintro rfl
    obtain ⟨g, hg⟩ := (ex f).exists
    exact (hτ f g).1 (hs f g hg) ▸ hg

section Group

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem genericSec_injective (k : ℕ) : Function.Injective (genericSec U k) := by
  have := U.smooth
  intro a b h
  refine SecOver.ext _ _ fun j => ExpInt.generic_app_injective G _ (fn_ext fun y hy => ?_)
  have hy' := (wchart_eq (L := U.LG.L) (φ := fun _ : Fin 1 => 𝟙 G.left) (p := pullback.fst G.hom (jK R))
    (φ' := fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) j).ge hy
  have e := congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
    (fun _ => (k : ℤ))) => gs (𝟙 _) y _ (s.f j)) h
  exact (gs_res (𝟙 _) y _ hy' _).symm.trans (e.trans (gs_res (𝟙 _) y _ hy' _))

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_sum {k n : ℕ} (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α, D.toPre.SecB k α)
    {s : Fam D.toPre F k} (h₁ : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (h₂ : ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
      (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) :
    U.ExpandsG F k (∑ i, c i • extendSec U F k (genericSec U k (σ i)) : GroupSec U F k) s :=
  ⟨n, c, σ, f, h₁, (secLin_iff U.LG.isLB _ σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl, h₂⟩

theorem exists_linear_section (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    ∃ e : Fam D.toPre F k →ₗ[F] GroupSec U F k, ∀ v s, U.ExpandsG F k v s ↔ v = e s := by
  obtain ⟨-, h₂⟩ := expandsG_bijective U F hG hk h
  choose f hf using fun s => (h₂ s).exists
  have iff : ∀ v s, U.ExpandsG F k v s ↔ v = f s := fun v s =>
    ⟨fun h => (h₂ s).unique h (hf s), fun h => h ▸ hf s⟩
  have lin : ∀ (c : F) s s', f (c • s + s') = c • f s + f s' := fun c s s' =>
    ((iff _ _).1 (expandsG_lin U F k c (hf s) (hf s'))).symm
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  exact ⟨{ toFun := f
           map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
           map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }, iff⟩

theorem exists_linear_series {k : ℕ} {κ : Type} (g : IntSec U k →ₗ[R] MvPowerSeries κ R) :
    ∃ Λ : GroupSec U F k →ₗ[F] MvPowerSeries κ F, ∀ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k),
      Λ (∑ i, c i • extendSec U F k (genericSec U k (σ i))) = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i)) := by
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  obtain ⟨Λ, hΛ⟩ := exists_linear_extension (genericSec U k) (genericSec_injective U k)
    (extendSec U F k) (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) g
  refine ⟨Λ, fun n c σ => ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΛ, MvPowerSeries.smul_eq_C_mul]

theorem exists_linear_germ (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) {κ : Type}
    (g : IntSec U k →ₗ[R] MvPowerSeries κ R) : ∃ gm : Fam D.toPre F k →ₗ[F] MvPowerSeries κ F,
    ∀ s f, (∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (fi : Fin n → ∀ α, D.toPre.SecB k α),
      (∀ i e, U.ExpandsAt e k (σ i) (fi i)) ∧
      (∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => fi i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))) ∧
      f = ∑ i, MvPowerSeries.C (c i) *
        MvPowerSeries.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) (g (σ i))) ↔
      f = gm s := by
  obtain ⟨e, he⟩ := exists_linear_section U F hG hk h
  obtain ⟨Λ, hΛ⟩ := exists_linear_series U F g
  refine ⟨Λ ∘ₗ e, fun s f => ⟨?_, ?_⟩⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, rfl⟩
    rw [LinearMap.comp_apply, ← (he _ s).1 (expandsG_sum U F c σ fi h₁ h₂), hΛ]
  · rintro rfl
    obtain ⟨n, c, σ, fi, h₁, -, h₂⟩ := (he _ s).2 rfl
    exact ⟨n, c, σ, fi, h₁, h₂,
      (congrArg Λ ((he _ s).1 (expandsG_sum U F c σ fi h₁ h₂)).symm).trans (hΛ n c σ)⟩

theorem exists_linear_quotient (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) (hser : JetSer.SerSt)
    (hex : JetSer.SerExSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) {j : U.LG.L.ι}
    (hj : ⊤ ≤ η[G].left ⁻¹ᵁ U.LG.L.U j) (k : ℕ) {r : PS R 1 d} (hr : IsUnit r) :
    ∃ g : IntSec U k →ₗ[R] PS R 1 d, ∀ (σ : IntSec U k) f,
      (∃ S, JetSer.IsSer1 x _ (LB.Sec.f σ (fun _ => j)) S ∧ f * r = S) ↔ f = g σ := by
  obtain ⟨τ, hτ⟩ := exists_serHom halg hrep hser hex hx
    (U := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j))
    (GermExist.top_le_preimage_wchart _ _ j _ (fun _ => by rw [Category.comp_id]; exact hj))
  obtain ⟨u, rfl⟩ := hr
  refine ⟨LinearMap.mulRight R (u⁻¹).val ∘ₗ τ.toLinearMap ∘ₗ chartLin G.hom
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))) (fun _ => j), fun σ f => ⟨?_, ?_⟩⟩
  · rintro ⟨S, hS, e⟩
    exact (Units.eq_mul_inv_iff_mul_eq u).2 (e.trans ((hτ _ _).1 hS))
  · intro e
    exact ⟨_, (hτ _ _).2 rfl, (Units.eq_mul_inv_iff_mul_eq u).1 e⟩

end Group

theorem germ_exists_unique_linear : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt →
    JetSer.SerSt → JetSer.SerExSt → FamGerm.GermExSt := by
  intro hL _ _ halg hrep hser hex E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq
  let _ := H.starRing
  have := y.t.act.hom H.w0
  obtain ⟨r, hr, ur⟩ := (hex V y.t.G y.d y.x y.hx).1
    (LB.wchart y.P.U.LG.L (JetSer.primφ (y.t.act.act H.w0)) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun k => by
      rw [GermExist.unit_comp_primφ _ (IsMonHom.one_hom _) k]; exact y.hj)) (y.ρ.s (fun _ => y.j)).val
  obtain ⟨g, hg⟩ := exists_linear_quotient y.P.U.toUnifPre halg hrep hser hex y.hx y.hj q
    ((GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hr).pow q)
  obtain ⟨gm, h⟩ := exists_linear_germ y.P.U.toUnifPre F hL.globalFns hq (y.P.U.expand q hq) g
  refine ⟨gm, fun s f => Iff.trans ⟨?_, ?_⟩ (h s f)⟩
  · rintro ⟨n, c, σ, fi, g', r', h₁, h₂, hr', h₃, e⟩
    obtain rfl := ur r' hr'
    obtain rfl : g' = fun i => g (σ i) := funext fun i => (hg _ _).1 (h₃ i)
    exact ⟨n, c, σ, fi, h₁, h₂, e⟩
  · rintro ⟨n, c, σ, fi, h₁, h₂, e⟩
    exact ⟨n, c, σ, fi, fun i => g (σ i), r, h₁, h₂, hr, fun i => (hg _ _).2 rfl, e⟩

end GlobalTheory.FamGermExist
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermValuation

theorem constantCoeff_of_isSer1 (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x)
    {U : G.left.Opens} (e : Spec (CommRingCat.of R) ⟶ G.left) (he : e = η[G].left) (hU : ⊤ ≤ e ⁻¹ᵁ U) {f : Γ(G.left, U)} {g : PS R 1 d}
    (h : JetSer.IsSer1 x U f g) : MvPowerSeries.constantCoeff g = JetSer.fnVal e U f := by
  have hr := (hrep R G d x hx (Fin 1 × Fin d)).2.2.2.1
  have hs := (h 1 _ _ hr 0).2
  have e₁ : (1 : Chart.sp (R₀ := R) (Chart.JetR R (Fin 1 × Fin d) 0) ⟶ G).left =
      Spec.map (CommRingCat.ofHom (algebraMap R (Chart.JetR R (Fin 1 × Fin d) 0))) ≫ e := by
    rw [he, Hom.one_def, Over.comp_left]
    congr 1
  beta_reduce at hs
  rw [e₁, JetSer.fnVal_specMap _ _ _ hU] at hs
  have e₂ := congrArg (Chart.jetAug R (Fin 1 × Fin d) 0) hs
  rw [AlgHom.commutes, ((halg R (Fin 1 × Fin d)).2.1 0 _).2] at e₂
  have e₃ : ev (n := 1) ![(0 : Fin d → PS R 1 d)] g = MvPowerSeries.C (MvPowerSeries.constantCoeff g) := by
    have := MvPowerSeries.subst_zero_eq_C_constantCoeff (τ := Fin 1 × Fin d) (S := R) (f := g)
    refine Eq.trans ?_ this
    unfold ev
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    fin_cases a
    rfl
  rw [e₃, MvPowerSeries.constantCoeff_C] at e₂
  exact e₂.symm

section Generic

variable {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sval_of_secLin {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Fin n → Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  simp only [sval_of (s _) (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs r z _) e).trans ?_)
  refine ((gs_eq _ z _ hm _).trans (by rw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
    (gs_eq _ z _ hm _).symm.trans ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _)
      ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)))))

end Generic

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem sectionValue_of_valueAtZero_stalk {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {x : F} (h : Val0 D F k α s x)
    (z : (TF (R := V) F).left) {J} (hJ : Good D.toPre.P.L z J) :
    sval s (DegPre.zF D.toPre F).left z J = cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z x *
      (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val := by
  obtain ⟨τ, -, hc, he⟩ := h
  have T := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pow, Category.id_comp,
    val_of τ (𝟙 _) z J (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))
      (fun i => by rw [Category.id_comp])] at T
  rw [← T]
  have hy' := hJ.mem (DegPre.famφ D.toPre F α) (DegPre.zF D.toPre F).left
  have hy : z ∈ LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)
      (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)) :=
    Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy' i
  have e := congrArg (gs (𝟙 _) z _) (he (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)))
  have l := (gs_res (𝟙 _) z _ hy _).symm.trans e
  refine Eq.trans ?_ (l.trans ((gs_mul (𝟙 _) z _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z le_top hy _)
    (gs_unit (𝟙 _) z _ hy _))))
  refine Eq.trans ?_ (gs_pull (𝟙 _) (DegPre.zF D.toPre F).left z _ hy' _).symm
  rw [Category.id_comp]
  rfl

theorem valueAtZero_linearCombination_integral_sections {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {l : ℕ} {c : Fin l → F}
    {g : Fin l → D.toPre.SecB k α}
    (hs : GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s (D.toPre.famφB α) (DegPre.famε k) g
      (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)))
    (a : Fin l → V)
    (ha : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g i) (r ≫ eSec D.toPre.P.A) z J = cst r z (a i) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val)
    (z : (TF (R := V) F).left) {J} (hJ : Good D.toPre.P.L z J) :
    sval s (DegPre.zF D.toPre F).left z J =
      cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z (∑ i, c i * TWO.algVF (V := V) (F := F) (a i)) *
      (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val := by
  have hz : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left =
      (jFK (R := V) F ≫ jK V) ≫ eSec D.toPre.P.A := GC.zF_prB D.toPre F
  have hK : (toUnit (TK V)).left = jK V := GC.toUnit_TK_left
  rw [sval_of_secLin hs _ z hJ, ExpansionValueZero.cst_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ha i _ _ z J hJ, H1.cst_mul, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·)
    ((ExpansionValueZero.cst_comp _ _ z (a i)).trans (H1.gs_spec _ z _)) (congrArg Units.val (congrArg (· ^ k) ?_)))
  · refine (gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
    rw [GC.zF_fst]
    rfl
  · exact ((val_pull hJ D.toPre.rig (toUnit (TK V)).left (jFK (R := V) F)).trans (by rw [hK])).symm

theorem valueAtZero_unique_of_stalk_reading {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {x x' : F} (h : Val0 D F k α s x)
    (h' : ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J →
      sval s (DegPre.zF D.toPre F).left z J = cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z x' *
        (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val) : x = x' :=
  H1.cst_ext fun z => by
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart D.toPre.P.isLB (ψ z)
    exact (Units.mul_left_inj _).1 ((sectionValue_of_valueAtZero_stalk h z hJ).symm.trans (h' z J hJ))

end Value

theorem exists_unit_frame {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (Lr : RigLB G) (j : Lr.L.ι) (e : Spec (CommRingCat.of R) ⟶ G.left) (he : e = eSec G) (hj : ⊤ ≤ e ⁻¹ᵁ Lr.L.U j) :
    ∃ u : Rˣ, ∀ (q : ℕ) (σ : H0 Lr.L q) (x : R), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good Lr.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := Lr.L) Lr.rig r z J ^ q).val) →
      JetSer.fnVal e (LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)) (σ.f (fun _ => j)) = x * u.val ^ q := by
  subst he
  have h₁ : ⊤ ≤ (𝟙 (Spec (CommRingCat.of R))) ⁻¹ᵁ
      LB.wchart Lr.L (fun _ : PUnit.{1} => (eSec G : Spec (CommRingCat.of R) ⟶ G.left)) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have h₂ : ⊤ ≤ (eSec G : Spec (CommRingCat.of R) ⟶ G.left) ⁻¹ᵁ
      LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) := fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have hu : IsUnit (JetSer.fnVal (𝟙 (Spec (CommRingCat.of R))) _ (Lr.rig.s (fun _ => j)).val) :=
    (congrArg IsUnit (JetSer.fnVal_eq_fnValHom _ _ h₁ _)).mpr ((Units.isUnit _).map _)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun q σ x hx => H1.cst_ext fun z => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good Lr.L Lr.isLB z
    (fun _ : PUnit.{1} => (eSec G : Spec (CommRingCat.of R) ⟶ G.left)) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hj (show z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial))
  have eJ' : J (eSec G) = j := eJ PUnit.unit
  have H := hx _ (𝟙 _) z J hJ
  have hc : ∀ a : R, cst (𝟙 (Sp R)) z a = ((Spec (CommRingCat.of R)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := fun a => gs_eq _ z ⊤ trivial _
  have a₁ : sval σ (𝟙 (Sp R) ≫ eSec G) z J = cst (𝟙 (Sp R)) z
      (JetSer.fnVal (A := R) (eSec G) (LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)) (σ.f (fun _ => j))) := by
    rw [Category.id_comp, hc]
    exact (sval_of σ _ z J (fun _ => j) (fun _ => (congrArg J (Category.comp_id _)).trans eJ')).trans
      (JetSer.valSer_germ_fnVal _ _ h₂ z _).symm
  have a₂ : (val (L := Lr.L) Lr.rig (𝟙 (Sp R)) z J).val = cst (𝟙 (Sp R)) z u.val := by
    rw [hc, hu]
    refine Eq.trans ?_ (JetSer.valSer_germ_fnVal _ _ h₁ z _).symm
    exact (congrArg Units.val (val_of (L := Lr.L) Lr.rig _ z J (fun _ => j)
      (fun _ => (congrArg J (Category.id_comp _)).trans eJ'))).trans
      (gs_unit _ z _ (h₁ (show z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) _).symm
  refine a₁.symm.trans (H.trans ?_)
  rw [Units.val_pow_eq_pow_val, a₂, H1.cst_mul, hc u.val, hc (u.val ^ q), map_pow, map_pow]

theorem val_eq_of_approx {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {X : Type} {l : ℕ} (c : Fin l → F) (x : Fin l → V) (a : Fin l → X → V)
    (h : ∀ i (e : ℕ), ∃ S : Finset X, ∀ T : Finset X, S ⊆ T → x i - ∑ α ∈ T, a i α ∈ maximalIdeal V ^ (e + 1))
    (χ : X) (r r' : ℚ) (hr : r < r') (hχ : v (∑ i, c i * TWO.algVF (V := V) (F := F) (a i χ)) = (r : ℚ))
    (ho : ∀ β, β ≠ χ → ((r' : ℚ) : WithTop ℚ) ≤ v (∑ i, c i * TWO.algVF (V := V) (F := F) (a i β))) :
    v (∑ i, c i * TWO.algVF (V := V) (F := F) (x i)) = (r : ℚ) := by
  classical
  have hb : ∀ i, ∃ n : ℕ, ((r : ℚ) : WithTop ℚ) < v (c i) + (((n : ℕ) : ℚ) : WithTop ℚ) := fun i => by
    induction v (c i) using WithTop.recTopCoe with
    | top => exact ⟨0, by simp⟩
    | coe t =>
      obtain ⟨n, hn⟩ := exists_nat_gt (r - t)
      exact ⟨n, by rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith⟩
  choose n hn using hb
  choose S hS using fun i => h i (n i)
  let T : Finset X := insert χ (Finset.univ.biUnion S)
  have hT : ∀ i, S i ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)).trans (Finset.subset_insert _ _)
  have e : ∑ i, c i * TWO.algVF (V := V) (F := F) (x i) = ∑ i, c i * TWO.algVF (V := V) (F := F) (a i χ) +
      (∑ β ∈ T.erase χ, ∑ i, c i * TWO.algVF (V := V) (F := F) (a i β) +
        ∑ i, c i * TWO.algVF (V := V) (F := F) (x i - ∑ α ∈ T, a i α)) := by
    rw [← _root_.add_assoc, Finset.add_sum_erase T (fun β => ∑ i, c i * TWO.algVF (V := V) (F := F) (a i β))
      (Finset.mem_insert_self _ _), Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, ← map_sum, map_sub]
    ring
  rw [e, AddValuation.map_add_eq_of_lt_left, hχ]
  rw [hχ]
  refine v.map_lt_add (v.map_lt_sum WithTop.coe_ne_top fun β hβ => ?_) (v.map_lt_sum WithTop.coe_ne_top fun i _ => ?_)
  · exact (WithTop.coe_lt_coe.2 hr).trans_le (ho β (Finset.ne_of_mem_erase hβ))
  · rw [AddValuation.map_mul]
    refine (hn i).trans_le (add_le_add le_rfl ?_)
    exact ExpansionValueZero.le_val_of_mem_pow hϖ hv (n i) (Ideal.pow_le_pow_right (Nat.le_succ _) (hS i T (hT i)))

theorem main : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt →
    FamGerm.GermExSt → GermValSt := by
  intro hL _ _ halg hrep hser hex hG E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq s f hf
  have hU : ⊤ ≤ η[y.t.G].left ⁻¹ᵁ LB.wchart y.P.U.LG.L (fun _ : Fin 1 => 𝟙 y.t.G.left) (fun _ => y.j) :=
    fun z hz => Set.mem_iInter.2 fun _ => y.hj hz
  obtain ⟨l, c, σ, fi, g, ρ, hE, hlin, hρ, hg, hfe⟩ := id hf
  have hρu : IsUnit ρ := GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hρ
  refine ⟨fun r hr mo => ?_, fun χ x r r' hx hvx hr ho => ?_⟩
  · obtain ⟨gm, hgm⟩ := hG E H V F y q hq
    obtain ⟨l', c', σ', fi', hc', hE', hlin'⟩ := exists_integral_expansions_of_vge hL V y.ϖ y.hϖ y.P.D _ y.t.G y.P.U
      y.Q y.hQ F y.v y.hv q hq s r hr
    choose S hS using fun i => ((hex V y.t.G y.d y.x y.hx).1 _ hU ((σ' i).f (fun _ => y.j))).exists
    obtain ⟨w, hw⟩ := hρu.pow q
    have hf' : y.Germ q s (∑ i, MvPowerSeries.C (c' i) *
        MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (S i * (w⁻¹).val)) :=
      ⟨l', c', σ', fi', fun i => S i * (w⁻¹).val, ρ, hE', hlin', hρ,
        fun i => ⟨S i, hS i, by rw [← hw, Units.inv_mul_cancel_right]⟩, rfl⟩
    rw [(hgm s f).1 hf, ← (hgm s _).1 hf', map_sum]
    refine y.v.map_le_sum fun i _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, AddValuation.map_mul]
    exact (hc' i).trans (le_add_of_nonneg_right (GC.v_alg_nonneg y.hϖ y.hv _))
  · choose a ha using fun i α => ExpansionValueZero.exists_value y.P.D.toPre q α (fi i α)
    choose x₀ hx₀ using fun i => ExpansionValueZero.exists_coeff (A := V) y.P.U.LG.isLB (σ i) (eSec y.t.G)
      (GeneratorPullback.powGen y.P.U.LG.L _ _ y.P.U.LG.rig q) (powGen_isGen _ _ _ _ y.P.U.LG.rigGen q) (fun W _ f => by simp)
    have hx₁ : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (J), Good y.P.U.LG.L z J →
        sval (σ i) (r ≫ eSec y.t.G) z J = cst r z (x₀ i) * (val (L := y.P.U.LG.L) y.P.U.LG.rig r z J ^ q).val :=
      fun i Z r z J hJ => (hx₀ i Z r z J hJ).trans (by rw [val_pow])
    obtain ⟨u, hu⟩ := exists_unit_frame y.P.U.LG y.j _ rfl y.hj
    obtain ⟨w, hw⟩ := hρu.map (MvPowerSeries.constantCoeff (R := V))
    have hgi : ∀ i, MvPowerSeries.constantCoeff (g i) = x₀ i * ((u * w⁻¹) ^ q).val := fun i => by
      obtain ⟨S, hS, hgS⟩ := hg i
      have e₁ := (constantCoeff_of_isSer1 halg hrep y.hx _ rfl hU hS).trans (hu q (σ i) (x₀ i) (hx₁ i))
      rw [← hgS, map_mul, map_pow, ← hw, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at e₁
      rw [mul_pow, Units.val_mul, ← _root_.mul_assoc, ← e₁, inv_pow, Units.mul_inv_cancel_right]
    have hv0 := fun α => valueAtZero_linearCombination_integral_sections (hlin α) (fun i => a i α) (fun i => ha i α)
    have key := val_eq_of_approx y.hϖ y.hv c x₀ a
      (fun i e => ExpansionValueZero.value_sub_sum_mem y.P.U.toUnifPre e q (σ i) (fi i) (hE i e) (x₀ i) (hx₁ i)
        (a i) (ha i)) χ r r' hr ((congrArg y.v (valueAtZero_unique_of_stalk_reading hx (hv0 χ))).symm.trans hvx)
      (fun β hβ => GC.valuation_ge_at_zero y.hϖ y.hv (ho β hβ) (PhiValue.valueAtZero_of_sectionValue _ F q β _ _ (hv0 β)))
    have e : MvPowerSeries.constantCoeff f = (∑ i, c i * TWO.algVF (V := V) (F := F) (x₀ i)) *
        TWO.algVF (V := V) (F := F) ((u * w⁻¹) ^ q).val := by
      rw [hfe, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hgi, map_mul, _root_.mul_assoc]
    rw [e, AddValuation.map_mul, key]
    exact (congrArg _ (GC.v_alg_unit y.hv _)).trans (add_zero _)

end GlobalTheory.GermValuation
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.DepthBound
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthFromChars

theorem depth_bound_of_chars : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  intro hL _ hL4 hTB hC p hp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y hcomp hpu Dw I r bs Cc M₀ hred a k
    haa hcop hpk T _ _ rk τ e he isV _ hV hU ⟨lam, hlam⟩ ⟨ε, hε⟩ n S col m hcol hS D hD hDp hk hM h hh ep hep
  have hTW : TwistBCSpanStatement := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hL.globalFns hTB
  obtain ⟨jA, jR, -, -, -, -, -, jS, jX, -, -, -, -, jB⟩ := GlobalTheory.JetRoad.jetRoad
  have hG : FamGerm.GermExSt := GlobalTheory.FamGermExist.germ_exists_unique_linear hL hL4 hTW jA jR jS jX
  have hGV : GermValSt := GlobalTheory.GermValuation.main hL hL4 hTW jA jR jS jX hG
  have hJ : JetsSt := GlobalTheory.GermJets.jets hL hL4 hTW jA jR jS jX hG
  have hP : PullGermSt := GlobalTheory.PullGerm.germ_pullback hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt hG
  have hE : EigGermSt := GlobalTheory.T.derivative_congruence_germ_integral_translate hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt jB hG
  classical
  let _ := H.starRing
  have hp' : p.Prime := hp.out
  have hp2 : 2 ≤ p := hp'.two_le
  have hpF : ((p : TWO.Ov y.v) : F) = p := map_natCast (TWO.Ov y.v).subtype p
  have hep0 : 0 < ep := by
    by_contra hle
    refine hpu (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 (mem_span_of_val_le y.v _ 1 ?_ ?_)))
    · rw [hpF]; exact_mod_cast hp'.ne_zero
    · rw [hpF, hep, OneMemClass.coe_one, y.v.map_one]
      exact_mod_cast not_lt.1 hle
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp2
    linarith
  set θ : ℚ := ep / ((p : ℚ) - 1) with hθ
  have hθ0 : 0 < θ := div_pos hep0 hp1
  obtain ⟨c, hc⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv hθ0.le
  obtain ⟨ω, hω1, hω⟩ := FramePull.exists_integral_frame_pullback V y.d (𝓞 E) F y.B h hh H.w0 a p haa

  let m₁ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then m t s else 0
  let m₂ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then 0 else m t s
  have hm : m = fun t s => m₁ t s + m₂ t s := by
    funext t s
    by_cases ht : isV t <;> simp [m₁, m₂, ht]
  have hm₁ : ∀ t, ¬ isV t → ∀ s, m₁ t s = 0 := fun t ht s => if_neg ht
  have hm₂ : ∀ t, ¬ ¬ isV t → ∀ s, m₂ t s = 0 := fun t ht s => if_pos (not_not.1 ht)
  have hDD : ∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) + ∑ t, ∑ s : Fin (rk t), m₂ t s * (s.val + 1) = D := by
    rw [hD, hm]
    simp only [add_mul, Finset.sum_add_distrib]

  obtain ⟨y₁, hy₁, hy₂⟩ := hC p E H V F y hcomp hpu a haa hcop {t // isV t} (fun t => rk t.1) (fun t => τ t.1)
    (fun l => e ⟨l.1.1, l.2⟩) (fun c l => he c ⟨l.1.1, l.2⟩) (fun t => hV t.1 t.2)
    (fun t => ⟨fun i => lam ⟨t.1, i⟩, fun i i' => by simpa using hlam ⟨t.1, i⟩ ⟨t.1, i'⟩⟩)
    ⟨fun t => ε t.1, fun t t' => by simpa only [Subtype.ext_iff] using hε t.1 t'.1⟩
    ⟨c, by rw [TWO.mem_Ov, hc]; exact_mod_cast hθ0.le⟩
    (by
      change (p - 1) • y.v c = _
      rw [hc, hep, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one, hθ,
        mul_div_cancel₀ _ hp1.ne'])
    n (fun t => col t.1) (fun t => hcol t.1)
  let yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v := fun x =>
    if hx : isV x.1.1 then y₁ (⟨⟨x.1.1, hx⟩, x.1.2⟩, x.2) else 0
  choose s₁ s₁' t₁ c₁ f₁ r₁ h₁ hc₁ hr₁ hf₁ hf₁' using fun b => exists_eigen_column y hL hTW hVR hUU hG hGV hE Dw I r bs
    Cc M₀ hred a p k hp' (by omega) haa hcop hpk (Σ t : {t // isV t}, Fin (rk t.1)) (fun l => e ⟨l.1.1, l.2⟩)
    (fun l => y₁ (l, b)) (fun l => τ l.1.1 a) (fun l => hV _ l.1.2) (fun l => he a ⟨l.1.1, l.2⟩) (hy₁ b) h hh ω hω1 hω
  have hD₁ : ((∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) : ℕ) : ℚ) * θ ≤ D * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hθ0.le
  have hF₁ := val_eigen_columns y.v _ (fO_comp_eq y) y.B h hh H.w0 a p k hp'.ne_zero hpu hcop ω hω1 hω τ e he isV hV
    S col m₁ (fun t i ht => (hS t i).2 ht) hm₁ yy f₁ (fun b _ => hf₁ b)
    (fun b _ l hl mo => by
      simp only [yy, dif_pos hl]
      exact hf₁' b ⟨⟨l.1, hl⟩, l.2⟩ mo)
    θ ep hep
    (fun t ht s => by
      simp only [yy, dif_pos ht]
      refine (hy₂ ⟨t, ht⟩ s).trans (le_of_eq ?_)
      change (s.val + 1) • y.v c = _
      rw [hc, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_succ])
    (hD₁.trans_lt (by
      have : (D : ℚ) < (p : ℚ) - 1 := by
        have h1 : D + 1 < p := by omega
        have h2 : (D : ℚ) + 1 < p := by exact_mod_cast h1
        linarith
      calc (D : ℚ) * θ < ((p : ℚ) - 1) * θ := mul_lt_mul_of_pos_right this hθ0
        _ = ep := by rw [hθ, mul_div_cancel₀ _ hp1.ne']))

  obtain ⟨g, nb, hg, hnb, hF₂⟩ := val_unit_columns y.v y.B h hh H.w0 a p k hp' hpu ω hω τ e (he a) (fun t => ¬ isV t)
    hU lam hlam Sᶜ col m₂ hcol (fun t i ht => Finset.mem_compl.2 fun h' => ht ((hS t i).1 h')) hm₂ (by omega)
  have hnbD : ∑ b, nb b ≤ D := by omega
  have hnbD' : ∀ b, nb b ≤ D := fun b =>
    (Finset.single_le_sum (f := nb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans hnbD
  choose s₂ s₂' t₂ c₂ f₂ r₂ h₂ hc₂ hr₂ hf₂ using fun b => exists_jet_column y hL hG hJ hP r bs Cc M₀ hred a p k (nb b)
    (by omega) haa (by have := hnbD' b; omega)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hnbD' b) hred.2.1) hM) h hh ω hω (g b) (hg b)
  have hF₂' := hF₂ f₂ fun b _ => hf₂ b
  let f : Fin n → PS F 1 y.d := fun b =>
    if b ∈ S then MvPowerSeries.C (c₁ b) * (FB.toK F (f₁ b) * FB.toK F ω ^ k)
    else MvPowerSeries.C (c₂ b) * (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k)
  have hval : y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) ≤
      ((∑ b ∈ S, r₁ b + D * θ + ∑ b ∈ Sᶜ, r₂ b : ℚ) : WithTop ℚ) := by
    have e₁ := colValue_mul_of_disjoint_columns F _ n (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
      (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) S (minorsP F col m₁) (minorsP F col m₂)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₁ isV hm₁ hmo l b hb
        exact (hS _ i).2 hz)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₂ (fun t => ¬ isV t) hm₂ hmo l b hb
        exact fun h' => hz ((hS _ i).1 h'))
    rw [← minorMonomial_add, ← hm, sum_prod_const_mul S _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (FB.toK F (f₁ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₁
        (fun b hb mo => by simp only [f, if_pos hb]; exact nabVal_C_mul _ _ _ _ _ _ _ _),
      sum_prod_const_mul Sᶜ _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₂
        (fun b hb mo => by simp only [f, if_neg (Finset.mem_compl.1 hb)]; exact nabVal_C_mul _ _ _ _ _ _ _ _)] at e₁
    refine (congrArg y.v e₁).trans_le ?_
    rw [y.v.map_mul, y.v.map_mul, y.v.map_mul, hF₂', add_zero, WithTop.coe_add, WithTop.coe_add]
    exact add_le_add (add_le_add (val_prod_le y.v _ _ _ fun b _ => (hc₁ b).le)
      (hF₁.trans (WithTop.coe_le_coe.2 hD₁))) (val_prod_le y.v _ _ _ fun b _ => (hc₂ b).le)
  obtain ⟨gm, hgm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hval)
  refine ⟨fun b => if b ∈ S then s₁ b else s₂ b, fun b => if b ∈ S then s₁' b else s₂' b,
    fun b => if b ∈ S then t₁ b else t₂ b, f, gm, fun b => ?_, hgm.symm, ?_⟩
  · by_cases hb : b ∈ S
    · simp only [f, if_pos hb]; exact h₁ b
    · simp only [f, if_neg hb]; exact h₂ b
  · rw [← hgm, WithTop.coe_le_coe] at hval
    have h1 : (gm : ℝ) ≤ ∑ b ∈ S, (r₁ b : ℝ) + D * (ep / (p - 1)) + ∑ b ∈ Sᶜ, (r₂ b : ℝ) := by
      rw [hθ] at hval
      exact_mod_cast hval
    have h2 : ∑ b ∈ S, (r₁ b : ℝ) ≤ S.card * r * Cc / (4 * k) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun b _ => hr₁ b).trans (le_of_eq ?_)
      rw [nsmul_eq_mul]; ring
    have hCk : 0 ≤ Cc / k := div_nonneg hred.1 (Nat.cast_nonneg _)
    have h3 : ∑ b ∈ Sᶜ, (r₂ b : ℝ) ≤ (D : ℝ) ^ 2 * Cc / k := by
      have h4 : ∑ b ∈ Sᶜ, nb b ^ 2 ≤ D ^ 2 :=
        calc ∑ b ∈ Sᶜ, nb b ^ 2 ≤ ∑ b, nb b ^ 2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ ≤ ∑ b, nb b * D := Finset.sum_le_sum fun b _ => by
            rw [sq]; exact Nat.mul_le_mul_left _ (hnbD' b)
          _ ≤ D ^ 2 := by rw [← Finset.sum_mul, sq]; exact Nat.mul_le_mul_right _ hnbD
      refine (Finset.sum_le_sum fun b _ => hr₂ b).trans ?_
      simp only [mul_div_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h4) hCk
    rw [mul_div_assoc (D : ℝ) (ep : ℝ)]
    linarith

end GlobalTheory.DepthFromChars
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_bound_from_characters_pointDatum : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  atlas_forward_decl GlobalTheory.DepthFromChars.depth_bound_of_chars
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_boxProduct_eq_prod_germs : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  first | exact @GlobalTheory.PowGerm.boxGermSt_holds | exact GlobalTheory.PowGerm.boxGermSt_holds | (intros; apply GlobalTheory.PowGerm.boxGermSt_holds <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem boxTup_of_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ Q hQ F _ _ _ _ v g g' π hg hg' hπ τ hτ hEL n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    s s₂ t₀ t p w ζ x σ f h
  have hG := hL.globalFns
  have hk : 1 ≤ g' * g := Nat.mul_pos hg' hg
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F g'
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (g' * g)
  obtain ⟨p', hp'⟩ := BoxQk.exists_isBoxQk hG T.V n P.D.toPre D'.toPre pD F (g' * g) p
  have hw : ∀ i, (w i).IsGen := fun i => (h i).2.2.1
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (g' * g) p' p hp' w hw
  obtain ⟨σ', hσ', -⟩ := (expandsG_bijective_of_dvr hL hL2 hL4 hT T.V D' A' G' U' F (g' * g) hk).2 (bx t)
  let x' : TFK (R := T.V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ x)
  have hx' : ∀ i, x' ≫ pA.pr i = x i := fun i => pA.lim.fac (Fan.mk _ x) ⟨i⟩
  have hπ' : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm, hπ]
  refine ⟨bx₁ s, bx s₂, p', w', ∏ i, ζ i, x', bx t₀, bx t, σ', ⟨?_, ?_, ⟨hw', ?_, ?_⟩, ?_, ?_, ?_, ?_, hσ', ?_⟩, hx'⟩
  · have := NuBox.main T.V ϖ hϖ n P.D D' pD Q hQ F v g' s (bx₁ s) ((hbx₁ _ _).2 rfl) (fun _ => 0) (fun i => (h i).1)
    rw [Finset.sum_const_zero] at this
    exact this
  · exact BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact (star π) g g' hg hg' hπ' s s₂ _ _
      (fun i => (h i).2.1) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => (h i).2.2.2.1
  · exact finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (g' * g) hk p' p hp' w w' hw hw' hΦ ζ (fun i => (h i).2.2.2.2.1)
  · exact ProdTorsion.qkToAk_box hL T.V _ n P.D D' P.A A' C.I.G.G G' pD pA pG U' P.U PU
      (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ P.U) (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ U') F (g' * g) hk
      p' p hp' x' x hx' (fun i => (h i).2.2.2.2.2.1)
  · intro i
    rw [← Category.assoc, hx']
    exact (h i).2.2.2.2.2.2.1
  · exact hΦ s₂ t₀ _ _ (fun i => (h i).2.2.2.2.2.2.2.1) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl)
  · refine (isSmul_iff _ _ _).2 ?_
    rw [← MultilinearMap.map_smul_univ]
    exact congrArg bx (funext fun i => (isSmul_iff _ _ _).1 (h i).2.2.2.2.2.2.2.2.1)
  · exact GlobalTheory.T.germ_boxProduct_eq_prod_germs hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
      C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (g' * g) hk σ t f σ' (bx t)
      (fun i => (h i).2.2.2.2.2.2.2.2.2) ((hbx _ _).2 rfl) hσ'

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  atlas_forward_decl GlobalTheory.boxTup_of_columns
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_frames_local_series : LinkEpsSt := by
  first | exact @GlobalTheory.LinkEps.linkEps | exact GlobalTheory.LinkEps.linkEps | (intros; apply GlobalTheory.LinkEps.linkEps <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkSec

theorem comp_psum_two {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (s : T ⟶ T') (x₀ x₁ : T' ⟶ G)
    (I : Finset (Fin 2)) : s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![s ≫ x₀, s ≫ x₁] I).left := by
  have e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I := by
    fin_cases I
    · exact MonObj.comp_one _
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·)
        (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))
  exact congrArg CommaMorphism.left e

theorem psum_mem {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (w : G ⟶ G) (x : T ⟶ G)
    (I : Finset (Fin 2)) : ∃ k, (psum G ![x, x ≫ w] I).left = x.left ≫ JetSer.primφ w k := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have p₀ : psum G ![x, x ≫ w] ∅ = 1 := rfl
  have p₁ : psum G ![x, x ≫ w] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x ≫ w] {1} = x ≫ w := _root_.mul_one _
  have p₄ : psum G ![x, x ≫ w] {0, 1} = x * (x ≫ w) := congrArg (x * ·) (_root_.mul_one _)
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  · exact ⟨4, congrArg CommaMorphism.left (p₀.trans e₄.symm)⟩
  · exact ⟨0, (congrArg CommaMorphism.left p₁).trans (Category.comp_id _).symm⟩
  · exact ⟨3, congrArg CommaMorphism.left p₂⟩
  · exact ⟨1, congrArg CommaMorphism.left (p₄.trans e₁.symm)⟩

theorem change_index {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by
  have E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left := fun I => by
    rw [comp_psum_two, h₀, h₁]
  have hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left)
      (fun _ => j) := Set.mem_iInter.2 fun I => by
    obtain ⟨k, hk⟩ := psum_mem w x I.down
    have a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j := Set.mem_iInter.1 hj k
    rw [← hk, ← E] at a
    exact a
  have hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  let h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ := fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)
  refine ⟨hs, h x.left, ?_, ?_⟩
  · refine (sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_))
    show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _
    rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]
  · have a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) *
        gm x.left y _ (ρ.s fun _ => j) := gen_trans hρ x.left y (hJ.mem _ _) hj
    have b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)),
        h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) *
        gm s.left y _ (e.s fun _ => j) := gen_trans he s.left y (hJ.mem _ _) hs
    simp only [E] at b
    rw [a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

def germAt (A : Type) [CommRing A] (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Sp A).presheaf.germ ⊤ y trivial).hom.comp (toΓ A)

theorem gs_toΓ_eq {A : Type} [CommRing A] (y : Sp A) (a : A) : gs (𝟙 _) y ⊤ (toΓ A a) = germAt A y a :=
  gs_eq (𝟙 _) y ⊤ trivial _

theorem gs_spMap_germAt {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (Geo.Tor.spMap f) y ⊤ (toΓ A a) = germAt B y (f a) := by
  have e := gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp] at e
  refine e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))
  exact congrArg (gs (𝟙 _) y ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

variable {V : Type} [CommRing V]

theorem psJet_pow {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

theorem toJet_eq {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    JetSer.toJet m f = psJet m f := (congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)).symm

theorem ev_pt_one {d : ℕ} (f : PS V 1 d) : ev (n := 1) ![pt V (n := 1) d 0] f = f := by
  have : (![pt V d 0] : Fin 1 → Pt V 1 d) = fun j => pt V d j := by
    funext j; fin_cases j; rfl
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

theorem gs_of_isSer1 {G : Over (Sp V)} {d : ℕ} (xT : JetPts G (Fin 1 × Fin d)) (x : JetSer.Fam G (Fin d))
    (hM : Match (oneCol d) xT x) (U : G.left.Opens) (f : Γ(G.left, U)) (g : PS V 1 d) (h : JetSer.IsSer1 x U f g)
    (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) :
    (xT m).left y ∈ U ∧ gs (xT m).left y U f = germAt _ y (psJet m g) := by
  have R : JetSer.Rep x (pt V (n := 1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by
    refine ⟨fun j => by simp [pt], fun m => ?_⟩
    obtain ⟨e, he1, he2⟩ := hM m
    refine ⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩
    · exact (he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm
    · apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans he2
  obtain ⟨h1, h2⟩ := h 1 _ _ R m
  have e : (LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _
  have h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U := e ▸ h1
  have h2' : JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g :=
    (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans
      (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))
  refine ⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩
  rw [← h2']
  exact (JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm

def diagSub {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (φ j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2

theorem psIn_one {d : ℕ} (m : ℕ) (f : PS V 1 d) : psIn d m ![(0 : Fin 1)] f = psTrunc m f := by
  unfold psIn
  have : (fun p : Fin 1 × Fin d => ((![(0 : Fin 1)] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [this, MvPolynomial.rename_id_apply]

theorem diagSub_zero {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : (diagSub m φ).comp (jetCopy d m 0) = AlgHom.id V _ := by
  refine Chart.jet_ext (R := V) fun p => ?_
  obtain ⟨a, i⟩ := p
  obtain rfl : a = 0 := Subsingleton.elim _ _
  show diagSub m φ (jetCopy d m 0 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = Ideal.Quotient.mk _ (MvPolynomial.X _)
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord]
  simp

theorem diagSub_one {d : ℕ} (m : ℕ) (φ : Pt V 1 d) :
    (diagSub m φ).comp (jetCopy d m 1) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2) := by
  refine Chart.jet_ext (R := V) fun p => ?_
  show diagSub m φ (jetCopy d m 1 (Ideal.Quotient.mk _ (MvPolynomial.X _))) =
    jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) (Ideal.Quotient.mk _ (MvPolynomial.X _))
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord, jetSubstP, LinkLaw.jetMap_coord]
  simp [psIn_one]

theorem diagSub_psJet {d : ℕ} (m : ℕ) (φ : Pt V 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (ε : PS V 2 d) :
    diagSub m φ (psJet m ε) = psJet m (ev (n := 1) ![pt V (n := 1) d 0, comp1 φ (pt V (n := 1) d 0)] ε) := by
  have c : comp1 φ (pt V (n := 1) d 0) = φ := funext fun i => ev_pt_one _
  rw [c]
  have h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by
    rintro ⟨a, i⟩
    fin_cases a
    · simp [pt]
    · exact hφ i
  obtain ⟨Φ, hΦ, hsub⟩ := LinkLaw.exists_subst
    (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m
  have e : diagSub m φ = Φ := by
    refine Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm
    obtain ⟨a, i⟩ := p
    fin_cases a
    · refine Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm
      have := AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord] at this
      exact this
    · have := AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord,
        LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)] at this
      exact this
  rw [e, ← toJet_eq, ← toJet_eq]
  exact hsub ε

theorem homAt_comp' {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

theorem val_prim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (hp : Function.Surjective t.G.hom.appTop.hom) (wP : PrimTyG t) (hw : IsPrimG t wP)
    (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig)
    {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z) (J) (hJ : Good t.PP.L z J) : val wP r z J = val ρ r z J := by
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  refine gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ
  · have P := JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k
    simp only [Over.id_left, Category.id_comp] at P
    refine P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _))
      (by rw [Fintype.prod_unique]; exact zpow_one _)
      (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Over.id_left]
    abel
  · have a := val_corr hJ hw.2 (𝟙 _)
    have b := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

theorem linkSec : LinkSecSt := by
  intro E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ
  letI := H.starRing
  obtain ⟨hj, vr⟩ := gs_of_isSer1 xT x hM _ _ r hr m y
  obtain ⟨-, vS⟩ := gs_of_isSer1 xT x hM _ _ S hS m y
  let s := Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))
  have h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_zero]
    refine Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0 := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_one]
    exact (hC.act m H.w0).symm
  obtain ⟨hs, c, c₁, c₂⟩ := change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ
  obtain ⟨J₂, hJ₂, e₂⟩ := exists_good t.PP.L t.PP.isLB (s.left y)
    (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
    (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)
  have e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j :=
    fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)
  have v₂ := hε m (s.left y) J₂ hJ₂ e₂'
  have v₃ := (gs_unit (𝟙 _) (s.left y) _ hs _).trans
    ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)
  have vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε)) :=
    (gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans
      ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans
        ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))
  have vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r) :=
    (gs_unit (xT m).left y _ hj _).symm.trans vr
  have vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J =
      c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j)) := by
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))
      exact congrArg (fun p => val wPT p y J) (Category.id_comp _)
    · refine (val_pull hJ _ _ _).trans ?_
      exact congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)
  rw [vL, gs_toΓ_eq]
  refine c₁.trans ((congrArg (_ * ·) vS).trans ?_)
  rw [← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end GlobalTheory.LinkSec
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.truncation_frames_local_series E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFromPointDatum_of_laws : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := by
  atlas_forward_decl GlobalTheory.ChartLink.link
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Transfer

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer GlobalTheory.PowGerm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem dLin_id : dLin (pt R (n := 1) d 0) = 1 := by
  classical
  ext i j
  simp only [dLin, pt, coeff_X, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero e)).symm

theorem law_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.G.F = B'.G.F := funext fun i => ((Related.refl B).law i).trans (h.law i).symm

theorem act_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.A.act = B'.A.act := funext fun a => ((Related.refl B).act a).trans (h.act a).symm

theorem const_diagSer {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d} (h : Related B B' φ φi ε) (w0 : O) :
    constantCoeff (diagSer B' w0 ε) = 1 := by
  have h1 := congrArg constantCoeff h.ax1
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_one] at h1
  unfold diagSer
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0))), h1]

theorem exists_inv_pow {σ : Type} (s : MvPowerSeries σ R) (hs : constantCoeff s = 1) (q : ℕ) :
    ∃ un : MvPowerSeries σ R, constantCoeff un = 1 ∧ un * s ^ q = 1 := by
  have hu : IsUnit (s ^ q) := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hs ▸ isUnit_one)).pow q
  obtain ⟨un, hun⟩ := hu.exists_left_inv
  refine ⟨un, ?_, hun⟩
  have := congrArg constantCoeff hun
  rwa [map_mul, map_pow, hs, one_pow, mul_one, map_one] at this

theorem const_gauge {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d}
    (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h1 := congrArg constantCoeff hh.ax1
  rwa [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_zero] at h1

theorem exists_gauge {B B' : FB R d O} {ε : PS R 2 d} (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ : PS k 2 d) (hh : B.IsCanonGauge k h₀) :
    ∃ h' : PS k 2 d, B₂.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ m = f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B₂.nabVal k h' w0 m f' u P = B.nabVal k h₀ w0 m f u P := by
  obtain ⟨h', hh', hv⟩ := GlobalTheory.JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.2.2.2.1 R d O B B' _ _ ε hr k h₀ hh
  refine ⟨h', (hG h').1 hh', fun w0 m f f' hf Λ _ u P => ?_⟩
  have e : (fun i => FB.toK k (pt R (n := 1) d 0 i)) = pt k (n := 1) d 0 := by
    funext i
    simp [pt]
  have h1 := hv w0 m f f' (by rw [e, gt_ev_pt_self]; exact hf) Λ u P
  rw [dLin_id, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [Matrix.one_mulVec] at h1
  rw [← h1]
  unfold FB.nabVal FB.hL
  rw [hF, hA]

theorem eig_map {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) (a : O) (u : Fin d → R) (s : R)
    (h : (dAct R B a).mulVec u = s • u) :
    (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • fun i => algebraMap R k (u i) := by
  funext i
  have h1 := congrArg (algebraMap R k) (congrFun h i)
  simpa [Matrix.mulVec, dotProduct, dAct, FB.actK, coeff_map] using h1

theorem value_eq [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] {B B' : FB R d O} {ε : PS R 2 d}
    (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ h : PS k 2 d) (hh₀ : B.IsCanonGauge k h₀)
    (hh : B₂.IsCanonGauge k h) {T : Type} [Fintype T] (r : T → ℕ) (cc : T → T) (σ : T → O →+* k)
    (hcc : ∀ τ, cc (cc τ) = τ) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu : ∀ l a, (dAct k B₂ a).mulVec (u l) = σ l.1 a • u l) {n : ℕ}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : ∀ (τ : T) (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
        (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0)
    (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (hf : ∀ b, f' b * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ q = f b)
    {Ix : Type} [Fintype Ix] (e : (Σ τ : T, Fin (r τ)) × Fin n → Ix) (cp : Ix → Fin n) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu' : ∀ p, u' (e p) = u p.1) :
    Formalism.L2.Pj.nabValN B₂ k h w0 q (boxSer f') cp u' (MvPolynomial.rename e Q) =
      ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h₀ w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  obtain ⟨h', hh', hval⟩ := exists_gauge hr B₂ hF hA hG h₀ hh₀
  rw [nabValN_boxSer R' d O B₂ k h w0 (const_gauge hh) q n f' _ Ix e cp u u' hcp hu' Q,
    canonGauge_independence_harmonic R' d O k B₂ h h' hh hh' T r cc (fun _ => True) σ hcc (fun _ => Or.inl trivial)
      hσ hsep u hu n Q (fun τ _ => hQ τ) w0 q f']
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b _ => hval w0 q (f b) (f' b) (hf b) _ u (MvPolynomial.monomial (colM mo b) 1)]

end GlobalTheory.Transfer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

set_option maxHeartbeats 400000 in

theorem transfer_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  intro L1 L2 L4 TW E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hFr P tors ϖ hϖ Q hQ F _ _ _ _ _ _ v hv
  letI := io.toAlgebra
  haveI := T.cpl
  obtain ⟨BT, e1, e2, e3, e4, e5, e6, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hF, hA, hG, hcan⟩ := e7 F
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hrel, hgerm⟩ := GlobalTheory.T.chartFromPointDatum_of_laws L1 L2 L4 TW E H T.V T.cpl C.I.G P tors ϖ hϖ
    Q hQ F v hv (chD C.ch) BT C.tgT C.xT C.eT C.wPT (by rw [e1, e2]; exact C.chartT)
    (by rw [e1, e2, e3, e4, e5, e6]; exact C.frameT) C.primT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C) hFr τ hτ
    (by rw [e2]; exact hEL)
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, (Transfer.law_eq hrel).trans e1, (Transfer.act_eq hrel).trans e2, ?_⟩
  intro g g' π hg hg' hπ n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hon s s' t f hcol
  obtain ⟨un, hun1, hun⟩ := Transfer.exists_inv_pow _ (Transfer.const_diagSer hrel H.w0) (g' * g)
  have hf : ∀ b, (f b * MvPowerSeries.map (algebraMap T.V F) un) *
      MvPowerSeries.map (algebraMap T.V F) (diagSer BT H.w0 ε) ^ (g' * g) = f b := fun b => by
    rw [_root_.mul_assoc, ← map_pow, ← map_mul, hun, map_one, _root_.mul_one]
  choose σ hσ1 hσ2 using fun b => hgerm (g' * g) (t b) (f b) _ (hcol b).2.2.2 (hf b)
  choose p xx w ζ t₀ h1 h2 h3 h4 h5 h6 h7 using fun b => (hcol b).2.2.1
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', hbox, -⟩ := GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange L1 L2 L4 TW E H Dw l Xo c T io y C P ϖ hϖ Q hQ F v
    g g' π hg hg' hπ τ hτ hEL n D' A' G' pD pA pG U' PU oD' hxe hon s s' t₀ t p w ζ xx σ
    (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un)
    (fun b => ⟨(hcol b).1, (hcol b).2.1, h3 b, h4 b, h5 b, h1 b, h2 b, h6 b, h7 b, hσ1 b, hσ2 b⟩)
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', _, un, hbox, hun1, rfl, ?_⟩
  intro h₀ hh₀ rk hrk Pp hPp
  have huv : ∀ ℓ i, algebraMap T.Fr F (C.ch.uvec ℓ i) = algebraMap T.V F (C.uvecT ℓ i) := fun ℓ i => by
    rw [C.gen.1.2.2.2.2.2.2 ℓ i, ← IsScalarTower.algebraMap_apply]
  refine Transfer.value_eq hrel C.ch.B hF hA hG h₀ _ hh₀ hcan rk ComplexEmbedding.conjugate
    (fun τ => (algebraMap T.Fr F).comp (io.comp (embK c τ))) (fun τ => ComplexEmbedding.involutive_conjugate E τ) ?_ ?_
    (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) ?_ Pp hPp
    H.w0 (g' * g) f _ hf
    (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n))
    (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    (fun _ => rfl) (fun p => funext fun i => huv _ i)
  · intro τ a
    have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    exact congrArg (fun z => algebraMap T.Fr F (io z)) h
  · intro τ τ' hne
    obtain ⟨a, ha⟩ := EigDir.embK_sep c τ τ' hne
    refine ⟨a, ?_⟩
    simp only [RingHom.comp_apply]
    rw [← map_sub, ← map_sub]
    exact ((isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)).map io).map _
  · intro ℓ a
    have h := Transfer.eig_map (k := F) C.ch.B a _ _
      (eigDirSt E H Dw l Xo c T io y C a ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩)
    have e : (fun i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i)) =
        fun i => algebraMap T.V F (C.uvecT ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i) := funext fun i => huv _ i
    exact e ▸ h

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  atlas_forward_decl GlobalTheory.transfer_columns
end

section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem isAdicComplete_ov_of_range {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (O : Type) [CommRing O]
    [Algebra O F] (hinj : Function.Injective (algebraMap O F))
    (hr : ∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) (g : ℕ)
    (hc : IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O) :
    IsAdicComplete (Ideal.span {((g : ℕ) : TWO.Ov v)}) (TWO.Ov v) := by
  let φ : O →+* TWO.Ov v := (algebraMap O F).codRestrict (TWO.Ov v) fun a => (hr _).2 ⟨a, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨a, ha⟩ := (hr z).1 z.2
    exact ⟨a, Subtype.ext ha⟩
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {((g : ℕ) : O)}) (RingEquiv.ofBijective φ hφ)).2 hc
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

theorem isUnit_iff_not_isUnit_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {x y u u' : R}
    (h : ¬ IsUnit (x * y)) (h1 : u * x + u' * y = 1) : IsUnit x ↔ ¬ IsUnit y := by
  refine ⟨fun hx hy => h (hx.mul hy), fun hy => ?_⟩
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h2 | h2
  · exact isUnit_of_mul_isUnit_right h2
  · exact absurd (isUnit_of_mul_isUnit_right h2) hy

theorem card_filter_val_lt (n₁ n₂ : ℕ) :
    (Finset.univ.filter fun b : Fin (n₁ + n₂) => b.val < n₁).card = n₁ := by
  rw [Fin.card_filter_val_lt]; omega

theorem lemmaBT_of_characters : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → LemmaBT := by
  intro L1 L2 L4 TB hch E _ _ _ H Dw l Xo c inst hst
  obtain rfl := starSt E H inst hst
  letI := H.starRing
  intro T io y hy C hfr P tors ϖ hϖ Q hQ g g' hg hg' hne og og' π π' hπ hπ' hcop hcop' hcard hnd hnu F _ _ _ _ _ _ v hv
    O _ _ _ _ hinj hO hOc I Φ M0 r b hΦ hb1 hb2 n₁ n₂ hn D' A' G' _ _ pD pA pG U' PU _ oD' hx1 hx2 m hm hd1 hd2 hd3 ρg hρg
  letI := io.toAlgebra
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  obtain ⟨σ, e, hσ, he1, -, heig, hval, hconj, ⟨lam, hlam⟩, hε, hgu⟩ :=
    GlobalTheory.T.exists_integral_types_and_directions' E H Dw l Xo c T io y C ϖ hϖ g hg hnu hcard hnd F v hv
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, -, hact, htr⟩ :=
    GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues L1 L2 L4 TB E H Dw l Xo c T io y C hfr P tors ϖ hϖ Q hQ F v hv
  obtain ⟨BT, -, hBT, -, -, -, -, hBF⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  have hdA : ∀ a, dAct F B a = dAct F C.ch.B a := by
    intro a
    have h1 : B.actK F a = C.ch.B.actK F a := by
      rw [← (hBF F).2.1 a]
      unfold FB.actK
      rw [hact, hBT]
    unfold dAct
    rw [h1]
  obtain ⟨rk, hrk, col, m', hcol, hty, hdeg, hmin⟩ :=
    minorSt E H Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁ n₂ (by convert hm)
  obtain ⟨h₀, hh₀⟩ := canonGauge_exists T.V (chD C.ch) (𝓞 E) F B
  have hππ : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, mul_comm, hπ]
  obtain ⟨u₁, u₂, hu12⟩ := hcop
  have hg'0 : (0 : ℝ) < g' := by exact_mod_cast hg'.pos
  have hred : (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ :
      FamGerm.Pt1 E H T.V F).Red r b Φ (max M0 0) := by
    refine ⟨hΦ, le_max_right _ _, hb1, fun i z => ?_⟩
    have h1 := hb2 i z
    have h2 : (0 : ℝ) ≤ Q z := by
      by_cases hz : z = 0
      · rw [hz, Q_zero hϖ P.D hQ, Int.cast_zero]
      · have h3 := Q_pos hϖ P.D hQ hz
        exact_mod_cast (by omega : 0 ≤ Q z)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  obtain ⟨s, s', t, f, gm, hs, hgm, hle⟩ := GlobalTheory.T.depth_bound_from_characters_pointDatum L1 L2 L4 TB hch g E H T.V F
    (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ)
    (isAdicComplete_ov_of_range v O hinj hO g hOc) hgu Dw I r b Φ (max M0 0) hred (star π) g' hππ
    ⟨u₂, u₁, by rw [star_star, add_comm, hu12]⟩ ((Nat.coprime_primes hg hg').2 hne) (E →+* ℂ) rk σ
    (fun l => e ⟨l.1, Fin.castLE (hrk l.1) l.2⟩)
    (fun a l => by rw [show dAct F _ a = dAct F C.ch.B a from hdA a]; exact heig a _)
    (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))))
    (fun τ h => (hval τ _).1 (by rw [hσ]; exact h)) (fun τ h => (hval τ _).2 (by rw [hσ]; exact h))
    ⟨fun l => lam ⟨l.1, Fin.castLE (hrk l.1) l.2⟩, fun l l' => by
      refine (hlam _ _).trans (if_congr ?_ rfl rfl)
      obtain ⟨τ, i⟩ := l
      obtain ⟨τ', i'⟩ := l'
      constructor
      · intro h
        obtain rfl : τ = τ' := congrArg Sigma.fst h
        have h2 := eq_of_heq (Sigma.mk.inj h).2
        obtain rfl : i = i' := Fin.castLE_injective _ h2
        rfl
      · intro h
        rw [h]⟩
    (by convert hε) (n₁ + n₂) (Finset.univ.filter fun b => b.val < n₁) col m' hcol
    (fun τ i => by rw [Finset.mem_filter, ← hty τ i]; simp) (degOf Dw m) hdeg.symm hd1 hd2
    (by
      rcases le_total M0 0 with h | h
      · rw [max_eq_right h, mul_zero]; exact hg'0
      · rw [max_eq_left h]; exact hd3)
    h₀ hh₀ ρg hρg
  simp only [star_star] at hs
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, un, hbox, -, -, hvl⟩ :=
    htr g g' π hg.one_le hg'.one_le hπ (n₁ + n₂) D' A' G' pD pA pG U' PU oD' hx1 hx2 s s' t f hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbox
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, gm, b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_, ?_⟩
  · rw [hmin, hvl h₀ hh₀ rk hrk (FamGerm.minorsP F col m') ?_, ← hgm]
    · simp only [he1]
    · intro τ
      refine minors_disjoint_columns_harmonic F _ rk _ col m' _ rfl τ _ fun i i' hii => ?_
      have k1 := hty τ i
      have k2 := hty _ i'
      rw [hii, k2, ← hσ, ← hσ, hconj, star_star] at k1
      have k3 : ∀ a, 0 < v (σ τ a : F) ↔ ¬ IsUnit (σ τ a) := fun a =>
        ⟨fun h hu => hgu (isUnit_of_dvd_unit (Ideal.mem_span_singleton.1 ((hval τ a).1 h)) hu),
          fun h => by_contra fun h' => h ((hval τ a).2 h')⟩
      rw [k3, k3] at k1
      have k4 : IsUnit (σ τ π) ↔ ¬ IsUnit (σ τ (star π)) :=
        isUnit_iff_not_isUnit_of_coprime (u := σ τ u₁) (u' := σ τ u₂) (by rw [← map_mul, hπ, map_natCast]; exact hgu)
          (by rw [← map_mul, ← map_mul, ← map_add, hu12, map_one])
      tauto
  · rw [card_filter_val_lt] at hle
    have h1 : (0 : ℝ) ≤ (degOf Dw m : ℝ) ^ 2 * Φ / g' := by positivity
    have h2 : 2 * (degOf Dw m : ℝ) ^ 2 * Φ / g' = 2 * ((degOf Dw m : ℝ) ^ 2 * Φ / g') := by ring
    rw [h2, mul_comm (ρg : ℝ)]
    linarith

end GlobalTheory.PowGerm
end
