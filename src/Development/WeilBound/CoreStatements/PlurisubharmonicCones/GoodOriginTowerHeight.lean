import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalScheme
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormula
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullDegSum
import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPshPull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionOfChartAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominating
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactor
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmoothStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLine
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullCst

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OmLink

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem lv_ext_cancel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} {k : Type} [Field k]
    (i : Ω →+* k) {x x' : Over.mk ξ ⟶ G} (h : GenWeilModel.ext i ≫ x = GenWeilModel.ext i ≫ x') : x = x' := by
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun f => Over.Hom.left f) h
  simp only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1
  have := epi_sp i
  exact (cancel_epi _).1 h1

section obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

theorem lv_push_pow {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (a : T ⟶ G') (n : ℕ) :
    pushPt hp.1.w (a ^ n) = pushPt hp.1.w a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact push_one hp T
  | succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]

theorem lv_div (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) (y : Over.mk ξ ⟶ t.G) (hy : y ^ n = 1) :
    ∃ x : Over.mk ξ ⟶ t.G, x ^ (n * r) = 1 ∧ x ^ r = y := by
  classical
  have hp := m.cart
  let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨a, ha, hpa⟩ := pull_point hp i y hy
  obtain ⟨T⟩ := exists_tate o i
  obtain ⟨α, rfl⟩ := (T.onto n hn a).1 ha
  have hnr : 0 < n * r := Nat.mul_pos hn hr
  obtain ⟨y', -, hy'a⟩ := desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)
  let x : Over.mk ξ ⟶ t.G := Over.homMk (y'.left ≫ m.cm.F) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w y']
    simp)
  have hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α) := by
    apply Over.OverMorphism.ext
    rw [hy'a]
    simp [x, pushPt, GenWeilModel.ext, ex]
  have hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  refine ⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩
  · rw [hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]
  · rw [hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]

theorem lv_down [CharZero Ω] (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (x : Over.mk ξ ⟶ t.G) (hx : x ^ (n * r) = 1) (q : Cpt ξ) (w : Module.Dual Ω V)
    (h : M.IsHTAt t.PP.L (n * r) x q w) : M.IsHTAt t.PP.L n (x ^ r) q w := by
  obtain ⟨h0, W, f, h1, h2, h3⟩ := h
  refine ⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩
  · have hp := m.cart
    have hg' : g ^ (n * r) = 1 := by rw [pow_mul, hg, one_pow]
    obtain ⟨g₀, hg₀⟩ := hf k i g hg'
    have hg₁ : g = GenWeilModel.ext i ≫ g₀ := Over.OverMorphism.ext hg₀
    have hg₂ : g₀ ^ n = 1 := lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])
    obtain ⟨a, ha, hpa⟩ := pull_point hp i x hx
    obtain ⟨a', ha', hpa'⟩ := pull_point hp i g₀ hg₂
    have e1 : a'.left ≫ m.φ = g.left := (congrArg (fun z => z.left) hpa').trans hg₀.symm
    have e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left := congrArg (fun z => z.left) hpa
    have e3 : (a ^ r).left ≫ m.φ = xk.left := by
      have h4 := lv_push_pow hp a r
      have h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r := by
        rw [MonObj.comp_pow]
        exact h4.trans (congrArg (· ^ r) hpa)
      exact (congrArg (fun z => z.left) h5).trans hxk.symm
    refine h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1] at hc
    have hk : CharZero k := charZero_of_injective_ringHom i.injective
    have hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤)) := by
      have h6 : IsUnit ((n * r : ℕ) : k) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit
      have h7 := h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      rwa [map_natCast] at h7
    have h8 := ((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc
    rw [Nat.cast_mul]
    exact h8
  · obtain ⟨u, hu, he⟩ := h3 e v hev hv
    refine ⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩
    rw [he]
    push_cast
    ring

end obj

theorem lv_kappa {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    (hq : IsIntegrallyClosed (X.presheaf.stalk q.1)) {p : ℕ} (hp : p.Prime) {κ : Ω} (h : HT.IsCp p κ) :
    ∃ a ∈ regAt ξ q, ((p ^ 4 : ℕ) : Ω) = a * κ := by
  classical
  unfold HT.IsCp at h
  split_ifs at h with h2
  · subst h2 h
    refine ⟨4, ?_, by norm_num⟩
    simp
  · obtain ⟨ζ, hζ, rfl⟩ := h
    have hfact : Fact p.Prime := ⟨hp⟩
    have hmem : ζ ∈ primitiveRoots p Ω := (mem_primitiveRoots hp.pos).2 hζ
    have hc := congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at hc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc
    rw [← Finset.mul_prod_erase _ _ hmem] at hc
    refine ⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩
    · apply GlobalTheory.T.integral_element_regular X Ω ξ q hξ hq
      refine IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_
      refine IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_
      exact ((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos
    · push_cast
      rw [pow_succ, hc]
      ring

theorem levelFree : LevelFree := by
  intro hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq
  have hp := 𝔐.S_prime p hpS
  haveI := Fact.mk hp
  have : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono
  have hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']
    exact 𝔐.fn_over
  obtain ⟨s0, o, ⟨m⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀
  have hno := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have hnc := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree
  have hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4) := by
    rw [← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]
  have hsw := (hS q hq).2.2.1
  have hf := 𝔐.tors p hpS
  unfold HT.omP at hsw
  rw [hR] at hsw hf ⊢
  obtain ⟨a, ha, hae⟩ := lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ
  have hn : 0 < p ^ 4 := pow_pos hp.pos _
  have hr : 0 < p ^ (𝔐.R p - 4) := pow_pos hp.pos _
  generalize p ^ (𝔐.R p - 4) = r at *
  generalize p ^ 4 = n at *
  have hf' : FullTorsion 𝔐.t.G 𝔐.ξ n := fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])
  have hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e := fun N hN hfN => by
    have := GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN
      (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)
    rwa [Category.id_comp] at this
  obtain ⟨e, he⟩ := hw n hn hf'
  obtain ⟨e', he'⟩ := hw _ (Nat.mul_pos hn hr) hf
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro w ⟨z, hz, hw⟩
    obtain ⟨x, hx, rfl⟩ := lv_div o 𝔐.t m hn hr hf z hz
    obtain ⟨U, hU, w', hw'⟩ := (GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he'
      _ 𝔐.M q).1
    have h1 := hw' x hx q hU
    obtain ⟨u, hu, rfl⟩ := ((GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz
      (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw
    refine add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_
    have h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u := by
      rw [← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]
      rfl
    exact h2 ▸ Submodule.smul_mem _ _ (hsw u hu)
  · rintro w ⟨x, hx, hw⟩
    exact Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩

end LevelTowerAlt.Comparison₂
end
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem mh_inv {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b₀ b : Fin r → V}
    {T : Matrix (Fin r) (Fin r) Ω} (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (hT : T.det ≠ 0) (k : Fin r) :
    b₀ k = ∑ k', T⁻¹ k' k • b k' := by
  have e : ∑ k', T⁻¹ k' k • b k' = ∑ k', (T * T⁻¹) k' k • b₀ k' := by
    simp only [h, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [e, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hT)]
  simp [Matrix.one_apply]

section Q

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type}
  (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ)

def MhQ (c : ∀ k, J k) (a : K → ℤ) (ρ : Ω) (x : ℝ) : Prop :=
  ∃ u : ℂ, ValAt ξ z (ρ / ∏ k, y ⟨k, c k⟩ ^ a k) u ∧ x = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

variable {ξ y z w}

theorem mh_chg (h : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) {c c' : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) {a : K → ℤ} {ρ : Ω} {x : ℝ} (hQ : MhQ ξ y z w c a ρ x) : MhQ ξ y z w c' a ρ x := by
  obtain ⟨u, hu, rfl⟩ := hQ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (hc k))).1
  choose r hrv hrw using fun k => (hw.2 k _ (IsUnit.mk0 _ (hc' k))).2 (c k)
  have hr0 : ∀ k, r k ≠ 0 := fun k h0 => hc k (by rw [hrw k, h0, zero_mul])
  refine ⟨u * ∏ k, r k ^ a k, ?_, ?_⟩
  · have h1 := CxVal.mul hu (MuIndep.valAt_prod h Finset.univ fun k => CxVal.zpow (hrv k) (hr0 k) (a k))
    have h2 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
    simp only [div_zpow, Finset.prod_div_distrib] at h1
    rwa [div_mul_div_cancel₀ h2] at h1
  · rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_zpow, ← mul_zpow, ← norm_mul, ← hrw k]

theorem mh_mul (hw : CoordsAt ξ y z w) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {a a' : K → ℤ} {ρ ρ' : Ω} {x x' : ℝ}
    (hQ : MhQ ξ y z w c a ρ x) (hQ' : MhQ ξ y z w c a' ρ' x') : MhQ ξ y z w c (a + a') (ρ * ρ') (x * x') := by
  obtain ⟨u, hu, rfl⟩ := hQ
  obtain ⟨u', hu', rfl⟩ := hQ'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (hc k))).1
  refine ⟨u * u', ?_, ?_⟩
  · have h1 := CxVal.mul hu hu'
    simp only [Pi.add_apply, zpow_add₀ (hy _), Finset.prod_mul_distrib]
    rwa [div_mul_div_comm] at h1
  · simp only [Pi.add_apply, zpow_add₀ (norm_ne_zero_iff.2 (hc _)), Finset.prod_mul_distrib, norm_mul]
    ring

theorem mh_prod (h : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (S : Finset ℕ) {a : ℕ → K → ℤ} {ρ : ℕ → Ω} {x : ℕ → ℝ} (hQ : ∀ p ∈ S, MhQ ξ y z w c (a p) (ρ p) (x p)) :
    MhQ ξ y z w c (∑ p ∈ S, a p) (∏ p ∈ S, ρ p) (∏ p ∈ S, x p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simpa using CxVal.one h, by simp⟩
  | insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.prod_insert hp, Finset.prod_insert hp]
    exact mh_mul hw hc (hQ p (Finset.mem_insert_self _ _)) (ih fun q hq => hQ q (Finset.mem_insert_of_mem hq))

end Q

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mh_change (Or : CptOrigin Y S₀ Dc Hd) {bb : ∀ τ, Fin Dc.N → W τ}
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} {lam : Ω}
    (hs : ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ))
    (hΛ : Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)))
    {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) {s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs' : Or.IsSmallPart d s') :
    ∃ T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω,
      (∀ τ k, s τ k = ∑ k', T τ k' k • s' τ k') ∧ d.u * chartMono Dc.y d.c Hd.aMu = lam * ∏ τ, (T τ).det := by
  have hq' := fun τ => MuIndep.quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ) (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1
    (d.adapted τ).2.2
  have hco : ∀ τ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)) =
      (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N k)) := fun τ k =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [(hq' τ).2]; trivial)
  choose t ht using hco
  refine ⟨fun τ => Matrix.of fun a k => t τ k a, fun τ k => ?_, ?_⟩
  · have h1 : bb τ (tailIdx Dc.j_le_N k) - ∑ a, t τ k a • d.b τ (tailIdx Dc.j_le_N a) ∈ Hd.F τ := by
      refine (Submodule.Quotient.eq (Hd.F τ)).1 ?_
      have := ht τ k
      simp_rw [← map_smul] at this
      rw [← map_sum] at this
      exact this.symm
    rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum] at h1
    rw [← sub_eq_zero]
    refine (Submodule.disjoint_def.1 (MuIndep.blocks_disjoint Or τ)) _ ?_
      (sub_mem (hs τ k).1 (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).1))
    have e : s τ k - ∑ a, t τ k a • s' τ a =
        (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - ∑ a, Or.i τ (t τ k a • d.b τ (tailIdx Dc.j_le_N a))) -
          (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k) +
          ∑ a, t τ k a • (Or.i τ (d.b τ (tailIdx Dc.j_le_N a)) - s' τ a) := by
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    show s τ k - ∑ a, t τ k a • s' τ a ∈ _
    rw [e]
    exact add_mem (sub_mem h1 (hs τ k).2) (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).2)
  · exact GlobalTheory.T.tensor_wedge_det_change (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N a))) (fun τ => Matrix.of fun a k => t τ k a) _ _
      (fun τ => (hq' τ).1) (fun τ => (hq' τ).2) (fun τ k => (ht τ k).symm) (d.eq.symm.trans hΛ)

end Main

theorem mh_char0 {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}
    (h : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) : ¬ InFibre ξ p ⟨centre z, h⟩ := by
  have h1 : ValAt ξ z (p : Ω) (p : ℂ) := ⟨h, p, map_natCast _ p, map_natCast _ p⟩
  obtain ⟨_, x, hx, -⟩ := CxVal.inv h1 (Nat.cast_ne_zero.2 hp.ne_zero)
  exact not_not.2 ⟨Nat.cast_ne_zero.2 hp.ne_zero, natCast_mem _ _, x, hx⟩

theorem muHodge : MuHodge := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B bb s lam hs hΛ z w hw hi
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hmc : w ∈ mcPts (mCoordIdeal Dc.y) := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w).2 ⟨z, h, hw⟩
  obtain ⟨d⟩ := GlobalTheory.T.component_data_hodge_first E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw
  obtain ⟨s', hs'⟩ := PhMuFree.exists_smallPart Or d
  obtain ⟨Γ, hΓ, hpd, -⟩ := PhMuFree.norm_eq Or hw hi d hs'
  have hph := PhMuFree.phMu_eq Or hw hi d hs' hΓ
  obtain ⟨T, hT, hΩ⟩ := mh_change Or hs hΛ d hs'
  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hy : ∀ k, Dc.y ⟨k, d.c k⟩ ≠ 0 := fun k => (hw.2 k _ (IsUnit.mk0 _ (d.inDom.1 k))).1
  have hm : chartMono Dc.y d.c Hd.aMu ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have n₀ : lam * ∏ τ, (T τ).det ≠ 0 := hΩ ▸ mul_ne_zero d.unit.1 hm
  have hlam : lam ≠ 0 := left_ne_zero_of_mul n₀
  have hd : ∀ τ, (T τ).det ≠ 0 := fun τ => Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul n₀) τ (Finset.mem_univ τ)
  have hex : ∃ c : (k : K) → J k, ∀ k, w ⟨k, c k⟩ ≠ 0 := ⟨d.c, d.inDom.1⟩
  have hvert : ∀ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 ∧
      MhQ Or.𝔐.ξ Dc.y z w d.c (Dc.vdeg p)
        (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p)) (Dc.vertFactor p w) := by
    intro p hp
    have hv := Dc.vertical p (hS p hp)
    obtain ⟨v, -, hv1⟩ := VertFactorPos.exists_value hmc (Dc.S_prime p (hS p hp)).ne_zero hv hex.choose hex.choose_spec
    refine ⟨?_, mh_chg h hw hex.choose_spec d.inDom.1 ⟨v, ?_, ?_⟩⟩
    · obtain ⟨bf, bg, hf, hg, -⟩ := hv.degrees
      exact div_ne_zero (fun h0 => hv.num_not_mem ((VertFactorPos.mem_mCoordIdeal_iff_of_homog _ hf).2 h0))
        fun h0 => hv.den_not_mem ((VertFactorPos.mem_mCoordIdeal_iff_of_homog _ hg).2 h0)
    · have h1 := (GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).2 hv1
      simp only [chartMono, Pi.neg_apply, _root_.zpow_neg, Finset.prod_inv_distrib] at h1
      rwa [← div_eq_mul_inv] at h1
    · rw [ComponentData.vertFactor, dif_pos hex, valAt_eq hmc hv1, zMono, norm_prod]
      simp only [norm_zpow]
  have hQ1 : MhQ Or.𝔐.ξ Dc.y z w d.c Hd.aMu (lam * ∏ τ, (T τ).det)
      (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) := by
    refine ⟨_, ?_, rfl⟩
    rw [← hΩ]
    show ValAt _ _ (d.u * chartMono Dc.y d.c Hd.aMu / chartMono Dc.y d.c Hd.aMu) _
    rw [mul_div_cancel_right₀ _ hm]
    exact hu.2
  have hQ := mh_mul hw d.inDom.1 hQ1 (mh_prod h hw d.inDom.1 (Dc.SB B) fun p hp => (hvert p hp).2)
  have hA : 0 < ‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    mul_pos (norm_pos_iff.2 hu.1) (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _)
  have hsq : ∀ τ, 0 < Real.sqrt (Γ τ).det.re := fun τ => Real.sqrt_pos.2 (PhMuFree.det_re_pos (hpd τ))
  have hsq' : 0 < ∏ τ, Real.sqrt (Γ τ).det.re := Finset.prod_pos fun τ _ => hsq τ
  have hvp : ∀ p ∈ Dc.SB B, 0 < Dc.vertFactor p w := fun p hp => VertFactorPos.proof II _ K J Ω W Dc p (hS p hp) w hmc
  have hvp' : 0 < ∏ p ∈ Dc.SB B, Dc.vertFactor p w := Finset.prod_pos hvp
  have hh : (muVert Hd B).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      (∏ p ∈ Dc.SB B, Dc.vertFactor p w) * ∏ τ, Real.sqrt (Γ τ).det.re := by
    refine Real.log_injOn_pos ((muVert Hd B).pos w hmc.1) (mul_pos (mul_pos hA hvp') hsq') ?_
    rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II _ Ω W Dc Hd B w hmc, Real.log_mul (mul_pos hA hvp').ne' hsq'.ne', Real.log_mul hA.ne' hvp'.ne',
      Real.log_prod fun p hp => (hvp p hp).ne', Real.log_prod fun τ _ => (hsq τ).ne']
    have e : ∑ τ, Real.log (Real.sqrt (Γ τ).det.re) = (∑ τ, Real.log (Γ τ).det.re) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (PhMuFree.det_re_pos (hpd τ)).le
    have e' : Real.log ((muLine Hd).h w) = phMu Hd w := rfl
    rw [e, e', hph]
    ring
  have hP : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hvert p hp).1
  have hP' : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p) =
      (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => (inv_div _ _).symm
  refine ⟨h, s', fun τ => (T τ)⁻¹, Γ, fun τ => ⟨?_, mh_inv (hT τ) (hd τ), hΓ τ, hpd τ⟩, ?_, hw, fun c' hc' => ?_⟩
  · have hf := (PhMuFree.frames Or hw d hs' τ h).2.1
    refine ⟨hf.1, Eq.trans ?_ hf.2⟩
    refine (Lat.patch_of_not _ _ _ fun p hp => mh_char0 h ?_).trans
      (Lat.patch_of_not _ _ _ fun p hp => mh_char0 h (Or.𝔐.S_prime p hp)).symm
    exact (Finset.mem_union.1 hp).elim (Or.𝔐.S_prime p) fun hp => Dc.S_prime p (hS p hp)
  · rw [hP']
    exact mul_ne_zero (inv_ne_zero hlam) (inv_ne_zero hP)
  · obtain ⟨u, hu1, hu2⟩ := mh_chg h hw d.inDom.1 hc' hQ
    refine ⟨u, ?_, ?_⟩
    · convert hu1 using 1
      have e : ∏ τ, ((T τ)⁻¹).det = (∏ τ, (T τ).det)⁻¹ := by
        rw [← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun τ _ => by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      rw [hP', e, inv_inv]
      show _ / ((∏ k, Dc.y ⟨k, c' k⟩ ^ (Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p) k) * _) = _
      field_simp
    · rw [hh]
      refine Eq.trans ?_ hu2
      field_simp

end LevelTowerAlt.Comparison₂
end
end

section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open scoped ContDiff

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem c2at (A : FinHolAtlas e X) {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ P.U x) : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hy, hU⟩)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

theorem levi_shift {F G : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) (a b : ℝ)
    (w : Fin e → ℂ) : levi (fun z => F z + a * G z + b) y w = levi F y w + a * levi G y w := by
  have h1 := TailChernBound.levi_lin 1 a hF hG w
  have h2 := TailChernBound.levi_lin 1 b ((contDiffAt_const (c := (1 : ℝ))).mul hF |>.add
    ((contDiffAt_const (c := a)).mul hG)) (contDiffAt_const (c := (1 : ℝ))) w
  have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y w = 0 := by simp [levi]
  rw [h0, h1] at h2
  simpa using h2

variable [CompactSpace X] [T2Space X]

theorem term_zero (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPosPot A (Θ i)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) (C₁ C₆ : ℝ) (hC₁ : 0 ≤ C₁)
    (u : ℝ → Fin e → X → ℝ) (g : ℝ → X → ℝ)
    (hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (u t i)) ∧ (∀ i, IsPsh A (Θ i + LocPot.ofFun (u t i))) ∧
      ∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u t i y ∧ u t i y ≤ 0)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), Continuous (g t) ∧ ∀ y ∉ bdry s, |g t y| ≤ C₆ * Real.log (rW L s y))
    (hg0 : ∀ K ⊆ (bdry s)ᶜ, IsCompact K → TendstoUniformlyOn g (fun _ => 0) (𝓝[>] 0) K) :
    Tendsto (fun t => mInt A (fun i => Θ i + LocPot.ofFun (u t i)) (g t)) (𝓝[>] 0) (𝓝 0) := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.tail_bound_statement_holds A Θ L s m W hΘ hΘp hL hs hsnc hle
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hle
  have hlog : ∀ y, 0 ≤ Real.log (rW L s y) := fun y =>
    Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hr y))
  set M : ℝ := |C * (C₁ + 3) * Real.log (Real.exp 1) / Real.exp 1| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hT : Tendsto (fun R : ℝ => |C₆| * (C * (C₁ + 3)) * (Real.log R ^ 2 / R)) atTop (𝓝 0) := by
    simpa using ((Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero).const_mul (|C₆| * (C * (C₁ + 3)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR1, hR2⟩ := ((hT.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop (Real.exp 1))).exists
  set δ : ℝ := ε / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hK := GlobalTheory.CompanionTheory.Ar.Giv.isCompact_rW_sublevel A L s hL hs R
  have hun := Metric.tendstoUniformlyOn_iff.1 (hg0 _ (fun y hy => hy.1) hK) δ hδ0
  filter_upwards [hu, hg, hun] with t ⟨hu1, hu2, hu3⟩ ⟨hg1, hg2⟩ hun
  have hpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u t i)) := fun i =>
    isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu1 i))
  have hI := ((maMeasure_thm A _ hpot hu2).2 (g t) hg1.measurable).2 (mIntegrableCont A _ hpot _ hg1)
  have hnull := bdry_null A L s m W hL hs hsnc _ hpot
  have hmass := (hC C₁ (u t) hC₁ hu1 hu2 hu3 (Real.exp 1) le_rfl).1
  have htail := (hC C₁ (u t) hC₁ hu1 hu2 hu3 R hR2).2
  set μ := maMeasure A fun i => Θ i + LocPot.ofFun (u t i) with hμ
  have huniv : bdry s ∪ {y | Real.exp 1 ≤ rW L s y} = Set.univ := Set.eq_univ_of_forall fun y => Or.inr (hr y)
  rw [huniv] at hmass
  replace hmass : μ Set.univ ≤ ENNReal.ofReal M := hmass.trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hBo : IsOpen (bdry s)ᶜ := by
    have h1 : (bdry s)ᶜ = ⋃ k : ℕ, {y | y ∉ bdry s ∧ rW L s y < k} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨fun h => (exists_nat_gt (rW L s y)).imp fun k hk => ⟨h, hk⟩, fun ⟨_, h, _⟩ => h⟩
    rw [h1]
    exact isOpen_iUnion fun k => (rW_open A L s hL hs).2 k
  have hE : MeasurableSet ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) := by
    have h1 : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = (bdry s)ᶜ \ {y | y ∉ bdry s ∧ rW L s y < R} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_lt]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [h1]
    exact hBo.measurableSet.diff ((rW_open A L s hL hs).2 R).measurableSet
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal ‖g t y‖ ≤ ENNReal.ofReal δ + ENNReal.ofReal |C₆| *
      ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}).indicator (fun y => ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    by_cases h : R ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | R ≤ rW L s y} from ⟨hy, h⟩),
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact (hg2 y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hlog y))
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      have := hun y ⟨hy, (not_le.1 h).le⟩
      rw [dist_comm, dist_zero_right] at this
      exact this.le
  have hb : ∫⁻ y, ENNReal.ofReal ‖g t y‖ ∂μ ≤
      ENNReal.ofReal (δ * M + max (|C₆| * (C * (C₁ + 3) * Real.log R ^ 2 / R)) 0) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator hE, ENNReal.ofReal_add (by positivity) (le_max_right _ _), ENNReal.ofReal_mul hδ0.le]
    refine add_le_add (by gcongr) ?_
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    gcongr
  rw [hI, dist_zero_right]
  refine (norm_integral_le_lintegral_norm _).trans_lt ?_
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hb).trans_lt ?_
  have h1 : δ * M < ε / 2 := by
    have : δ * (M + 1) = ε / 2 := by rw [hδ]; field_simp
    nlinarith
  have h2 : max (|C₆| * (C * (C₁ + 3) * Real.log R ^ 2 / R)) 0 < ε / 2 :=
    max_lt (by convert hR1 using 1; ring) (half_pos hε)
  linarith

set_option maxHeartbeats 1000000 in
theorem weak_zero (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hL : IsPotential A L)
    (hs : IsSection A L s) (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) (P : Fin e → LocPot X)
    (hP : ∀ i, IsPotential A (P i)) (Q : ℝ → Fin e → LocPot X) (f : ℝ → Fin e → X → ℝ) (g : ℝ → X → ℝ)
    (C : Fin e → ℝ) (C₆ : ℝ)
    (hQ : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (f t i) ∧ IsPotential A (Q t i) ∧ (∀ x, (Q t i).U x = (P i).U x) ∧
      (∀ x, ∀ y ∈ (P i).U x, (Q t i).φ x y = (P i).φ x y + f t i y) ∧ IsPsh A (Q t i + Θ.rsmul (C i)) ∧
      ∀ y ∉ bdry s, -C i * Real.log (rW L s y) ≤ f t i y ∧ f t i y ≤ C i)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), Continuous (g t) ∧ ∀ y ∉ bdry s, |g t y| ≤ C₆ * Real.log (rW L s y))
    (hg0 : ∀ K ⊆ (bdry s)ᶜ, IsCompact K → TendstoUniformlyOn g (fun _ => 0) (𝓝[>] 0) K) :
    Tendsto (fun t => mInt A (Q t) (g t)) (𝓝[>] 0) (𝓝 0) := by
  classical
  choose D hD0 hD _ using fun i => TailBoundAlt.exists_psh_chern_bound A Θ (P i) hΘ hΘp (hP i)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ i, (|C i| + D i) + 1 := ⟨_, rfl⟩
  have hci : ∀ i, |C i| + D i + 1 ≤ c := fun i => by
    have := Finset.single_le_sum (f := fun i => |C i| + D i) (fun i _ => add_nonneg (abs_nonneg _) (hD0 i))
      (Finset.mem_univ i)
    linarith
  have hc0 : 0 < c := by
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun i => |C i| + D i) fun i _ => add_nonneg (abs_nonneg _) (hD0 i)
    linarith
  have hΘ' : IsPotential A (Θ.rsmul c) := isPotentialRsmul A c Θ hΘ
  have hΘ'p : IsPosPot A (Θ.rsmul c) := fun x j y hy w hw => by
    have := TailChernBound.levi_smul' c (c2at A hΘ x j hy.1 hy.2) w
    exact lt_of_lt_of_eq (mul_pos hc0 (hΘp x j y hy w hw)) this.symm
  have hT : ∀ i, IsPotential A (P i + Θ.rsmul c) := fun i => isPotentialAdd A _ _ (hP i) hΘ'
  have hTp : ∀ i, IsPosPot A (P i + Θ.rsmul c) := fun i x j y hy w hw => by
    have h1 := hD i x j y ⟨hy.1, hy.2.2, hy.2.1⟩ w
    have h2 := levi_shift (c2at A (isPotentialAdd A _ _ (isPotentialRsmul A (D i) Θ hΘ) (hP i)) x j hy.1 ⟨hy.2.2, hy.2.1⟩)
      (c2at A hΘ x j hy.1 hy.2.2) (c - D i) 0 w
    have h3 : (P i + Θ.rsmul c).φ x ∘ (A.chart j).symm = fun z => ((Θ.rsmul (D i) + P i).φ x ∘ (A.chart j).symm) z +
        (c - D i) * (Θ.φ x ∘ (A.chart j).symm) z + 0 := by
      funext z
      show (P i).φ x _ + c * Θ.φ x _ = D i * Θ.φ x _ + (P i).φ x _ + (c - D i) * Θ.φ x _ + 0
      ring
    rw [h3, h2]
    have := mul_pos (show 0 < c - D i by linarith [hci i, abs_nonneg (C i)]) (hΘp x j y ⟨hy.1, hy.2.2⟩ w hw)
    linarith
  have hlog : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (rW_ge L s hle y))]
    exact rW_ge L s hle y
  have hQ' := eventually_all.2 hQ
  have hsm : ∀ {v : X → ℝ}, A.Smooth v → A.Smooth fun y => v y - c := fun hv j => (hv j).sub contDiffOn_const
  have hterm : ∀ S : Finset (Fin e), Tendsto (fun t => mInt A (fun i => (if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) +
      LocPot.ofFun (if i ∈ S then fun y => f t i y - c else fun _ => 0)) (g t)) (𝓝[>] 0) (𝓝 0) := by
    intro S
    refine term_zero A (fun i => if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) L s m W
      (fun i => by split_ifs; exacts [hT i, hΘ']) (fun i => by split_ifs; exacts [hTp i, hΘ'p]) hL hs hsnc hle (2 * c) C₆
      (by linarith) (fun t i => if i ∈ S then fun y => f t i y - c else fun _ => 0) g ?_ hg hg0
    filter_upwards [hQ'] with t ht
    refine ⟨fun i => ?_, fun i => ?_, fun i y hy => ?_⟩
    · split_ifs
      exacts [hsm (ht i).1, fun j => contDiffOn_const]
    · split_ifs
      · obtain ⟨-, h2, h3, h4, h5, -⟩ := ht i
        intro x j y hy w
        have hyP : (A.chart j).symm y ∈ (P i).U x := hy.2.1.1
        have hyT : (A.chart j).symm y ∈ Θ.U x := hy.2.1.2
        have hyQ : (A.chart j).symm y ∈ (Q t i + Θ.rsmul (C i)).U x := ⟨(h3 x).symm ▸ hyP, hyT⟩
        have a1 := h5 x j y ⟨hy.1, hyQ⟩ w
        have a2 := levi_shift (c2at A (isPotentialAdd A _ _ h2 (isPotentialRsmul A (C i) Θ hΘ)) x j hy.1 hyQ)
          (c2at A hΘ x j hy.1 hyT) (c - C i) (-c) w
        have a3 : (P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c).φ x ∘ (A.chart j).symm =ᶠ[𝓝 y]
            fun z => ((Q t i + Θ.rsmul (C i)).φ x ∘ (A.chart j).symm) z +
              (c - C i) * (Θ.φ x ∘ (A.chart j).symm) z + -c := by
          filter_upwards [((A.chart j).isOpen_inter_preimage_symm ((P i).isOpen_U x)).mem_nhds ⟨hy.1, hyP⟩] with z hz
          show (P i).φ x _ + c * Θ.φ x _ + (f t i _ - c) = (Q t i).φ x _ + C i * Θ.φ x _ + (c - C i) * Θ.φ x _ + -c
          rw [h4 x _ hz.2]
          ring
        rw [levi_congr a3, a2]
        have := mul_nonneg (show 0 ≤ c - C i by linarith [hci i, le_abs_self (C i), hD0 i])
          (TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y ⟨hy.1, hyT⟩ w)
        linarith
      · refine TailBoundAlt.isPsh_congr A _ _ (TailBoundAlt.isPsh_of_isPosPot A _ hΘ'p) (fun x y hy => hy.1) ?_
        funext x y
        exact add_zero _
    · have h1 := hlog y
      split_ifs
      · obtain ⟨h2, h3⟩ := (ht i).2.2.2.2.2 y hy
        have h4 := hci i
        have h5 := le_abs_self (C i)
        have h6 := hD0 i
        constructor
        · nlinarith
        · linarith
      · exact ⟨by nlinarith, le_rfl⟩
  have hsum := tendsto_finsetSum Finset.univ fun S (_ : S ∈ Finset.univ) => (hterm S).const_mul ((-1 : ℝ) ^ (e - S.card))
  simp only [mul_zero, Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hQ', hg] with t ht hgt
  have hΦ : ∀ i, IsPotential A (P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c) := fun i =>
    isPotentialAdd A _ _ (hT i) (isPotential_ofFun A _ (hsm (ht i).1))
  have h1 := mixed_integral_inclusion_exclusion A (Θ.rsmul c) _ hΘ' hΦ (g t) hgt.1
  have h2 := (mInt_congr_samePot e X A Set.univ (Q t)
    (fun i => P i + Θ.rsmul c + (LocPot.ofFun fun y => f t i y - c) + (Θ.rsmul c).rsmul (-1)) (g t) (g t)
    (by simp [IsNull]) (fun i x _ => ⟨(P i).U x, (P i).isOpen_U x, (P i).mem_U x, fun _ => c,
      fun j => analyticOnNhd_const, fun y hy => by
        show (Q t i).φ x y - ((P i).φ x y + c * Θ.φ x y + (f t i y - c) + -1 * (c * Θ.φ x y)) = c
        rw [(ht i).2.2.2.1 x y hy]
        ring⟩)
    (fun i x _ => GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.isC2At_of_isPotential A
      (isPotentialAdd A _ _ (hΦ i) (isPotentialRsmul A (-1) _ hΘ')) x) (fun _ _ => rfl)).1
  rw [h2, h1]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  unfold mInt integralWith locDens
  have : ∀ i, ((if i ∈ S then P i + Θ.rsmul c else Θ.rsmul c) +
      LocPot.ofFun (if i ∈ S then fun y => f t i y - c else fun _ => 0)).φ =
      (if i ∈ S then P i + Θ.rsmul c + LocPot.ofFun fun y => f t i y - c else Θ.rsmul c).φ := fun i => by
    split_ifs
    · rfl
    · funext x y
      exact add_zero _
  simp only [this]

end LevelTowerAlt.Comparison₂
end
end

section
noncomputable section

namespace LevelTowerAlt.Comparison₂

open MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot

theorem one_coord₂ (hBr : ResBridgeStatement) (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hIso : IsLineIso P A.a B.a f g) (hw : IsDefectOn P (mcPts P) f g A B w) :
    I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) =
      -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  obtain ⟨⟨α, γ, hfα, hgγ, hdeg⟩, hU⟩ := hIso
  have hfP : f ∉ P := hU.1
  have hgP : g ∉ P := hU.2.1
  set M' : HermLine ι := fsOfDeg γ with hM'def
  set M : HermLine ι := twist M' A B with hMdef
  have hM' : IsSmoothHerm M' := isSmoothHerm_fsOfDeg γ
  have hM : IsSmoothHerm M := isSmoothHerm_twist hM' hA hB
  have hMa : ∀ k, M.a k = α k := by
    intro k
    have h := hdeg k
    have e1 : M.a k = (γ k : ℤ) + A.a k + -B.a k := rfl
    rw [e1]
    linarith
  have hM'a : ∀ k, M'.a k = γ k := fun _ => rfl

  have a1 := hI.2.1 P e L M B hP hL hM hB
  have a2 := hI.2.1 P e L M' A hP hL hM' hA
  have ht : M.tensor B = M'.tensor A := twist_tensor (fun z hz => fsOfDeg_h_of_notMem γ hz) A B
  rw [ht] at a1

  have r1 := hI.2.2 P e L M f α hP hL hM hMa hfα hfP
  have r2 := hI.2.2 P e L M' g γ hP hL hM' hM'a hgγ hgP
  rw [recR_eq] at r1 r2

  have hc := GlobalTheory.T.unit_ratio_same_divisor_multiplicities K ι P f g hU
  have hcyc : cycR I P L f = cycR I P L g := by
    unfold cycR
    refine finsum_mem_congr hc.1 fun W hW => ?_
    rw [hc.2 W (hc.1 ▸ hW)]

  have hsf : IsSectionOn P M f := ⟨α, hMa, hfα, hfP⟩
  have hsg : IsSectionOn P M' g := ⟨γ, hM'a, hgγ, hgP⟩
  rw [arInt_eq_mInt hBr hG R hP hL hM hsf] at r1
  rw [arInt_eq_mInt hBr hG R hP hL hM' hsg] at r2
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => potOf_isPotential R (L i) (hL i)
  have hlin := mIntLinear R.A (fun j => potOf R (L j)) hpot (-1)
    (fun x => logNorm M' g (R.lift x x)) (fun x => logNorm M f (R.lift x x))
    (brIntegrable R L M' g hP hL hM' hsg) (brIntegrable R L M f hP hL hM hsf)
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  have hw' : mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) =
      mInt R.A (fun j => potOf R (L j))
        (fun x => -1 * logNorm M' g (R.lift x x) + logNorm M f (R.lift x x)) := by
    refine mInt_congr_null _ _ fun j => ?_
    refine measure_mono_null ?_ (measure_union_null (zeros_null R Ψ hP hΨ hfα hfP j)
      (zeros_null R Ψ hP hΨ hgγ hgP j))
    rintro y ⟨hyt, hy⟩
    by_contra hcon
    have hnf : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) f ≠ 0 :=
      fun h => hcon (Or.inl ⟨hyt, h⟩)
    have hng : evC (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) g ≠ 0 :=
      fun h => hcon (Or.inr ⟨hyt, h⟩)
    have hmem := R.mem ((R.A.chart j).symm y) _ (R.mem_U ((R.A.chart j).symm y))
    apply hy
    have hd := hw _ hmem g f (by rw [mul_comm, sub_self]; exact P.zero_mem) hng
    have := logNorm_sub_eq (M := M') (A := A) (B := B) (show _ ∈ blockSet ι from hmem.1) hnf hng
    show w _ = -1 * logNorm M' g _ + logNorm M f _
    rw [hd, ← this]
    ring
  rw [hw', hlin]
  linarith

end LevelTowerAlt.Comparison₂
end
end

section
open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

theorem log_sub_lift (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (x : R.X) {y : R.X} (hy : y ∈ R.U x) :
    Real.log (A.h (R.lift x y)) = Real.log (A'.h (R.lift x y)) +
      (Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y))) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hz := (R.mem x y hy).1
  have hp : (∏ k, ‖c k‖ ^ A'.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, A.smul c _ hc, A'.smul c _ hc, h, Real.log_mul hp (A.pos _ hz).ne', Real.log_mul hp (A'.pos _ hz).ne']
  ring

theorem smooth_log_sub (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') : R.A.Smooth fun y => Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y)) := by
  intro j y hy
  have hn := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U ((R.A.chart j).symm y))).mem_nhds
    ⟨hy.1, R.mem_U _⟩
  have h1 := (((potOf_isPotential R A hA).1 ((R.A.chart j).symm y) j).sub
    ((potOf_isPotential R A' hA').1 ((R.A.chart j).symm y) j)).contDiffAt hn
  refine (h1.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with z hz
  have := log_sub_lift R h ((R.A.chart j).symm y) hz.2
  show _ - _ = Real.log (A.h (R.lift _ _)) - Real.log (A'.h (R.lift _ _))
  linarith

theorem position_zero {I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ} (hI : IsIntersectionFamily I)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0)
    (l : Fin e → ℝ → HermLine J) (hl : ∀ j, Tame R Θ L s (l j)) {A₁ A₂ : ℝ → HermLine J} {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ} (hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A₁ t) ∧ IsSmoothHerm (A₂ t))
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (A₁ t).a (A₂ t).a f g ∧ IsDefectOn P (mcPts P) f g (A₁ t) (A₂ t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => I P (e + 1) (Fin.snoc (fun j => l j t) (A₂ t)) - I P (e + 1) (Fin.snoc (fun j => l j t) (A₁ t)))
      (𝓝[>] 0) (𝓝 0) := by
  choose ref c href hev using hl
  have h := weak_zero R.A Θ L s mb Wb hΘ hΘp hL hs hsnc hle (fun j => potOf R (ref j))
    (fun j => potOf_isPotential R _ (href j)) (fun t j => potOf R (l j t))
    (fun t j y => Real.log ((l j t).h (R.lift y y)) - Real.log ((ref j).h (R.lift y y))) (fun t x => w t (R.lift x x)) c C
    (fun j => (hev j).mono fun t ht => ⟨smooth_log_sub R ht.2.1 ht.1 (href j), potOf_isPotential R _ ht.1, fun _ => rfl,
      fun x y hy => log_sub_lift R ht.2.1 x hy, ht.2.2.1, ht.2.2.2⟩) ?_ hw0
  · refine h.congr' ?_
    filter_upwards [hsm, hw, eventually_all.2 hev] with t h1 h2 h3
    have := one_coord₂ GlobalTheory.T.resolution_statement_holds Link.goodProjExistsStatement_holds hI R (fun j => l j t) (A₁ t) (A₂ t) f g (w t) hP
      (fun j => (h3 j).1) h1.1 h1.2 h2.1 h2.2.1
    linarith
  · filter_upwards [hsm, hw] with t h1 h2
    refine ⟨?_, h2.2.2⟩
    obtain ⟨w', a1, -, a2⟩ := GlobalTheory.T.line_isomorphism_defect_function K J P B e R (A₁ t) (A₂ t) f g hP.2.1 h2.1 h1.1 h1.2
    refine (OneModel.continuous_of_smooth R.A a2).congr fun x => ?_
    have hz := R.mem x x (R.mem_U x)
    obtain ⟨u, v, huv, hu, -⟩ := OneModel.exists_pair_ne h2.1.2 hz
    rw [a1 _ hz u v huv hu, h2.2.1 _ hz u v huv hu]

theorem comb_single {τ : Type} [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (a : τ) :
    Top.combLine l (Pi.single a 1) = l a := by
  refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ j, (Pi.single a 1 : τ → ℤ) j • (l j).a = _
    simp [Pi.single_apply]
  · show ∏ j, (l j).h z ^ (Pi.single a 1 : τ → ℤ) j = _
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

theorem ii_comb_snoc {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) (hP : IsArithVar P (e + 1)) {τ : Type}
    [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (hl : ∀ a, IsSmoothHerm (l a)) (ν : Fin e → τ → ℤ) (a : τ) :
    II K J P (e + 1) (Fin.snoc (fun k => Top.combLine l (ν k)) (l a)) =
      ∑ w : Fin e → τ, (∏ k, (ν k (w k) : ℝ)) * II K J P (e + 1) (Fin.snoc (fun k => l (w k)) (l a)) := by
  have h := GlobalTheory.T.arith_intersection_multilinear_all II hII K J P (e + 1) τ l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1)) hP hl
  have h1 : (fun k => Top.combLine l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1) k)) =
      Fin.snoc (α := fun _ => HermLine J) (fun k => Top.combLine l (ν k)) (l a) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [comb_single]
    · simp
  rw [← h1, h, ← (Fin.snocEquiv fun _ => τ).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    · simp [Fin.prod_univ_castSucc, Fin.snocEquiv]
    · congr 1
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [Fin.snocEquiv]
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [Fin.prod_univ_castSucc, Fin.snocEquiv, hb]
  · simp

theorem replace_gen {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) {d : ℕ} (hd : d = e + 1)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0) {σ : Type} [Fintype σ]
    (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J) (m : σ → ℤ) (n : Fin d → σ → ℤ) (q : Fin d → Prop) [DecidablePred q]
    (hq : ∀ k, q k → n k = m) (hA : ∀ i, Tame R Θ L s fun t => A t i) (hM : Tame R Θ L s M) {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ}
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => II K J P d (fun k => if q k then M t else Top.combLine (A t) (n k)) -
      II K J P d fun k => Top.combLine (A t) (n k)) (𝓝[>] 0) (𝓝 0) := by
  classical
  subst hd
  have hAs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsSmoothHerm (A t i) := eventually_all.2 fun i => by
    obtain ⟨_, _, -, h⟩ := hA i
    exact h.mono fun t ht => ht.1
  have hMs : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (M t) := by
    obtain ⟨_, _, -, h⟩ := hM
    exact h.mono fun t ht => ht.1
  have hc : ∀ t, (∀ i, IsSmoothHerm (A t i)) → ∀ r, IsSmoothHerm (Top.combLine (A t) r) := fun t h r =>
    (GlobalTheory.T.hermitian_combination_smooth_conj K J σ (A t) r).1 h
  let l : ℝ → Option (Option σ) → HermLine J := fun t o => o.elim (Top.combLine (A t) m) fun o' => o'.elim (M t) (A t)
  let ν : (σ → ℤ) → Option (Option σ) → ℤ := fun r o => o.elim 0 fun o' => o'.elim 0 r
  have hν : ∀ t r, Top.combLine (l t) (ν r) = Top.combLine (A t) r := fun t r => by
    refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
    · show ∑ j, ν r j • (l t j).a = ∑ j, r j • (A t j).a
      simp [Fintype.sum_option, ν, l]
    · show ∏ j, (l t j).h z ^ ν r j = ∏ j, (A t j).h z ^ r j
      simp [Fintype.prod_option, ν, l]
  have hstep : ∀ i : Fin (e + 1), Tendsto (fun t =>
      II K J P (e + 1) (fun j => if j < i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j)) -
      II K J P (e + 1) (fun j => if j ≤ i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    by_cases hi : q i
    swap
    · refine tendsto_const_nhds.congr fun t => (sub_eq_zero.2 (congrArg _ (funext fun j => ?_))).symm
      rcases lt_trichotomy j i with h | rfl | h
      · simp [h, h.le]
      · simp [hi]
      · simp [h.not_gt, h.not_ge]
    let μ : Fin e → Option (Option σ) → ℤ := fun k =>
      if ¬ i.succAbove k < i ∧ q (i.succAbove k) then Pi.single (some none) 1 else ν (n (i.succAbove k))
    have hμ0 : ∀ k, μ k none = 0 := fun k => by
      simp only [μ]
      split_ifs
      · simp
      · rfl
    have hμ : ∀ t k, Top.combLine (l t) (μ k) = if i.succAbove k < i then Top.combLine (A t) (n (i.succAbove k)) else
        if q (i.succAbove k) then M t else Top.combLine (A t) (n (i.succAbove k)) := fun t k => by
      simp only [μ]
      by_cases h1 : i.succAbove k < i
      · simp [h1, hν]
      · by_cases h2 : q (i.succAbove k)
        · simp only [h1, h2, not_false_eq_true, and_self, if_true, if_false]
          exact comb_single _ _
        · simp [h1, h2, hν]
    have hterm : ∀ u : Fin e → Option (Option σ), Tendsto (fun t => (∏ k, (μ k (u k) : ℝ)) *
        (II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (M t)) -
          II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (Top.combLine (A t) m)))) (𝓝[>] 0) (𝓝 0) := by
      intro u
      by_cases hu : ∃ k, u k = none
      · obtain ⟨k, hk⟩ := hu
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, hμ0, Int.cast_zero])]
        simp
      · have h := position_zero (hII.1 K J) R hP hΘ hΘp hL hs hsnc hle (fun k t => l t (u k)) (fun k => by
          rcases hk : u k with _ | _ | a
          · exact absurd ⟨k, hk⟩ hu
          · exact hM
          · exact hA a) ((hAs.and hMs).mono fun t ht => ⟨hc t ht.1 m, ht.2⟩) hw hw0
        simpa using h.const_mul (∏ k, (μ k (u k) : ℝ))
    have hsum := tendsto_finsetSum Finset.univ fun u (_ : u ∈ Finset.univ) => hterm u
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hAs, hMs] with t h1 h2
    have hl : ∀ o, IsSmoothHerm (l t o) := by
      rintro (_ | _ | a)
      exacts [hc t h1 m, h2, h1 a]
    have s₁ := GlobalTheory.T.intersection_family_symmetric K J (II K J) (hII.1 K J) P e (fun j => if j < i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have s₂ := GlobalTheory.T.intersection_family_symmetric K J (II K J) (hII.1 K J) P e (fun j => if j ≤ i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have hiff : ∀ k : Fin e, i.succAbove k ≤ i ↔ i.succAbove k < i := fun k =>
      ⟨fun h => lt_of_le_of_ne h (Fin.succAbove_ne i k), le_of_lt⟩
    simp only [lt_irrefl, le_refl, hi, if_true, if_false, hiff, hq i hi, ← hμ] at s₁ s₂
    rw [s₁, s₂]
    have e₁ := ii_comb_snoc hII hP (l t) hl μ (some none)
    have e₂ := ii_comb_snoc hII hP (l t) hl μ none
    refine Eq.trans ?_ (congrArg₂ (· - ·) e₁ e₂).symm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
  have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (GlobalTheory.T.telescoping_coordinate_difference (HermLine J) (e + 1) (II K J P (e + 1)) _ _).symm

theorem replace : Replace := by
  intro _ II hII K _ J _ P B e a b R Θ L s nb mb Wb σ _ A M m n f g w C hab hP hΘ hΘp hL hs hsnc hle hA hM hw hw0
  have h := replace_gen hII hab R hP hΘ hΘp hL hs hsnc hle A M m (Fin.append (fun _ : Fin a => m) n)
    (fun k => (k : ℕ) < a) (fun k => by
      refine Fin.addCases (fun k _ => ?_) (fun k hk => ?_) k
      · simp
      · simp at hk) hA hM hw hw0
  refine h.congr fun t => ?_
  congr 2
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

end LevelTowerAlt.Comparison₂
end
end

section
open MeasureTheory Metric Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (Mollifier molli coordDiv)

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem molli_le_of_le {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : ReciprocityTheory.AnForm.A.IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, φ y ≤ c) : molli ρ t φ z ≤ c := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled t y * c := by
        refine integral_mono (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z)
          ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _) fun y => ?_
        by_cases hy : ρ.scaled t y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
        have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
        rw [indicator_of_mem hmem]
        exact hc _ hmem
    _ = c := by rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem neBot_Yo (R : RegChartData A) (x : X) : (𝓝[R.Yo] x).NeBot := by
  obtain ⟨k, hk⟩ := R.cover x
  have hs := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hne := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S k) (R.chart k).open_target ((R.chart k).map_source hs)
  have ht : Tendsto (R.chart k).symm (𝓝[(R.chart k).target \ coordDiv (R.S k)] (R.chart k x)) (𝓝[R.Yo] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((R.chart k).continuousAt_symm ((R.chart k).map_source hs)).tendsto
      rw [(R.chart k).left_inv hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [R.mem_Yo k _ ((R.chart k).map_target hy.1), (R.chart k).right_inv hy.1]
      exact hy.2
  exact ht.neBot

theorem phReg_le [CompactSpace X] [T2Space X] (R : RegChartData A) (ρ : Mollifier D) (Kt : ℝ → ℝ)
    (hK : Tendsto Kt (𝓝[>] 0) atTop) {V K' : Set X} {g : X → ℝ} (hV : IsOpen V) (hg : ContinuousOn g V)
    (hph : ∀ x ∈ V ∩ R.Yo, g x = R.ph x) (hK'V : K' ⊆ V) (hK' : IsCompact K') (j : Fin R.N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K', x ∈ R.mid j → R.phReg ρ (Kt t) t j x ≤ g x + ε := by
  obtain ⟨δ, B, hδ, hT⟩ := TruncPsh.proof X D A R
  obtain ⟨U, hU, -, hUb, hUp⟩ := hT j
  set L := R.chart j '' (K' ∩ closure (R.mid j)) with hL
  have hsub : K' ∩ closure (R.mid j) ⊆ (R.chart j).source := fun x hx => R.closure_mid j hx.2
  have hLc : IsCompact L := (hK'.inter_right isClosed_closure).image_of_continuousOn ((R.chart j).continuousOn.mono hsub)
  set O := (R.chart j).target ∩ (R.chart j).symm ⁻¹' V with hO
  have hOo : IsOpen O := (R.chart j).isOpen_inter_preimage_symm hV
  have hLO : L ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(R.chart j).map_source (hsub hx), ?_⟩
    show (R.chart j).symm _ ∈ V
    rw [(R.chart j).left_inv (hsub hx)]
    exact hK'V hx.1
  let F : (Fin D → ℂ) → ℝ := fun y => R.q j y + g ((R.chart j).symm y)
  have hF : ContinuousOn F O := ((R.q_smooth j).continuousOn.mono inter_subset_left).add
    (hg.comp ((R.chart j).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2)
  obtain ⟨η, hη, hηO⟩ := hLc.exists_cthickening_subset_open hOo hLO
  obtain ⟨d, hd, hdF⟩ := Metric.uniformContinuousOn_iff.1
    ((hLc.cthickening (r := η)).uniformContinuousOn_of_continuous (hF.mono hηO)) ε hε
  obtain ⟨M, hM⟩ := hLc.exists_bound_of_continuousOn (hF.mono hLO)
  have hsm : ∀ {a : ℝ}, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun ha =>
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ha)
  filter_upwards [self_mem_nhdsWithin, hsm hδ, hsm (half_pos hη), hsm (half_pos hd), hK.eventually_ge_atTop M]
    with t ht t1 t2 t3 t4 x hx hxm
  have ht0 : (0 : ℝ) < t := ht
  have hxL : R.chart j x ∈ L := ⟨x, ⟨hx, subset_closure hxm⟩, rfl⟩
  have hxs := hsub ⟨hx, subset_closure hxm⟩
  have hFx : F (R.chart j x) = R.q j (R.chart j x) + g x := by simp only [F, (R.chart j).left_inv hxs]
  have h1 : molli ρ t (R.trunc (Kt t) j) (R.chart j x) ≤ F (R.chart j x) + ε := by
    refine molli_le_of_le ρ hU (hUp _).1 ht0 ((closedBall_subset_closedBall t1.le).trans (hUb x hxm)) fun y hy => ?_
    have hyx : dist y (R.chart j x) ≤ t := hy
    have hyO : y ∈ O := hηO (mem_cthickening_of_dist_le y _ _ _ hxL (by linarith))
    refine TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t hyO.1 ht0 fun y' hy' hy't hy'S => ?_
    have h2 : dist y' (R.chart j x) < 2 * t := by
      have := dist_triangle y' y (R.chart j x)
      have h3 : dist y' y < t := hy'
      linarith
    have hy'c : y' ∈ cthickening η L := mem_cthickening_of_dist_le y' _ _ _ hxL (by linarith)
    have h4 := hdF y' hy'c _ (self_subset_cthickening L hxL) (by linarith)
    have h5 : R.u j y' = F y' := by
      show R.q j y' + R.ph _ = R.q j y' + g _
      rw [hph _ ⟨(hηO hy'c).2, by
        rw [R.mem_Yo j _ ((R.chart j).map_target hy't), (R.chart j).right_inv hy't]
        exact hy'S⟩]
    rw [Real.dist_eq] at h4
    have h6 := hM _ hxL
    rw [Real.norm_eq_abs] at h6
    refine max_le ?_ ?_
    · rw [h5]
      linarith [(abs_lt.1 h4).2]
    · linarith [(abs_le.1 h6).1]
  show molli ρ t (R.trunc (Kt t) j) (R.chart j x) - R.q j (R.chart j x) ≤ _
  linarith

theorem regUnif : RegUnif := by
  intro K _ J _ P n M Xo B S V g hS hV hg hph
  obtain ⟨C₀, t₀, ht₀, hb⟩ := ChartMollifiedBounds.proof TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  have h3 : ∀ t x, S.regWeight t x = S.R.glue
      (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := fun _ _ => rfl
  have hup : ∀ t, 0 < t → ∀ x c, (∀ j, x ∈ S.R.mid j → S.R.phReg S.ρ (S.K t) t j x ≤ c) →
      S.regWeight t x ≤ c + S.e1 t := by
    intro t ht0 x c h
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    rw [h3]
    refine LogLogRegularisation.glue_le S.R.toPotentialCharts _ hε0 fun j hj => ?_
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t) (S.cutoff.bounds j x hj).2
    have := h j hj
    show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ c
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C₀ + 1) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x := by
    filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀), hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := hup t ht0 x C₀ fun j hj => ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
      linarith
    · have hlow : ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x := by
        intro x hx
        obtain ⟨k, hk⟩ := S.R.cover x
        have hkm := S.R.inner_subset_mid k hk
        have a1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
        have a2 := LogLogRegularisation.le_glue S.R.toPotentialCharts
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
        simp only [S.cutoff.eq_zero k x hk, mul_zero, add_zero] at a2
        rw [h3]
        linarith
      have := neBot_Yo S.R x
      have c1 : Tendsto g (𝓝[S.R.Yo] x) (𝓝 (g x)) := (hg.continuousAt (hV.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
      have c2 : Tendsto (S.regWeight t) (𝓝[S.R.Yo] x) (𝓝 (S.regWeight t x)) :=
        ((GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.continuous_of_smooth M.atlas hsm.1).tendsto x).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto c1 c2 ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy hyV
      rw [hph y ⟨hyV, hy⟩]
      exact hlow y hy
  refine ⟨⟨C₀ + 1, h1⟩, fun K' hK'V hK' => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  filter_upwards [h1, self_mem_nhdsWithin, hS.e1_tendsto_zero.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_all.2 fun j => phReg_le S.R S.ρ S.K hS.K_tendsto hV hg hph hK'V hK' j (half_pos hε)] with t a1 ht a2 a3 x hx
  have a4 := hup t ht x (g x + ε / 2) fun j hj => a3 j x hx hj
  have a5 := a1.2 x (hK'V hx)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end LevelTowerAlt.Comparison₂
end
end

section
open Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem smul_mem {P : Ideal (MRing J)} {n : ℕ} (hP : IsArithVar P n) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts P :=
  mem_mcPts_of_sameOrbit hP.2.1.2.1 ⟨c, hc, rfl⟩ hz

theorem proj_eq {P : Ideal (MRing J)} {n : ℕ} (M : CxModel P n) {z z' : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) (hz' : z' ∈ mcPts P) :
    M.proj z' = M.proj z ↔ SameOrbit z z' := M.fibre z' hz' z hz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W)

theorem bd_orbit {z z' : (Σ k, J k) → ℂ} (h : SameOrbit z z') (hz : z' ∈ D.Bd) : z ∈ D.Bd := by
  obtain ⟨c, hc, rfl⟩ := h
  exact D.bd_torus _ hz c hc

theorem exists_read {z₀ : (Σ k, J k) → ℂ} (hz₀ : z₀ ∈ mcPts (mCoordIdeal D.y)) :
    ∃ (a : Fin D.nCharts) (T : ((Σ k, J k) → ℂ) → Fin D.n → ℂ), AnalyticAt ℂ T z₀ ∧ T z₀ ∈ Metric.ball 0 1 ∧
      ∀ᶠ z in 𝓝 z₀, z ∈ mcPts (mCoordIdeal D.y) → T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) := by
  obtain ⟨a, t₀, ht₀, c, hc, rfl⟩ := D.chart_cover z₀ hz₀
  have hb : t₀ ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := mem_ball_zero_iff.2 (ht₀.trans_lt (by norm_num))
  obtain ⟨V, T, hV, hm, hT, h0, h⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a t₀ hb
  have hs : ∀ z, AnalyticAt ℂ (torusSmul (ι := J) fun k => (c k)⁻¹) z := fun z =>
    analyticAt_pi_iff.2 fun p => analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) p).analyticAt z)
  have e0 : torusSmul (fun k => (c k)⁻¹) (torusSmul c ((D.chart a).γ t₀)) = (D.chart a).γ t₀ :=
    funext fun p => inv_mul_cancel_left₀ (hc _) _
  refine ⟨a, T ∘ torusSmul fun k => (c k)⁻¹, AnalyticAt.comp (by rw [e0]; exact hT _ hm) (hs _), ?_, ?_⟩
  · exact Set.mem_of_eq_of_mem ((congrArg T e0).trans h0) hb
  · filter_upwards [(hs _).continuousAt.eventually_mem (hV.mem_nhds (by rwa [e0]))] with z hz hzP
    obtain ⟨h1, c', hc', h2⟩ := h _ ⟨hz, smul_mem D.arith hzP fun k => inv_ne_zero (hc k)⟩
    refine ⟨h1, fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => ?_⟩
    have := congrFun h2 p
    simp only [torusSmul] at this
    exact ((mul_inv_cancel_left₀ (hc _) _).symm.trans (congrArg _ this)).trans (mul_assoc _ _ _).symm

theorem contOn_Xo (Hd : HodgeData D) (ref : HermLine J) (ha : (muLine Hd).a = ref.a) (hr : IsSmoothHerm ref) :
    ContinuousOn (fun z => Real.log ((muLine Hd).h z) - Real.log (ref.h z)) D.Xo := by
  intro z₀ hz₀
  obtain ⟨a, T, hT, hb, h⟩ := exists_read D hz₀.1
  have h0 := h.self_of_nhds hz₀.1
  have hoff : T z₀ ∈ offBd D a := ⟨hb, fun hm => hz₀.2 (bd_orbit D h0.2 hm)⟩
  have h1 : ContinuousAt (fun t => phMu Hd ((D.chart a).γ t)) (T z₀) :=
    ((GlobalTheory.T.hodge_potential_smooth_off_boundary K J II Ψ Ω W D Hd).1 a).continuousOn.continuousAt ((SncPiece.isOpen_offBd D a).mem_nhds hoff)
  have hγ := ((D.chart a).analytic _ hb).continuousAt
  have hm := (D.chart a).mem _ hb
  have ho : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : ContinuousAt (fun t => Real.log (ref.h ((D.chart a).γ t))) (T z₀) :=
    (ContinuousAt.comp (f := (D.chart a).γ) (hr.continuousOn.continuousAt (ho.mem_nhds hm.1)) hγ).log (ref.pos _ hm.1).ne'
  have h3 := (ContinuousAt.comp (f := T) (h1.sub h2) hT.continuousAt).continuousWithinAt (s := D.Xo)
  have key : ∀ z, T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) →
      Real.log ((muLine Hd).h z) - Real.log (ref.h z) =
        ((fun t => phMu Hd ((D.chart a).γ t) - Real.log (ref.h ((D.chart a).γ t))) ∘ T) z := fun z hz =>
    log_diff_orbit ha ((D.chart a).mem _ hz.1).1 hz.2
  refine h3.congr_of_eventuallyEq ?_ (key _ h0)
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hz' using key z (hz hz'.1)

theorem exists_ext (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) :
    ∃ (V : Set M.Xc) (g : M.Xc → ℝ), IsOpen V ∧ ContinuousOn g V ∧ (∀ x ∈ V ∩ S.R.Yo, g x = S.R.ph x) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), (z ∉ D.Bd → M.proj z ∈ V) ∧
        g (M.proj z) = Real.log ((muLine Hd).h z) - Real.log (S.ref.h z) := by
  choose r hr hr' using M.surj
  have hg : ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muLine Hd).h (r (M.proj z))) - Real.log (S.ref.h (r (M.proj z))) =
      Real.log ((muLine Hd).h z) - Real.log (S.ref.h z) := fun z hz =>
    log_diff_orbit S.ref_deg.symm hz.1 ((proj_eq M (hr _) hz).1 (hr' _).symm)
  have hV : ∀ z ∈ mcPts (mCoordIdeal D.y), r (M.proj z) ∉ D.Bd ↔ z ∉ D.Bd := fun z hz =>
    not_congr ⟨bd_orbit D ((proj_eq M hz (hr _)).1 (hr' _)), bd_orbit D ((proj_eq M (hr _) hz).1 (hr' _).symm)⟩
  have key : ∀ x, r x ∉ D.Bd → ∃ s : M.Xc → (Σ k, J k) → ℂ, ContinuousAt s x ∧
      ∀ᶠ y in 𝓝 x, s y ∈ D.Xo ∧ M.proj (s y) = y := by
    intro x hx
    obtain ⟨U, hU, hxU, s, hs, hs'⟩ := M.sections x
    have hc : ContinuousAt s x := continuousAt_pi.2 fun p => holo_cont (hs' p) hxU
    refine ⟨s, hc, ?_⟩
    obtain ⟨F, hF, hF'⟩ := isClosed_induced_iff.1 D.bd_closed
    have hm : ∀ z ∈ mcPts (mCoordIdeal D.y), z ∈ F ↔ z ∈ D.Bd := fun z hz => Set.ext_iff.1 hF' ⟨z, hz⟩
    have h1 : s x ∈ Fᶜ := fun h => (hV _ (hs x hxU).1).1 (by rwa [(hs x hxU).2]) ((hm _ (hs x hxU).1).1 h)
    filter_upwards [hU.mem_nhds hxU, hc.eventually_mem (hF.isOpen_compl.mem_nhds h1)] with y hy hy'
    exact ⟨⟨(hs y hy).1, fun h => hy' ((hm _ (hs y hy).1).2 h)⟩, (hs y hy).2⟩
  refine ⟨{x | r x ∉ D.Bd}, fun x => Real.log ((muLine Hd).h (r x)) - Real.log (S.ref.h (r x)), ?_, ?_, ?_,
    fun z hz => ⟨(hV z hz).2, hg z hz⟩⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨s, -, hs⟩ := key x hx
    filter_upwards [hs] with y hy
    have := (hV _ hy.1.1).2 hy.1.2
    rwa [hy.2] at this
  · intro x hx
    obtain ⟨s, hc, hs⟩ := key x hx
    have h1 := (contOn_Xo D Hd S.ref S.ref_deg.symm S.ref_smooth _ hs.self_of_nhds.1).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hc.tendsto, hs.mono fun y hy => hy.1⟩)
    have h2 : ∀ y, s y ∈ D.Xo ∧ M.proj (s y) = y → Real.log ((muLine Hd).h (s y)) - Real.log (S.ref.h (s y)) =
        Real.log ((muLine Hd).h (r y)) - Real.log (S.ref.h (r y)) := fun y hy => by
      rw [← hg _ hy.1.1, hy.2]
    rw [h2 x hs.self_of_nhds] at h1
    exact ContinuousAt.continuousWithinAt (h1.congr' (hs.mono fun y hy => h2 y hy))
  · intro x hx
    have := S.ph_eq (r x) ⟨⟨hr x, hx.1⟩, hr x⟩ (by rw [hr']; exact hx.2)
    rw [hr'] at this
    exact this.symm

theorem holoMap_proj (M : XModel D) {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : X → Set X)
    (hU : ∀ x, IsOpen (U x) ∧ x ∈ U x) (lv : X → X → (Σ k, J k) → ℂ) (hl : ∀ x p, A.HoloOn (U x) fun y => lv x y p)
    (hm : ∀ x, ∀ y ∈ U x, lv x y ∈ mcPts (mCoordIdeal D.y))
    (ho : ∀ x, ∀ y ∈ U x, M.proj (lv y y) = M.proj (lv x y)) : HoloMap A M.atlas fun x => M.proj (lv x x) := by
  have hc : ∀ x, ContinuousAt (lv x) x := fun x => continuousAt_pi.2 fun p => holo_cont (hl x p) (hU x).2
  have hn : ∀ x, U x ∈ 𝓝 x := fun x => (hU x).1.mem_nhds (hU x).2
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k y hy => ?_⟩
  · have h1 := (M.cont _ (hm x x (hU x).2)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨(hc x).tendsto, Filter.mem_of_superset (hn x) (hm x)⟩)
    exact h1.congr' (Filter.mem_of_superset (hn x) fun y hy => (ho x y hy).symm)
  · obtain ⟨x, hx⟩ : ∃ x, x = (A.chart j).symm y := ⟨_, rfl⟩
    obtain ⟨a, T, hT, hb, h⟩ := exists_read D (hm x x (hU x).2)
    have h0 := h.self_of_nhds (hm x x (hU x).2)
    have hp : ∀ z ∈ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) →
        M.proj ((D.chart a).γ (T z)) = M.proj z := fun z hz h' => (proj_eq M hz ((D.chart a).mem _ h'.1)).2 h'.2
    have h1 := (GlobalTheory.T.projection_of_chart_analytic K J II Ψ Ω W D M a k _ hb (by
      rw [hp _ (hm x x (hU x).2) h0, hx]; exact hy.2)).1
    have h2 : AnalyticAt ℂ (fun y' => lv x ((A.chart j).symm y')) y :=
      analyticAt_pi_iff.2 fun p => hl x p j y ⟨hy.1, by rw [Set.mem_preimage, ← hx]; exact (hU x).2⟩
    have h3 : AnalyticAt ℂ (T ∘ fun y' => lv x ((A.chart j).symm y')) y := AnalyticAt.comp (by rwa [← hx]) h2
    have h4 := AnalyticAt.comp (f := T ∘ fun y' => lv x ((A.chart j).symm y')) (x := y)
      (by rw [Function.comp_apply, ← hx]; exact h1) h3
    refine h4.congr ?_
    have hs : Tendsto (A.chart j).symm (𝓝 y) (𝓝 x) := hx ▸ (A.chart j).continuousAt_symm hy.1
    filter_upwards [hs.eventually (hn x), hs.eventually ((hc x).eventually h)] with y' h5 h6
    simp only [Function.comp_apply]
    rw [hp _ (hm x _ h5) (h6 (hm x _ h5)), ho x _ h5]

theorem baseSide (hU : RegUnif) : BaseSide := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B K' _ J' _ P' B' e R κ v Θ Mt hS hv hP hΘ hΘp hMt
  classical
  have hpl := GlobalTheory.T.block_pullback_herm_line K J K' J' κ v hv
  let lv : R.X → R.X → (Σ k, J k) → ℂ := fun x y p => R.lift x y (v p)
  have hm : ∀ x, ∀ y ∈ R.U x, lv x y ∈ mcPts (mCoordIdeal D.y) := fun x y hy => hP ▸ hpl.2.2.1 P' _ (R.mem x y hy)
  have ho : ∀ x, ∀ y ∈ R.U x, M.proj (lv y y) = M.proj (lv x y) := by
    intro x y hy
    obtain ⟨c, hc, h⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
    refine (proj_eq M (hm x y hy) (hm y y (R.mem_U y))).2 ⟨fun k => c (κ k), fun k => hc _, funext fun p => ?_⟩
    simp only [lv, h, hv.2.2.1]
  have hπ := holoMap_proj D M R.A R.U (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) lv (fun x p => R.holo x _) hm ho
  set π : R.X → M.Xc := fun x => M.proj (lv x x) with hπd
  have hSB : ∀ p : D.SB B, (p : ℕ) ∈ D.S := fun p => (Finset.mem_filter.1 p.2).1
  choose Ap hAa hAs hAc hAh using fun p : D.SB B => (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (hSB p)).1
  let N₀ : HermLine J := Top.combLine (fun o : Option (D.SB B) => o.elim S.ref Ap) fun _ => 1
  have hN : IsSmoothHerm N₀ := (GlobalTheory.T.hermitian_combination_smooth_conj K J _ _ _).1 fun o => by
    cases o
    exacts [S.ref_smooth, hAs _]
  have hNa : N₀.a = muTwDeg Hd B := by
    simp only [N₀, Top.combLine, Fintype.sum_option, one_smul, Option.elim, hAa, S.ref_deg, muTwDeg]
    rw [Finset.sum_coe_sort (D.SB B) D.vdeg]
    rfl
  have hNh : ∀ z ∈ mcPts (mCoordIdeal D.y),
      Real.log (N₀.h z) = Real.log (S.ref.h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
    intro z hz
    simp only [N₀, Top.combLine, Fintype.prod_option, zpow_one, Option.elim]
    rw [Real.log_mul (S.ref.pos z hz.1).ne' (Finset.prod_ne_zero_iff.2 fun p _ => ((Ap p).pos z hz.1).ne'),
      Real.log_prod fun p _ => ((Ap p).pos z hz.1).ne', ← Finset.sum_coe_sort (D.SB B)]
    simp only [hAh _ z hz]
  obtain ⟨ref, href⟩ := (hpl.1 N₀).exists
  obtain ⟨V, g, hV, hg, hgS, hgz⟩ := exists_ext D Hd M S
  obtain ⟨⟨C₁, hC₁⟩, hun⟩ := hU K J _ _ M D.Xo _ S V g hS hV hg hgS
  obtain ⟨Θ', hΘ', hΘ'p, -⟩ := GlobalTheory.T.exists_positive_potential_dominating K J II Ψ Ω W D M S.R.th S.R.th_pot
  obtain ⟨-, ⟨C₂, hC₂⟩, hw⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K J _ _ M D.Xo _ S Θ' hS hΘ' hΘ'p
  obtain ⟨C₃, hC₃⟩ := exists_psh_pull hπ hΘ hΘp (pot_rsmul hΘ' 1)
  have hreg := GlobalTheory.T.regularized_hodge_metric_smooth K J II Ψ Ω W D Hd M S B hS
  have hloc : ∀ x, LocRe R.A (fun y => Real.log (N₀.h (lv x y)) - S.R.th.φ (π x) (π y)) x := by
    intro x
    obtain ⟨U, hUo, hxU, -, s, hs, hs', G, hG, hG'⟩ := S.th_ref (π x) (π x) (S.R.th.mem_U _)
    have h1 : LocRe M.atlas (fun y => S.R.th.φ (π x) y - Real.log (S.ref.h (s y))) (π x) := ⟨U, hUo, hxU, G, hG, hG'⟩
    have h2 : LocRe M.atlas (fun y => ∑ p ∈ D.SB B, Real.log (D.vertFactor p (s y))) (π x) := LocRe.sum _ fun p hp => by
      obtain ⟨V', a1, a2, -, a3⟩ := GlobalTheory.T.local_section_vertical_factor II Ψ K J Ω W D p M U s (hSB ⟨p, hp⟩) hUo (fun y hy => (hs y hy).1) hs' _ hxU
      exact ⟨V', a1, a2, a3⟩
    have hO : IsOpen (R.U x ∩ π ⁻¹' U) := (R.isOpen_U x).inter (hUo.preimage hπ.1)
    have h3 := locRe_orbit (A := R.A) N₀ hO (s := lv x) (s' := fun y => s (π y))
      (fun p => holo_mono (R.holo x _) Set.inter_subset_left) (fun p => holo_mono (holo_comp (hs' p) hπ) Set.inter_subset_right)
      (fun y hy => (hs _ hy.2).1.1)
      (fun y hy => (proj_eq M (hm x y hy.1) (hs _ hy.2).1).1 ((hs _ hy.2).2.trans (ho x y hy.1))) ⟨R.mem_U x, hxU⟩
    refine ((h3.add (h2.comp hπ)).add ((h1.comp hπ).mul (-1))).congr ?_
    filter_upwards [hO.mem_nhds ⟨R.mem_U x, hxU⟩] with y hy
    rw [hNh _ (hs _ hy.2).1]
    ring
  have hval : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, ∀ y ∈ R.U x,
      Real.log ((Mt t).h (R.lift x y)) = Real.log (N₀.h (lv x y)) + S.regWeight t (π y) := by
    filter_upwards [hreg] with t ht x y hy
    rw [(hMt t).2, ht.2.2 _ (hm x y hy), hNh _ (hm x y hy), ← ho x y hy]
    ring
  have hmu : ∀ x, Real.log ((muVert Hd B).h (lv x x)) = Real.log (N₀.h (lv x x)) + g (π x) := by
    intro x
    have hx := hm x x (R.mem_U x)
    rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B _ hx, hNh _ hx, (hgz _ hx).2]
    ring
  refine ⟨ref, max C₁ C₃, hpl.2.1 _ _ href hN, ?_, fun K₀ hK₀ hKc => ?_⟩
  · filter_upwards [hreg, hC₁, hC₂, hw 1 one_pos, hval] with t h1 h2 h3 h4 h5
    have hs := hpl.2.1 _ _ (hMt t) h1.1
    have hp := isPotential_potOf R hs
    refine ⟨hs, by rw [(hMt t).1, href.1, h1.2.1, hNa], ?_, fun x => ?_, fun x hx => ?_⟩
    · have h6 := hC₃ _ _ hp (isPotentialAdd _ _ _ S.R.th_pot (isPotential_ofFun _ _ h3.1)) h4 fun x => (hloc x).congr (by
        filter_upwards [(R.isOpen_U x).mem_nhds (R.mem_U x)] with y hy
        show Real.log ((Mt t).h (R.lift x y)) - (S.R.th.φ (π x) (π y) + S.regWeight t (π y)) = _
        rw [h5 x y hy]
        ring)
      have h7 := isPshAdd R.A _ _ (isPotentialAdd _ _ _ hp (pot_rsmul hΘ C₃)) (pot_rsmul hΘ (max C₁ C₃ - C₃)) h6
        (isPshRsmul R.A _ _ (sub_nonneg.2 (le_max_right _ _)) hΘ (TailBoundAlt.isPsh_of_isPosPot _ _ hΘp))
      refine TailBoundAlt.isPsh_congr R.A _ _ h7 (fun x y hy => ⟨hy, hy.2⟩) ?_
      funext x y
      show _ + _ * Θ.φ x y = _ + C₃ * Θ.φ x y + _ * Θ.φ x y
      ring
    · rw [h5 x x (R.mem_U x), href.2, add_sub_cancel_left]
      exact (h2.1 _).trans (le_max_left _ _)
    · rw [h5 x x (R.mem_U x), hmu]
      exact add_le_add le_rfl (h2.2 _ ((hgz _ (hm x x (R.mem_U x))).1 hx))
  · have h1 := hun (π '' K₀) (by
      rintro _ ⟨x, hx, rfl⟩
      exact (hgz _ (hm x x (R.mem_U x))).1 (hK₀ hx)) (hKc.image hπ.1)
    rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
    intro ε hε
    filter_upwards [h1 ε hε, hval] with t h2 h3 x hx
    have := h2 _ ⟨x, hx, rfl⟩
    rw [h3 x x (R.mem_U x), hmu, Real.dist_eq] at *
    rwa [show (0 : ℝ) - (Real.log (N₀.h (lv x x)) + S.regWeight t (π x) - (Real.log (N₀.h (lv x x)) + g (π x))) =
      g (π x) - S.regWeight t (π x) by ring]

end LevelTowerAlt.Comparison₂
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem LevelTowerAlt.good_origin_tower_height : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) :=
  LevelTowerAlt.Comparison₂.tie_of (LevelTowerAlt.Comparison₂.common LevelTowerAlt.Comparison₂.levelFree LevelTowerAlt.Comparison₂.muHodge) LevelTowerAlt.Comparison₂.replace (LevelTowerAlt.Comparison₂.baseSide LevelTowerAlt.Comparison₂.regUnif)
end
