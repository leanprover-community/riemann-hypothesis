import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolution
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushforwardRegularIdeal
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependent
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierOpen
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionBigBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardIdealRegularity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmple

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.MultIdealExists

theorem isProper_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem exists_isMultIdeal : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B hη hm hres
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : IsProper (s ≫ p) := isProper_of_isProjOver' hres.proj
  haveI : IsProper p := isProper_of_isProjOver' hp
  haveI : QuasiCompact s := QuasiCompact.of_comp s p
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hres.proj (pullCart s G - m • K) m
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_pushforward_regular_ideal X Y s (-F)
  exact ⟨J, (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hη hm hres hF J).2 hJ⟩

end GlobalTheory.MultIdealExists
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_multiplier_ideal : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J := by
  atlas_forward_decl _root_.GlobalTheory.MultIdealExists.exists_isMultIdeal
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem inMultAt_one_iff_kltAt {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) (y : X) : InMultAt p n η m G y 1 ↔ KltAt p n Δ y := by
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  have hkey : ∀ g, G.IsEqn y g → (KltAt p n Δ y ↔ ∀ (E : DivOver p), E.Through y → -1 < discrep E η m g) :=
    fun g hg => IsLogEqn.kltAt_iff hn hM.ne_zero hM.pos (hM.eqn y g hg)
  constructor
  · intro h
    obtain ⟨g, hg⟩ := G.exists_isEqn y
    rw [hkey g hg]
    intro E hE
    have h1 := h g hg E hE
    simpa [DivOver.ord_one] using h1
  · intro h g hg E hE
    have h1 := (hkey g hg).1 h E hE
    simpa [DivOver.ord_one] using h1

theorem one_mem_ideal_iff {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) {J : X.IdealSheafData} (hJ : IsMultIdeal p n η m G J)
    (U : X.affineOpens) : (1 : Γ(X, U.1)) ∈ J.ideal U ↔ ∀ y ∈ U.1, KltAt p n Δ y := by
  rw [hJ U 1]
  constructor
  · intro h y hy
    exact (inMultAt_one_iff_kltAt hp hn hM y).1 (h y hy 1 (by simp))
  · intro h y hy u hu
    have : u = 1 := Units.ext (by simpa using hu)
    subst this
    exact (inMultAt_one_iff_kltAt hp hn hM y).2 (h y hy)

theorem mem_support_multIdeal_iff : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro k _ _ X _ _ _ p n hp hn Δ η m G Y _ _ s _ K B hM hR J hJ x
  have hO := (isOpen_kltAt_and_lcAt_of_isLogRes k X p n hp hn Δ η m G Y s K B hM hR).1
  have hb : ∀ {U : X.Opens} {z : X}, z ∈ U → ∃ U' ∈ X.affineOpens, z ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  constructor
  · intro hx hk
    obtain ⟨V, hV, hxV, hVO⟩ := hb (show x ∈ (⟨_, hO⟩ : X.Opens) from hk)
    have h1 : (1 : Γ(X, V)) ∈ J.ideal ⟨V, hV⟩ :=
      (one_mem_ideal_iff hp hn hM hJ ⟨V, hV⟩).2 (fun y hy => hVO hy)
    have h2 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h2
    exact h2 1 h1 (by rw [Scheme.basicOpen_one]; exact hxV)
  · intro hnk
    by_contra hx
    obtain ⟨V, hV, hxV, -⟩ := hb (show x ∈ (⊤ : X.Opens) from trivial)
    have h2 : ¬ x ∈ X.zeroLocus (J.ideal ⟨V, hV⟩ : Set Γ(X, V)) := fun h =>
      hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).2 h)
    rw [Scheme.mem_zeroLocus_iff] at h2
    push_neg at h2
    obtain ⟨f, hf, hfx⟩ := h2
    rw [Scheme.mem_basicOpen X f x hxV] at hfx
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hgen : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV f) =
        X.germToFunctionField V f := by simp
    have hunit : IsUnit (X.germToFunctionField V f) := by
      rw [← hgen]
      exact hfx.map _
    have hmem := (hJ ⟨V, hV⟩ f).1 hf x hxV hunit.unit (by rw [IsUnit.unit_spec]; rfl)
    apply hnk
    rw [← inMultAt_one_iff_kltAt hp hn hM x]
    intro g hg E hE
    have h3 := hmem g hg E hE
    have h4 : E.ord hunit.unit = 0 :=
      DivOver.ord_eq_zero_of_unitAt hE _ ⟨_, hfx, by rw [IsUnit.unit_spec]; exact hgen⟩
    simpa [h4, DivOver.ord_one] using h3

end GlobalTheory.Discrepancy
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_log_resolution : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  atlas_forward_decl _root_.GlobalTheory.Discrepancy.mem_support_multIdeal_iff
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isMultIdeal_support_iff_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), IsLogMult p n Δ η m G → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J ∧ ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ η m G hL
  have hne : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    have hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, hYi, s, hsd, K, B, hR, -⟩ :=
    LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne
  haveI := hYi
  haveI := hsd
  haveI := hR.smooth
  have hsm : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)
  obtain ⟨-, -, hYn⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm
  haveI := hYn
  obtain ⟨J, hJ⟩ := MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR
  exact ⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩

end GlobalTheory.Discrepancy
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem regAt_of_regularAt_neg_roundDown : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  intro k _ _ X _ _ _ p n hproj _ Δ η m G Y _ _ s _ K B F hΔ hmult hres hF x f hf
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  by_cases hf0 : f = 0
  · subst hf0; exact regAt_zero x
  refine regAt_of_forall_coheight_eq_one fun z hzx hz1 => ?_
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hz1
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
  obtain ⟨w, rfl, hE'⟩ := GlobalTheory.T.divisor_point_proper_lift k X Y p s hres.bir inferInstance E' E hE'E _ hE
  obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
  have hg' := isEqn_pullCart s hg
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hmult.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  have hd := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m
    hmult.pos hres.div E' w (fnPull s g) hE' hg'
  have hd2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
    simp only [discrep]
    rw [GlobalTheory.T.form_order_birational_pullback k X Y p s hres.bir E' E hE'E n η hmult.ne_zero,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E g]
  have hd3 := (hmult.eqn _ g hg).discrep_eq_neg hmult.pos (specializes_refl _) hE
  have hm : (0 : ℚ) < m := by exact_mod_cast hmult.pos
  have hnn : 0 ≤ (pullCart s G - m • K).mult w := by
    have e : ((pullCart s G - m • K).mult w : ℚ) / m = Δ (s w) := by
      rw [← hd2, hd] at hd3
      rw [neg_div] at hd3
      exact neg_injective hd3
    have h0 : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) / m := e ▸ hΔ (s w)
    have := (div_nonneg_iff.1 h0)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.2 hm)
  have hFn : 0 ≤ F.mult w := by
    rw [hF]; exact Int.ediv_nonneg hnn (by exact_mod_cast hmult.pos.le)
  obtain ⟨h, hh⟩ := F.exists_isEqn w
  have hreg := (hh.neg.regularAt_iff).1 (hf w hzx)
  set u : X.functionFieldˣ := Units.mk0 f hf0 with hu
  have hv : ((fnPull s u * h⁻¹ : Y.functionFieldˣ) : Y.functionField) =
      functionFieldMap s f * ((h⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    simp [hu, fnPull]
  have h1 : 0 ≤ E'.ord (fnPull s u * h⁻¹) :=
    (E'.ord_nonneg_iff _).2 (hv ▸ (hE' _).2 hreg)
  rw [E'.ord_mul, E'.ord_inv, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E u, hE'.ord_eq h,
    ← hh.mult_eq] at h1
  have h2 : 0 ≤ E.ord u := by omega
  exact (hE f).1 ((E.ord_nonneg_iff u).1 h2)

end GlobalTheory.Discrepancy
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_effective_boundary : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  atlas_forward_decl _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem nadel_of_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro k _ _ X _ _ _ p n hp hdim Δ η m G Y _ _ s _ K B hΔ hLM hR N M T hN hMlb r hT hr hcls hMnef
    a Fd A hA hFd J hJ i hi
  haveI := hR.smooth
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hR.proj (pullCart s G - m • K) m
  have hJ' := (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF J).1 hJ
  obtain ⟨e⟩ := GlobalTheory.T.pushforward_ideal_regularity X Y s hR.bir (-F) J hJ'
    (GlobalTheory.T.multiplier_ideal_effective_boundary k X p n hp hdim Δ η m G Y s K B F hΔ hLM hR hF)
  have hv := (GlobalTheory.T.multiplier_vanishing_nef_twist_ample k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF N M T hN hMlb r hT hr
    hcls hMnef a Fd A hA hFd).1 i hi
  exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ i ((twistFunctor N).mapIso e)).symm.toEquiv hv

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem GlobalTheory.nadelVanishing : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → (letI := algebraΓOfHom p; IsBig k M) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro hP k _ _ X _ _ _ p n hproj hdim Δ η m G hΔ hlm N M T hN hM r hT hr hcls hMnef hMbig J hJ i hi
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, _, s, _, K, B, hres, -, a, Fd, A, hA, hkod⟩ :=
    GlobalTheory.LogResBig.exists_logRes_smul_eq_ample_add_eff hP k X p n hproj hdim η m G hlm.ne_zero ⊥ hZ M hM hMbig
  haveI : IsLocallyNoetherian Y :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hres.smooth.smooth).2.2
  exact GlobalTheory.nadel_of_logRes k X p n hproj hdim Δ η m G Y s K B hΔ hlm hres N M T hN hM r hT hr hcls hMnef a Fd A hA hkod J hJ i hi
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem nadelVanishingPair_of_principalisation (hP : GlobalTheory.Published.Principalisation) :
    GlobalTheory.Published.NadelVanishingPair := by
  intro X _ _ _ p n hproj hdim N Δ m G r M₀ hN hΔ hm hlc hr hnef hbig hcurve
  letI := algebraΓOfHom p
  obtain ⟨η, hlm⟩ := hlc.exists_isLogMult hm
  obtain ⟨J, hJ, hsupp⟩ :=
    exists_isMultIdeal_support_iff_not_kltAt hP ℂ X p n hproj hdim Δ η m G hlm
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hM : M₀.IsLB := hnef.isLB
  have hG : (toLB G).IsLB := isLB_toLB G
  have hP1 : (lbPow N (m * r)).IsLB := isLB_lbPow hN _
  have hP2 : (lbPow (toLB G) r).IsLB := isLB_lbPow hG _
  have hP3 : (lbPow M₀ m).IsLB := isLB_lbPow hM _
  have hD2 : (dual (lbPow (toLB G) r)).IsLB := isLB_dual hP2
  have hD3 : (dual (lbPow M₀ m)).IsLB := isLB_dual hP3
  have hS : (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))).IsLB := isLB_tens hD2 hD3
  have hTl : (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))).IsLB :=
    isLB_tens hP1 hS
  have hclsS : cls _ hS = cls _ hD2 + cls _ hD3 := cls_tens hD2 hD3 hS
  have hclsT : cls _ hTl = cls _ hP1 + cls _ hS := cls_tens hP1 hS hTl
  have hT : IsNef ℂ (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))) := by
    refine ⟨hTl, fun Z hZ => ?_⟩
    have e1 := hZ.interNumRed_of_cls_eq_add hH hTl hP1 hS hclsT
    have e2 := hZ.interNumRed_of_cls_eq_add hH hS hD2 hD3 hclsS
    have e3 := hZ.interNumRed_dual (L := lbPow (toLB G) r) hH hP2
    have e4 := hZ.interNumRed_dual (L := lbPow M₀ m) hH hP3
    have e5 := hZ.interNumRed_lbPow hH hN (m * r)
    have e6 := hZ.interNumRed_lbPow hH hG r
    have e7 := hZ.interNumRed_lbPow hH hM m
    have hq := hcurve Z hZ
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    have hz : ((m : ℤ) * r) * interNumRed ℂ Z ![N] = r * interNumRed ℂ Z ![toLB G] + m * interNumRed ℂ Z ![M₀] := by
      have : ((m : ℚ) * r) * (interNumRed ℂ Z ![N] : ℚ) = r * (interNumRed ℂ Z ![toLB G] : ℚ) + m * (interNumRed ℂ Z ![M₀] : ℚ) := by
        rw [hq]
        field_simp
      exact_mod_cast this
    rw [e1, e2, e3, e4, e5, e6, e7]
    push_cast
    linarith
  have hcls : cls _ hT.isLB = (m * r) • cls N hN - r • toPic G - m • cls M₀ hM := by
    rw [hclsT, hclsS, cls_dual hP2 hD2, cls_dual hP3 hD3, cls_lbPow hN (m * r) hP1, cls_lbPow hG r hP2,
      cls_lbPow hM m hP3]
    have : cls (toLB G) hG = toPic G := rfl
    rw [this]
    abel
  exact ⟨J, hsupp, fun i hi =>
    GlobalTheory.nadelVanishing hP ℂ X p n hproj hdim Δ η m G hΔ.nonneg hlm N M₀ _ hN hM r hT hr hcls hnef hbig J hJ i hi⟩

end GlobalTheory.Discrepancy
end
