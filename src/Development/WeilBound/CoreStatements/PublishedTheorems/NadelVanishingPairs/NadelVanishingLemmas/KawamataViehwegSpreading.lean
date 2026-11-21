import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistDivisorRecursion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTopPartEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLatticeCohomologyVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelFiniteQuasicoherent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsEqChartForms
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAtSmulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemSpanFormsOfMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelUniqueInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionAtlasModP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleOpenRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubschemeClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomologyVanishingSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldToModPSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeToNumberField

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem descend_vanishing : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G hD hG e₀ h0
  have step : ∀ e, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G (e + 1)) a) b) →
      ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e) a) b := by
    intro e he a b hab
    obtain ⟨ρ, hρ, hGe⟩ := hG e
    refine hD (G e) ρ hρ a b ?_
    rw [← hGe]
    refine DI.hypZero_of_cechZero (extD X.functionField) _ (fun x => CechDR.dDR_dDR x) ?_ ?_ (a + b) ?_
    · intro q s t _ hst
      show latSec _ _ ≤ latSec _ _
      have hle : inter 𝒜.U t ≤ inter 𝒜.U s := Finset.inf_mono hst
      intro x hx
      simp only [latSec, AddSubgroup.mem_iInf] at hx ⊢
      exact fun y hy => hx y (hle hy)
    · intro q s x hx
      have := GlobalTheory.T.log_sections_differential_closed p 𝒜 (G e) ρ hρ q (inter 𝒜.U s) x (by rw [← hGe]; exact hx)
      rw [← hGe] at this
      exact this
    · intro q b' hqb
      exact he q b' (by omega)
  induction e₀ with
  | zero => exact h0
  | succ k ih => exact ih (step k h0)

end GlobalTheory.LogDR
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.cech_vanishing_frobenius_descent : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  atlas_forward_decl _root_.GlobalTheory.LogDR.descend_vanishing
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

theorem mem_chartForms_iff_sum_card {K : Type} [Field K] (A : Subring K) {n : ℕ} (x : Fin n → Kˣ)
    (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K) :
    η ∈ chartForms A x J t a ↔ ∃ d : {I : Finset (Fin n) // I.card = a} → K, (∀ I, d I ∈ A) ∧
      η = ∑ I, d I • (((t⁻¹ * ∏ j ∈ I.1 \ J, x j : Kˣ) : K) • logWedge x I.1) := by
  classical
  rw [GlobalTheory.T.mem_chart_forms_iff K A n x J t a η]
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hP : ∀ I : Finset (Fin n), ∏ j ∈ I \ J, (x j : K) ≠ 0 := fun I =>
    Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  have hsplit : ∀ f : Finset (Fin n) → abelian₂ K, (∀ I, I.card ≠ a → f I = 0) →
      ∑ I, f I = ∑ I : {I : Finset (Fin n) // I.card = a}, f I.1 := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Finset (Fin n) => I.card = a) f,
      Finset.sum_eq_zero (s := (Finset.univ : Finset {I : Finset (Fin n) // ¬ I.card = a}))
        (fun I _ => hf I.1 I.2), add_zero]
  constructor
  · rintro ⟨c, hc0, hcA, rfl⟩
    refine ⟨fun I => c I.1 * t / ∏ j ∈ I.1 \ J, (x j : K), fun I => hcA I.1, ?_⟩
    rw [hsplit (fun I => c I • logWedge x I) (fun I hI => by simp only [hc0 I hI, zero_smul])]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul]
    congr 1
    have := hP I.1
    push_cast
    field_simp
  · rintro ⟨d, hdA, rfl⟩
    refine ⟨fun I => if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) else 0,
      ?_, ?_, ?_⟩
    · intro I hI
      simp [hI]
    · intro I
      by_cases hI : I.card = a
      · dsimp only
        rw [dif_pos hI]
        have e : d ⟨I, hI⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) * t / ∏ j ∈ I \ J, (x j : K) =
            d ⟨I, hI⟩ := by
          have := hP I
          push_cast
          field_simp
        rw [e]
        exact hdA _
      · dsimp only
        rw [dif_neg hI, zero_mul, zero_div]
        exact zero_mem A
    · rw [hsplit (fun I => (if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K)
          else 0) • logWedge x I) (fun I hI => by simp only [dif_neg hI, zero_smul])]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dif_pos I.2, smul_smul]

theorem latModel_logAt_isFiniteQC : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C]
    (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ)
    (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ C _ E n ι 𝒜 G a F hF
  refine GlobalTheory.T.lattice_model_finite_quasicoherent X _ F hF fun y => ?_
  obtain ⟨i, hi⟩ : ∃ i, y ∈ 𝒜.U i := by
    have : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := ht.exists_nhds
  obtain ⟨f, hfW, hyf⟩ := (𝒜.affine i).exists_basicOpen_le (V := W) ⟨y, hyW⟩ hi
  let S := {I : Finset (Fin n) // I.card = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let u : S → X.functionFieldˣ := fun I => t⁻¹ * ∏ j ∈ I.1 \ 𝒜.J i, 𝒜.x i j
  let g : S → abelian₂ X.functionField := fun I => ((u I : X.functionFieldˣ) : X.functionField) • logWedge (𝒜.x i) I.1
  refine ⟨X.basicOpen f, Fintype.card S, fun k => g (e k), hyf, (𝒜.affine i).basicOpen f, ?_, ?_⟩
  · have hc : IsCoord (𝒜.x i) := ((𝒜.chart i).chart _ (𝒜.gen i)).coord
    have h1 := (GlobalTheory.LogDR.logWedge_basis _ n (𝒜.x i) hc).1.comp (fun k => (e k).1)
      (Subtype.val_injective.comp e.injective)
    exact h1.units_smul (fun k => u (e k))
  · intro z hz w
    have hzU : z ∈ 𝒜.U i := X.basicOpen_le f hz
    have hzt : G.IsEqn z t := hW z (hfW hz)
    rw [GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) G z t a (𝒜.chart i) hzU hzt,
      mem_chartForms_iff_sum_card]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun k => d (e k), fun k => hd _, (e.sum_comp fun I => d I • g I).symm⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun I => c (e.symm I), fun I => hc _, ?_⟩
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rfl

end GlobalTheory.LogDR
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.log_forms_lattice_finite : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ) (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  atlas_forward_decl _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem spanForms_eq_bot_of_isCoord {K : Type} [Field K] {n : ℕ} {x : Fin n → Kˣ} (hx : IsCoord x)
    (M : Set K) (H : Set Ω[K⁄ℤ]) {a : ℕ} (ha : n < a) : spanForms M H a = ⊥ := by
  let bs : Module.Basis (Fin n) K Ω[K⁄ℤ] := Module.Basis.mk hx.1 hx.2.ge
  haveI : Module.Finite K Ω[K⁄ℤ] := Module.Finite.of_basis bs
  have hfr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  refine eq_bot_iff.2 ((AddSubgroup.closure_le _).2 ?_)
  rintro η ⟨c, -, v, -, rfl⟩
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ v hv, smul_zero]
  exact AddSubgroup.zero_mem _

theorem logAt_eq_bot_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (Z : Set X) (G : CartierDiv X) {a : ℕ} (ha : n < a) (y : X) :
    logAt Z G a y = ⊥ := by
  have hg : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, -⟩ := (Opens.mem_iSup).1 hg
  exact spanForms_eq_bot_of_isCoord ((𝒜.chart i).chart _ (𝒜.gen i)).coord _ _ ha

theorem cechFam_eq_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) :
    cechFam 𝒜 G a = cechFam 𝒜 G (n + 1) := by
  funext s
  simp only [cechFam, logSec, latSec, logAt_eq_bot_of_lt 𝒜 _ G ha,
    logAt_eq_bot_of_lt 𝒜 _ G (Nat.lt_succ_self n)]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem exists_cechZero_cechFam_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  intro k _ X _ f hf C _ E n ι _ _ 𝒜 H B R hH
  haveI : IsProper f := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  haveI : X.IsSeparated := by
    constructor
    rw [show terminal.from X = f ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  letI := algebraΓOfHom f
  have key : ∀ (j : Fin B) (a : Fin (n + 2)), ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ b : ℕ, 0 < b →
      DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
    intro j a
    obtain ⟨F, ⟨lm⟩⟩ := GlobalTheory.T.exists_lattice_model X (logAt (suppAll E) (R j) a)
      (fun y g v hg hv => logAt_smul_mem X _ _ _ y g v hg hv)
    haveI : IsFiniteQC F := GlobalTheory.T.log_forms_lattice_finite X E 𝒜 (R j) a F lm
    have hev := eventually_subsingleton_coh_twistZ_of_isProjOver (f := f) (fun _ => rfl) F hf hH
    obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
    refine ⟨q₀, fun q hq b hb => ?_⟩
    obtain ⟨lm'⟩ := nonempty_latModel_twist X (logAt (suppAll E) (R j) a)
      (logAt (suppAll E) (q • H + R j) a) F (q • H) (toLB (q • H)) _ (presents_toLB _)
      (fun y g v hD => by rw [add_comm]; exact logtwist X _ _ _ _ y g v hD) lm
    haveI : IsFiniteQC (twist F (toLB (q • H))) := isFiniteQC_twist (isLB_toLB _)
    have hc := GlobalTheory.T.cech_lattice_cohomology_vanish X (logAt (suppAll E) (q • H + R j) a) (twist F (toLB (q • H))) 𝒜.U lm'
      𝒜.affine 𝒜.gen 𝒜.cover b hb
    refine hc.2 ?_
    haveI hs : Subsingleton (coh (twist F (lbZPow (toLB H) (q : ℤ))) b) := hq₀ q hq b hb
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F (isLB_toLB (q • H)) (isLB_lbZPow (isLB_toLB H) q)
      (by rw [cls_lbZPow (isLB_toLB H), ← toPic_apply, ← toPic_apply, map_nsmul, natCast_zsmul])
    exact (cohOn.mapIso k ⊤ b e).injective.subsingleton
  choose q₁ hq₁ using key
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun p : Fin B × Fin (n + 2) => q₁ p.1 p.2)
  refine ⟨Q, fun q hq j a b hb => ?_⟩
  by_cases ha : a ≤ n + 1
  · exact hq₁ j ⟨a, by omega⟩ q ((hQ (j, ⟨a, by omega⟩)).trans hq) b hb
  · rw [cechFam_eq_of_lt 𝒜 _ (by omega : n < a)]
    exact hq₁ j ⟨n + 1, by omega⟩ q ((hQ (j, ⟨n + 1, by omega⟩)).trans hq) b hb

end GlobalTheory.LogDR
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.serre_vanishing_snc_atlas : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  atlas_forward_decl _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogDR
open TopForm
variable {k K : Type} [CommRing k] [Field K]

def absDer (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) :
    letI := α.toAlgebra; letI : Module k Ω[K⁄ℤ] := Module.compHom _ α; Derivation k K Ω[K⁄ℤ] :=
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  { toFun := KaehlerDifferential.D ℤ K
    map_add' := map_add _
    map_smul' := fun c a => by
      obtain ⟨n, rfl⟩ := hk c
      rw [Algebra.smul_def, Derivation.leibniz]
      have : algebraMap k K (Int.castRingHom k n) = algebraMap ℤ K n := by simp
      rw [this, Derivation.map_algebraMap, smul_zero, add_zero, RingHom.id_apply]
      exact congrArg (· • KaehlerDifferential.D ℤ K a) this.symm
    map_one_eq_zero' := Derivation.map_one_eq_zero _
    leibniz' := fun a b => Derivation.leibniz _ a b }

theorem intCast_surj (p : ℕ) : Function.Surjective (Int.castRingHom (ZMod p)) :=
  fun a => ZMod.intCast_surjective a

def omegaToAbs (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) :
    Omega α →ₗ[K] Ω[K⁄ℤ] :=
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  letI tw : IsScalarTower k K Ω[K⁄ℤ] := ⟨fun c a m => mul_smul (α c) a m⟩
  @Derivation.liftKaehlerDifferential k K _ _ _ _ _ _ _ tw (absDer α hk)

@[simp] theorem omegaToAbs_dFun (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) (f : K) :
    omegaToAbs α hk (dFun α f) = dK f := by
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  letI tw : IsScalarTower k K Ω[K⁄ℤ] := ⟨fun c a m => mul_smul (α c) a m⟩
  exact @Derivation.liftKaehlerDifferential_comp_D k K _ _ _ _ _ _ _ tw (absDer α hk) f

def formsToLam (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) (D : ℕ) :
    Forms α D →ₗ[K] abelian₂ K :=
  (⋀[K]^D Ω[K⁄ℤ]).subtype ∘ₗ exteriorPower.map D (omegaToAbs α hk)

theorem formsToLam_dForm (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) {D : ℕ}
    (f : Fin D → K) :
    formsToLam α hk D (dForm α f) = ExteriorAlgebra.ιMulti K D fun i => dK (f i) := by
  simp only [formsToLam, dForm, dWedge, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, Function.comp_def]
  congr 1
  funext i
  exact omegaToAbs_dFun α hk (f i)

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv

theorem isEqn_sum_of_isSncOn {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (h : IsSncOn E U x J)
    (y : X) (hy : y ∈ U) : (∑ c, E c).IsEqn y (∏ j ∈ J, x j) := by
  classical
  obtain ⟨e, he_inj, hJ, hE⟩ := h
  have key : ∀ S : Finset C, (∑ c ∈ S, E c).IsEqn y (∏ c ∈ S, (e c).elim 1 x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isEqn_zero y
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (hE a y hy).add ih
  have hprod : (∏ c, (e c).elim 1 x) = ∏ j ∈ J, x j := by
    have s1 : ∀ c, (e c).elim 1 x = ∏ j ∈ J, (if e c = some j then x j else 1) := by
      intro c
      cases hc : e c with
      | none => simp
      | some j0 =>
        have hj0 : j0 ∈ J := (hJ j0).2 ⟨c, hc⟩
        simp [hj0]
    have s2 : ∀ j ∈ J, (∏ c, (if e c = some j then x j else 1)) = x j := by
      intro j hj
      obtain ⟨c0, hc0⟩ := (hJ j).1 hj
      have hiff : ∀ c, (e c = some j ↔ c0 = c) := fun c =>
        ⟨fun h => he_inj c0 c j hc0 h, fun h => h ▸ hc0⟩
      simp only [hiff]
      simp
    rw [Finset.prod_congr rfl (fun c _ => s1 c), Finset.prod_comm]
    exact Finset.prod_congr rfl s2
  have := key Finset.univ
  rwa [hprod] at this

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem det_mem_subring {K : Type} [Field K] (A : Subring K) {n : ℕ} (c : Matrix (Fin n) (Fin n) K)
    (hc : ∀ i k, c i k ∈ A) : c.det ∈ A := by
  rw [Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact A.zsmul_mem (A.prod_mem fun i _ => hc _ _) _

private theorem forms_mem_lemma {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (d : ℕ)
    (P : Submodule A (Forms α d)) (hgen : ∀ f : Fin d → A, dForm α f ∈ P) (ω : Forms α d) : ω ∈ P := by
  letI := α.toAlgebra
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  refine Submodule.span_induction (fun x hx => ?_) P.zero_mem (fun _ _ _ _ => P.add_mem)
    (fun a _ _ => P.smul_mem a) hω
  obtain ⟨w, rfl⟩ := hx
  have hw : ∀ i, ∃ c : A →₀ A, (c.sum fun a r => r • KaehlerDifferential.D k A a) = w i := fun i =>
    (Finsupp.mem_span_range_iff_exists_finsupp).1
      (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  choose c hc using hw
  have hw' : w = fun i => ∑ a ∈ (c i).support, c i a • KaehlerDifferential.D k A a :=
    funext fun i => (hc i).symm
  rw [hw']
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum_finset]
  refine P.sum_mem fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, AlternatingMap.coe_multilinearMap]
  exact P.smul_mem _ (hgen r)

private theorem ιMulti_eq_det_lemma_2 {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x)
    (v : Fin n → Ω[K⁄ℤ]) :
    ExteriorAlgebra.ιMulti K n v = (Module.Basis.mk hx.1 (le_of_eq hx.2.symm)).det v •
      ExteriorAlgebra.ιMulti K n (fun j => dK (x j : K)) := by
  classical
  set b := Module.Basis.mk hx.1 (le_of_eq hx.2.symm) with hbdef
  have hb : (fun j => dK (x j : K)) = ⇑b := (Module.Basis.coe_mk _ _).symm
  rw [hb, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have h1 := congrArg (fun g => g v)
    (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K n)))
  simp only [AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply, smul_eq_mul] at h1
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_comm, sub_self]

theorem formOf_eq_regAt_smul (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) {U : X.Opens} (ω : FormsOn f d U) (y : X) (hy : y ∈ U) (x : Fin d → X.functionFieldˣ)
    (hx : AlgChart (locRing y) x) :
    ∃ u : X.functionField, RegAt y u ∧
      formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) =
        u • ExteriorAlgebra.ιMulti _ d fun j => dK (x j : X.functionField) := by
  classical
  have hxc := hx.coord
  set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef
  have hbi : ∀ i, b i = dK (x i : X.functionField) := fun i => Module.Basis.mk_apply _ _ _
  have hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y := by
    intro g hg j
    obtain ⟨c, hc, hd⟩ := hx.deriv g hg
    have hs : dK g = ∑ i, c i • b i := by
      rw [hd]
      simp only [hbi]
    rw [hs, Module.Basis.repr_sum_self]
    exact hc j
  let W := ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField))
  let P : Submodule (Γ(X, U)) (FormsOn f d U) :=
    { carrier := {ω | ∃ u, RegAt y u ∧
        formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) = u • W}
      add_mem' := by
        rintro a c ⟨u1, h1, e1⟩ ⟨u2, h2, e2⟩
        exact ⟨u1 + u2, h1.add h2, by rw [map_add, map_add, e1, e2, add_smul]⟩
      zero_mem' := ⟨0, regAt_zero y, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a c ⟨u, hu, e⟩
        refine ⟨fnOf U (gen_mem hy) a * u, (regAt_fnOf hy _ a).mul hu, ?_⟩
        rw [LinearMap.map_smulₛₗ, map_smul, e, mul_smul] }
  have hgen : ∀ g : Fin d → Γ(X, U), dForm (algX f U) g ∈ P := by
    intro g
    refine ⟨b.det (fun j => dK (fnOf U (gen_mem hy) (g j))), ?_, ?_⟩
    · rw [← mem_locRing, Module.Basis.det_apply]
      refine det_mem_subring _ _ fun i j => ?_
      rw [Module.Basis.toMatrix_apply]
      exact hrep _ (mem_locRing.2 (regAt_fnOf hy _ _)) i
    · simp only [formOf, formMap_dForm, formsToLam_dForm]
      exact ιMulti_eq_det_lemma_2 x hxc _
  exact forms_mem_lemma (algX f U) d P hgen ω

theorem coordForm_eq_regAt_smul (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) {U : X.Opens} (ω : FormsOn f d U) (hω : IsFrame ω) (y : X) (hy : y ∈ U)
    (x : Fin d → X.functionFieldˣ) (hx : ∀ j, RegAt y (x j : X.functionField)) :
    ∃ v : X.functionField, RegAt y v ∧
      ExteriorAlgebra.ιMulti _ d (fun j => dK (x j : X.functionField)) =
        v • formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) := by
  classical
  choose Uj hyj aj haj using fun j => RegAt.exists_fnOf (hx j)
  have hS : (U : Set X) ∩ ⋂ j, (Uj j : Set X) ∈ nhds y :=
    Filter.inter_mem (U.isOpen.mem_nhds hy)
      (Filter.iInter_mem.2 fun j => (Uj j).isOpen.mem_nhds (hyj j))
  let O : X.Opens := ⟨interior ((U : Set X) ∩ ⋂ j, (Uj j : Set X)), isOpen_interior⟩
  have hyO : y ∈ O := mem_interior_iff_mem_nhds.2 hS
  obtain ⟨W, hWa, hyW, hWO⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)) hyO
  have hWU : W ≤ U := fun z hz => (interior_subset (hWO hz)).1
  have hWj : ∀ j, W ≤ Uj j := fun j z hz => Set.mem_iInter.1 (interior_subset (hWO hz)).2 j
  have hg : genericPoint X ∈ W := gen_mem hyW
  have hgx : ∀ j, fnOf W hg (resG X (hWj j) (aj j)) = (x j : X.functionField) := by
    intro j
    rw [fnOf_resG]
    exact haj j
  obtain ⟨c, hc⟩ := hω.exists_coeff hWU (dForm (algX f W) fun j => resG X (hWj j) (aj j))
  have hc' := hc W hWa le_rfl
  have e1 : formOf W hg (resForm le_rfl (dForm (algX f W) fun j => resG X (hWj j) (aj j))) =
      formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j)) :=
    formOf_resForm le_rfl hg _
  have e2 : formOf W hg (resForm hWU ω) = formOf U (gen_mem hy) ω := formOf_resForm hWU hg ω
  have e3 : formsToLam (constFn f) (intCast_surj p) d
      (formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j))) =
      ExteriorAlgebra.ιMulti _ d (fun j => dK (x j : X.functionField)) := by
    simp only [formOf, formMap_dForm, formsToLam_dForm]
    congr 1
    funext j
    rw [← hgx j]
  refine ⟨fnOf W hg (resG X le_rfl c), regAt_fnOf hyW hg _, ?_⟩
  rw [← e3, ← e1, hc', LinearMap.map_smulₛₗ, map_smul, e2]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv

theorem ιMulti_coord_ne_zero {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    ExteriorAlgebra.ιMulti K n (fun j => dK (x j : K)) ≠ 0 := by
  classical
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli (le_of_eq hsp.symm)
  intro h0
  have hb : (fun j => dK (x j : K)) = ⇑b := (Module.Basis.coe_mk _ _).symm
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ∀ e : Fin n ↪o Fin n, ⇑e = id := by
    intro e
    have h1 := Finset.orderEmbOfFin_unique' hc (f := e) (fun _ => Finset.mem_univ _)
    have h2 := Finset.orderEmbOfFin_unique' hc
      (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (fun _ => Finset.mem_univ _)
    rw [h1, ← h2]
    rfl
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  have hne := (exteriorPower.ιMulti_family_linearIndependent_ofBasis K n b).ne_zero s
  apply hne
  rw [exteriorPower.ιMulti_family, he, Function.comp_id, ← hb]
  exact Subtype.ext (by simpa using h0)

theorem exists_baseForm_eq (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) [SmoothOfRelativeDimension d f] (y : X) (x : Fin d → X.functionFieldˣ)
    (hx : AlgChart (locRing y) x) :
    ∃ (g : X.functionFieldˣ) (u : X.functionField), (canonical f d).IsEqn y g ∧ UnitAt y u ∧
      formsToLam (constFn f) (intCast_surj p) d (baseForm f d) =
        ((g : X.functionField) * u) • ExteriorAlgebra.ιMulti _ d fun j => dK (x j : X.functionField) := by
  classical
  set L := CanonLB.all f d with hL
  have hcov : y ∈ ⨆ i, L.bundle.U i := by
    rw [L.isLB.cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hω : IsFrame (L.om i) := L.isFrame i
  have hgU : genericPoint X ∈ L.bundle.U i := gen_mem hi
  obtain ⟨u0, hu0, e0⟩ := formOf_eq_regAt_smul p f d (L.om i) y hi x hx
  obtain ⟨v, hv, ev⟩ := coordForm_eq_regAt_smul p f d (L.om i) hω y hi x
    (fun j => mem_locRing.1 (hx.mem j))
  have hW : ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) ≠ 0 :=
    ιMulti_coord_ne_zero x hx.coord
  have hvu : v * u0 = 1 := by
    have h0 : (v * u0 - 1) •
        ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) = 0 := by
      rw [sub_smul, mul_smul, ← e0, ← ev, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hW)
  have hu0ne : u0 ≠ 0 := by
    rintro rfl
    simp at hvu
  have hUu0 : UnitAt y u0 := by
    refine (unitAt_iff hu0ne).2 ⟨hu0, ?_⟩
    rw [← eq_inv_of_mul_eq_one_left hvu]
    exact hv
  have hB := isFrame_baseFrame f d
  have hr := formOf_eq_ratio_smul (gen_mem_baseOpen f d) hgU hB hω
  set t := fnOf (baseOpen f d ⊓ L.bundle.U i) (by exact ⟨gen_mem_baseOpen f d, hgU⟩)
    (↑(hB.ratio hω) : Γ(X, baseOpen f d ⊓ L.bundle.U i)) with ht
  have htne : t ≠ 0 := ((hB.ratio hω).isUnit.map _).ne_zero
  have hbf : baseForm f d = ((Units.mk0 t⁻¹ (inv_ne_zero htne) : X.functionFieldˣ) : X.functionField) •
      formOf (L.bundle.U i) hgU (L.om i) := by
    rw [Units.val_mk0, hr, smul_smul, inv_mul_cancel₀ htne, one_smul]
    rfl
  refine ⟨Units.mk0 t⁻¹ (inv_ne_zero htne), u0,
    isDivOfForm_canonical f d _ (L.om i) hω y hi _ hbf, hUu0, ?_⟩
  rw [hbf, map_smul, e0, smul_smul]

private theorem dlog_mul_lemma_3 {K : Type} [Field K] (g h : Kˣ) : dlog (g * h) = dlog g + dlog h := by
  have hg := g.ne_zero
  have hh := h.ne_zero
  simp only [dlog, dK, Units.val_mul, Units.val_inv_eq_inv_val, Derivation.leibniz, smul_add, smul_smul]
  rw [show ((g : K) * h)⁻¹ * g = (h : K)⁻¹ by field_simp,
    show ((g : K) * h)⁻¹ * h = (g : K)⁻¹ by field_simp, add_comm]

private theorem dlog_prod_lemma_4 {K : Type} [Field K] {n : ℕ} (u : Kˣ) (x : Fin n → Kˣ) (J : Finset (Fin n))
    (m : Fin n → ℤ) : dlog (u * ∏ j ∈ J, x j ^ m j) = dlog u + ∑ j ∈ J, m j • dlog (x j) := by
  let φ : Kˣ →* Multiplicative Ω[K⁄ℤ] :=
    { toFun := fun g => Multiplicative.ofAdd (dlog g)
      map_one' := by simp [dlog, dK]
      map_mul' := fun g h => by rw [dlog_mul_lemma_3]; rfl }
  have h := congrArg Multiplicative.toAdd (map_mul φ u (∏ j ∈ J, x j ^ m j))
  rw [map_prod] at h
  simpa only [map_zpow, toAdd_mul, toAdd_prod, toAdd_zpow, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, φ] using h

private theorem unit_or_succ_lemma_5 {X : Scheme} [IsIntegral X] {y : X} {f : X.functionField}
    (hf : RegAt y f) : UnitAt y f ∨ UnitAt y (f + 1) := by
  by_contra h
  push_neg at h
  have h1 : ZeroAt y f := zeroAt_iff.2 ⟨hf, h.1⟩
  have hr1 : RegAt y (1 : X.functionField) := (unitAt_one y).regAt
  have h2 : ZeroAt y (f + 1) := zeroAt_iff.2 ⟨hf.add hr1, h.2⟩
  have hm : RegAt y (-1 : X.functionField) := mem_locRing.1 (neg_mem (mem_locRing.2 hr1))
  have h3 := h2.add (h1.mul hm)
  have h4 : f + 1 + f * -1 = (1 : X.functionField) := by ring
  rw [h4] at h3
  exact (zeroAt_iff.1 h3).2 (unitAt_one y)

private theorem logAt_top_lemma_6 {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G : CartierDiv X) (y : X)
    {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (hch : AlgChart (locRing y) x)
    (hlog : ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
      ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y ↑u ∧ g = u * ∏ j ∈ J, x j ^ m j)
    (gG : X.functionFieldˣ) (hG : G.IsEqn y gG) (η : abelian₂ X.functionField) :
    η ∈ logAt Z G n y ↔ ∃ a : X.functionField, RegAt y (a * gG) ∧
      η = (a * (∏ j ∈ J, (x j : X.functionField))⁻¹) •
        ExteriorAlgebra.ιMulti _ n (fun j => dK (x j : X.functionField)) := by
  classical
  have hxc := hch.coord
  set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef
  have hbi : ∀ i, b i = dK (x i : X.functionField) := fun i => Module.Basis.mk_apply _ _ _
  set W := ExteriorAlgebra.ιMulti X.functionField n (fun j => dK (x j : X.functionField)) with hW
  set e : X.functionField := ∏ j ∈ J, (x j : X.functionField) with he
  have hene : e ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  let s : Fin n → X.functionField := fun i => if i ∈ J then (x i : X.functionField) else 1
  have hs_prod : ∏ i, s i = e := by
    simp only [s]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hsA : ∀ i, s i ∈ locRing y := fun i => by
    simp only [s]
    split_ifs
    · exact hch.mem i
    · exact one_mem _
  have hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y := by
    intro g hg j
    obtain ⟨c, hc, hd⟩ := hch.deriv g hg
    have hs : dK g = ∑ i, c i • b i := by
      rw [hd]
      simp only [hbi]
    rw [hs, Module.Basis.repr_sum_self]
    exact hc j
  have hcoord : ∀ g : X.functionFieldˣ, LogUnit Z y g → ∀ i, s i * b.repr (dlog g) i ∈ locRing y := by
    intro g hg i
    obtain ⟨u, m, hu, rfl⟩ := (hlog g).1 hg
    rw [dlog_prod_lemma_4]
    simp only [map_add, map_sum, Finsupp.add_apply, Finsupp.finset_sum_apply, mul_add, Finset.mul_sum]
    refine add_mem ?_ (sum_mem fun j hj => ?_)
    · rw [show dlog u = ((u⁻¹ : X.functionFieldˣ) : X.functionField) • dK (u : X.functionField) from rfl,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      refine mul_mem (hsA i) (mul_mem ?_ (hrep _ (mem_locRing.2 hu.regAt) i))
      rw [Units.val_inv_eq_inv_val]
      exact mem_locRing.2 hu.inv.regAt
    · rw [map_zsmul, Finsupp.smul_apply, mul_smul_comm]
      refine zsmul_mem ?_ _
      have hdx : dlog (x j) = ((x j : X.functionField))⁻¹ • b j := by
        rw [hbi]
        simp [dlog, Units.val_inv_eq_inv_val]
      rw [hdx, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hij : j = i
      · subst hij
        simp only [s, hj, if_true, mul_one]
        rw [mul_inv_cancel₀ (x j).ne_zero]
        exact one_mem _
      · rw [if_neg hij, mul_zero, mul_zero]
        exact zero_mem _
  constructor
  · intro hη
    let S : AddSubgroup (abelian₂ X.functionField) :=
      { carrier := {η | ∃ a : X.functionField, RegAt y (a * gG) ∧ η = (a * e⁻¹) • W}
        add_mem' := by
          rintro _ _ ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          exact ⟨a1 + a2, by rw [add_mul]; exact h1.add h2, by rw [add_mul, add_smul]⟩
        zero_mem' := ⟨0, by rw [zero_mul]; exact regAt_zero y, by rw [zero_mul, zero_smul]⟩
        neg_mem' := by
          rintro _ ⟨a, h, rfl⟩
          exact ⟨-a, by rw [neg_mul]; exact mem_locRing.1 (neg_mem (mem_locRing.2 h)),
            by rw [neg_mul, neg_smul]⟩ }
    have hle : logAt Z G n y ≤ S := by
      rw [logAt, spanForms, AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      choose g hg hgv using hv
      have hdet : b.det v * e ∈ locRing y := by
        rw [Module.Basis.det_apply, ← hs_prod, mul_comm, ← Matrix.det_mul_column]
        refine det_mem_subring _ _ fun i k => ?_
        rw [Matrix.of_apply, Module.Basis.toMatrix_apply, ← hgv k]
        exact hcoord (g k) (hg k) i
      refine ⟨(b.det v * e) * c, ?_, ?_⟩
      · rw [mul_assoc]
        exact RegAt.mul (mem_locRing.1 hdet) ((hG.regularAt_iff).1 hc)
      · rw [ιMulti_eq_det_lemma_2 x hxc v, smul_smul]
        congr 1
        rw [mul_right_comm (b.det v) e c, mul_assoc _ e, mul_inv_cancel₀ hene, mul_one, mul_comm]
    exact hle hη
  · rintro ⟨a, ha, rfl⟩
    have hreg : ∀ i, RegAt y (x i : X.functionField) := fun i => mem_locRing.1 (hch.mem i)
    have hq : ∀ i, ∃ q : X.functionFieldˣ, LogUnit Z y q ∧
        dK (q : X.functionField) = dK (x i : X.functionField) ∧
        (q : X.functionField) = s i * (if i ∈ J then 1 else (q : X.functionField)) ∧
        RegAt y (if i ∈ J then 1 else (q : X.functionField)) := by
      intro i
      by_cases hi : i ∈ J
      · refine ⟨x i, (hlog _).2 ⟨1, Pi.single i 1, unitAt_one y, ?_⟩, rfl, by simp [s, hi], ?_⟩
        · rw [one_mul, Finset.prod_eq_single i (fun j _ hji => by simp [Pi.single_apply, hji])
            (fun h => absurd hi h)]
          simp
        · simpa [hi] using (unitAt_one y).regAt
      · rcases unit_or_succ_lemma_5 (hreg i) with h | h
        · exact ⟨x i, (hlog _).2 ⟨x i, 0, h, by simp⟩, rfl, by simp [s, hi], by simpa [hi] using hreg i⟩
        · have hne : (x i : X.functionField) + 1 ≠ 0 := h.ne_zero
          refine ⟨Units.mk0 _ hne, (hlog _).2 ⟨Units.mk0 _ hne, 0, by simpa using h, by simp⟩, ?_,
            by simp [s, hi], ?_⟩
          · simp [dK]
          · simpa [hi] using h.regAt
    choose q hqlog hqd hqs hqr using hq
    let v : Fin n → Ω[X.functionField⁄ℤ] := fun i => dlog (q i)
    have hv : ExteriorAlgebra.ιMulti X.functionField n v = (∏ i, ((q i : X.functionField))⁻¹) • W := by
      have hv' : v = fun i => ((q i : X.functionField))⁻¹ • dK (x i : X.functionField) := by
        funext i
        simp only [v, dlog, Units.val_inv_eq_inv_val, hqd]
      rw [hv', AlternatingMap.map_smul_univ]
    let r : Fin n → X.functionField := fun i => if i ∈ J then 1 else (q i : X.functionField)
    have hqprod : ∏ i, (q i : X.functionField) = e * ∏ i, r i := by
      rw [← hs_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hqs i
    have hqne : ∏ i, (q i : X.functionField) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (q i).ne_zero
    have hrne : ∏ i, r i ≠ 0 := by
      intro h0
      apply hqne
      rw [hqprod, h0, mul_zero]
    have hrA : RegAt y (∏ i, r i) := mem_locRing.1 (prod_mem fun i _ => mem_locRing.2 (hqr i))
    have hcoef : G.RegularAt y (a * ∏ i, r i) := by
      rw [hG.regularAt_iff, mul_right_comm]
      exact RegAt.mul ha hrA
    have hmem : (a * ∏ i, r i) • ExteriorAlgebra.ιMulti X.functionField n v ∈ logAt Z G n y := by
      rw [logAt, spanForms]
      exact AddSubgroup.subset_closure ⟨a * ∏ i, r i, hcoef, v, fun i => ⟨q i, hqlog i, rfl⟩, rfl⟩
    convert hmem using 1
    rw [hv, smul_smul]
    congr 1
    rw [Finset.prod_inv_distrib, hqprod]
    field_simp

theorem logAt_top_eq_canonical : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  intro p _ X _ f d _ C _ E ι 𝒜
  classical
  refine ⟨formsToLam (constFn f) (intCast_surj p) d (baseForm f d), ?_, ?_⟩
  · have hg0 : genericPoint X ∈ ⨆ i, 𝒜.U i := by
      rw [𝒜.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hg0
    obtain ⟨g, u, -, hu, e⟩ := exists_baseForm_eq p X f d _ (𝒜.x i) ((𝒜.chart i).chart _ hi)
    rw [e]
    exact smul_ne_zero (mul_ne_zero g.ne_zero hu.ne_zero)
      (ιMulti_coord_ne_zero _ ((𝒜.chart i).chart _ hi).coord)
  · intro G y η
    have hy0 : y ∈ ⨆ i, 𝒜.U i := by
      rw [𝒜.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy0
    have hch := (𝒜.chart i).chart y hi
    obtain ⟨gK, u, hgK, hu, hω⟩ := exists_baseForm_eq p X f d y (𝒜.x i) hch
    have hE := isEqn_sum_of_isSncOn E (𝒜.U i) (𝒜.x i) (𝒜.J i) (𝒜.snc i) y hi
    obtain ⟨gG, hG⟩ := CartierDiv.exists_isEqn G y
    have hT := (hgK.add hE).add hG
    rw [logAt_top_lemma_6 (suppAll E) G y (𝒜.x i) (𝒜.J i) hch ((𝒜.chart i).logUnit y hi) gG hG η, hω]
    have hune : (u : X.functionField) ≠ 0 := hu.ne_zero
    have hgne : (gK : X.functionField) ≠ 0 := gK.ne_zero
    have hene : (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => (𝒜.x i j).ne_zero
    simp only [hT.regularAt_iff, Units.val_mul, Units.coe_prod]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹, ?_, ?_⟩
      · have hh : a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹ *
            ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG) =
            (a * gG) * (u : X.functionField)⁻¹ := by
          field_simp
        rw [hh]
        exact ha.mul hu.inv.regAt
      · rw [smul_smul]
        congr 1
        field_simp
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))), ?_, ?_⟩
      · have hh : c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG =
            (c * ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG)) * u := by
          ring
        rw [hh]
        exact hc.mul hu.regAt
      · rw [smul_smul]
        congr 1
        field_simp

end GlobalTheory.LogDR
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.top_log_forms_canonical_generator : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  atlas_forward_decl _root_.GlobalTheory.LogDR.logAt_top_eq_canonical
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPVanish

theorem gen_mem_inter {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens)
    (h : ∀ i, genericPoint X ∈ U i) (s : Finset ι) : genericPoint X ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.inf_insert]; exact ⟨h i, ih⟩

theorem cechZero_of_forall_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (N : Finset ι → AddSubgroup E) (h : ∀ s, ∀ x ∈ N s, x = 0) (b : ℕ) : DI.CechZero N b := by
  intro c hc _
  refine ⟨0, ⟨rfl, fun s => zero_mem _, fun _ _ => rfl⟩, ?_⟩
  funext t
  simp only [DI.delta, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
  exact (h t _ (hc.2.1 t)).symm

theorem cechFam_eq_zero {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) (s : Finset ι) :
    ∀ x ∈ cechFam 𝒜 G a s, x = 0 := by
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ 𝒜.U i := by
    have : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  have hx' : x ∈ logAt (suppAll E) G a (genericPoint X) :=
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hx (genericPoint X)) (gen_mem_inter _ 𝒜.gen s)
  have hc := ((𝒜.chart i).chart _ hi).coord
  rw [logAt, spanForms_eq_bot_of_lt_card _ n (𝒜.x i) _ _ a hc ha] at hx'
  exact (AddSubgroup.mem_bot).1 hx'

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : X.IsSeparated := by
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver h
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

theorem twist_split {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (M K H : CartierDiv X) (r : ℕ) (b : C → ℕ) (hr : 0 < r) (key : r • (M - K) = ∑ c, b c • E c + H)
    (N : ℕ) :
    N • (M - K) - ∑ c, (N * b c / r) • E c - ∑ c, E c =
      (N / r) • H + ((N % r) • (M - K) - ∑ c, ((N % r) * b c / r) • E c - ∑ c, E c) := by
  conv_lhs => rw [← Nat.div_add_mod N r]
  generalize N / r = Q
  generalize N % r = ρ
  have hfl : ∀ c, (r * Q + ρ) * b c / r = ρ * b c / r + Q * b c := by
    intro c
    rw [show (r * Q + ρ) * b c = ρ * b c + r * (Q * b c) by ring, Nat.add_mul_div_left _ _ hr]
  simp only [hfl, add_smul, Finset.sum_add_distrib]
  rw [show r * Q = Q * r from mul_comm _ _, mul_smul, key]
  simp only [mul_smul, ← Finset.smul_sum, smul_add]
  abel

theorem subsingleton_coh_of_decomp : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → d < p →
    ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} [Fintype ι] [LinearOrder ι]
      (𝒜 : SncAtlas E d ι), Decomp p 𝒜 → ∀ (M H : CartierDiv X) (r : ℕ) (b : C → ℕ),
      IsAmpleLB (toLB H) → 0 < r → (∀ c, b c < r) → r • M = r • canonical f d + ∑ c, b c • E c + H →
      ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (toLB M)) q) := by
  intro p _ X _ f d _ hproj _ C _ E ι _ _ 𝒜 hdec M H r b hH hr hb hM q hq
  haveI : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  haveI : X.IsSeparated := isSeparated_of_isProjOver hproj
  let G : ℕ → CartierDiv X := fun e =>
    p ^ e • (M - canonical f d) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c
  let R : Fin r → CartierDiv X := fun j =>
    (j : ℕ) • (M - canonical f d) - ∑ c, ((j : ℕ) * b c / r) • E c - ∑ c, E c
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.T.serre_vanishing_snc_atlas (ZMod p) X f hproj E 𝒜 H r R hH
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : q₀ * r ≤ p ^ (q₀ * r) := by
    have := Nat.lt_pow_self hp1 (n := q₀ * r)
    omega
  have hQ : q₀ ≤ p ^ (q₀ * r) / r := (Nat.le_div_iff_mul_le hr).2 hpow
  have key : r • (M - canonical f d) = ∑ c, b c • E c + H := by
    rw [smul_sub, hM]; abel
  have hG : G (q₀ * r) = (p ^ (q₀ * r) / r) • H + R ⟨p ^ (q₀ * r) % r, Nat.mod_lt _ hr⟩ :=
    twist_split E M (canonical f d) H r b hr key _
  have hrec : ∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c :=
    GlobalTheory.T.frobenius_twist_divisor_recursion X p E M (canonical f d) r b (by omega) hr
  have hvan : ∀ a b' : ℕ, d < a + b' → DI.CechZero (cechFam 𝒜 (G (q₀ * r)) a) b' := by
    intro a b' hab
    rcases Nat.eq_zero_or_pos b' with rfl | hb'
    · exact cechZero_of_forall_eq_zero _ (cechFam_eq_zero 𝒜 _ (by omega)) 0
    · rw [hG]; exact hq₀ _ hQ _ a b' hb'
  have h0 := GlobalTheory.T.cech_vanishing_frobenius_descent p X E 𝒜 G hdec hrec (q₀ * r) hvan d q (by omega)
  have hG0 : G 0 = M - canonical f d - ∑ c, E c := by
    simp only [G, pow_zero, one_smul, one_mul, Nat.div_eq_of_lt (hb _), zero_smul,
      Finset.sum_const_zero, sub_zero]
  obtain ⟨ω₀, hω₀, htop⟩ := GlobalTheory.T.top_log_forms_canonical_generator p X f d E 𝒜
  let φ : X.functionField →ₗ[X.functionField] abelian₂ X.functionField :=
    LinearMap.toSpanSingleton _ _ ω₀
  have hφ : Function.Injective φ := fun c c' h => smul_left_injective _ hω₀ h
  have hD : canonical f d + ∑ c, E c + G 0 = M := by rw [hG0]; abel
  have hlat : logAt (suppAll E) (G 0) d =
      fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom := by
    funext y; ext η
    rw [htop, AddSubgroup.mem_map, hD]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.2 (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hc), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.1 hc y rfl, rfl⟩
  obtain ⟨L0⟩ := nonempty_latModel_of_presents X M (toLB M) _ (presents_toLB M)
  obtain ⟨L1⟩ := (GlobalTheory.T.lattice_model_unique_injective X _ (LB.toMod (toLB M)) (LB.toMod (toLB M)) φ hφ L0).1
  haveI := LB.isQuasicoherent_toMod (isLB_toLB M)
  refine (GlobalTheory.T.cech_lattice_cohomology_vanish X _ (LB.toMod (toLB M)) 𝒜.U L1 𝒜.affine 𝒜.gen 𝒜.cover q hq).1 ?_
  have hfam : cechFam 𝒜 (G 0) d = fun s =>
      latSec (fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom) (inter 𝒜.U s) := by
    funext s; simp only [cechFam, logSec]; rw [hlat]
  rwa [hfam] at h0

end GlobalTheory.CharPVanish
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open GlobalTheory.Cartier GlobalTheory.LogDR

theorem GlobalTheory.CharPVanish.charp_of_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X _ g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  obtain ⟨m, E, 𝒜, hdec, hE⟩ := GlobalTheory.LogAtlas.exists_atlas_decomp p Y X g f π d hpb hproj hdp s L σ h
  obtain ⟨M', hM'⟩ := GlobalTheory.Cartier.toPic_surjective (cls M hM)
  have hcan : GlobalTheory.Cartier.toPic (GlobalTheory.Cartier.canonical f d) = cls K.bundle K.isLB :=
    (GlobalTheory.Cartier.presents_canonical f d).toPic_eq.trans
      ((CechPic.cls_eq_iff _ _).2 (CanonLB.lbIso _ _))
  have hH : GlobalTheory.Cartier.toPic (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)
      = cls A hA.isLB := by
    simp only [map_sub, map_nsmul, map_sum, hM', hcan, hE]
    rw [heq]
    abel
  have hiso : LBIso (GlobalTheory.Cartier.toLB (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)) A := by
    rw [← CechPic.cls_eq_iff (GlobalTheory.Cartier.isLB_toLB _) hA.isLB, ← GlobalTheory.Cartier.toPic_apply]
    exact hH
  have hampleH := IsAmpleLB.of_lbIso hA (GlobalTheory.Cartier.isLB_toLB _) hiso
  have key := GlobalTheory.CharPVanish.subsingleton_coh_of_decomp p X f d hproj hdp E 𝒜 hdec M'
    (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i) r b hampleH hr hb (by abel) q hq
  refine GlobalTheory.Div.coh_subsingleton_of_cls_eq X (GlobalTheory.Cartier.toLB M') M (GlobalTheory.Cartier.isLB_toLB _) hM ?_ q key
  rw [← GlobalTheory.Cartier.toPic_apply, hM']
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.kodaira_vanishing_mod_p_squared : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  atlas_forward_decl _root_.GlobalTheory.CharPVanish.charp_of_lift
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory

theorem charp_vanishing_liftable : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨κ, U, hcov, hdisj, hU⟩ := GlobalTheory.T.exists_integral_clopen_cover_of_smooth_quasiCompact_field (ZMod p) X f
  refine GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover X M κ U hM hcov hdisj q (fun c => ?_)
  have hint := (hU c).1
  have hcl := (hU c).2
  obtain ⟨W, ρ, hρ, hpb'⟩ := GlobalTheory.T.open_subscheme_closed_base_change (ZMod (p ^ 2)) (ZMod p)
    (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) Y X g f π (U c) (ZMod.ringHom_surjective _) hpb
  have hsm : SmoothOfRelativeDimension d ((U c).ι ≫ f) := by
    have := smoothOfRelativeDimension_comp (f := (U c).ι) 0 d f
    simpa using this
  have hproj' : IsProjOver ((U c).ι ≫ f) := by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, (U c).ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  have h' := GlobalTheory.T.relative_snc_open_immersion (ZMod (p ^ 2)) Y W.toScheme g W.ι d s L σ h
  let K' : CanonLB ((U c).ι ≫ f) d := Classical.choice inferInstance
  have hA' : IsAmpleLB (A.pull (U c).ι) := hA.pull_of_isClosedImmersion (U c).ι
  have hK := GlobalTheory.T.canonical_bundle_open_restrict (ZMod p) X (U c).toScheme f (U c).ι d K K'
  refine GlobalTheory.T.kodaira_vanishing_mod_p_squared p W.toScheme (U c).toScheme (W.ι ≫ g) ((U c).ι ≫ f) ρ d hpb' hproj' hdp s
    (fun i => (L i).pull W.ι) (fun i => Cartier.secPull (σ i) W.ι) h' K' (M.pull (U c).ι) (A.pull (U c).ι)
    (pull_isLB hM _) hA' r b hr hb ?_ q hq
  have e2 := congrArg (CechPic.pull (U c).ι) heq
  simp only [map_nsmul, map_add, map_sum] at e2
  rw [cls_pull hM (U c).ι, hK, cls_pull hA.isLB (U c).ι, e2]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pull_comp, ← hρ, pull_comp]
  rfl

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SemicontLB

open GlobalTheory.AbLaw GlobalTheory.Adelic

theorem nonempty_cechLB_homology_equiv_coh {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB) {κ : Type} [LinearOrder κ] [Finite κ]
    {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (n : ℕ) : Nonempty ((cechLB f M D).homology n ≃ coh (LB.toMod M) n) := by
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
  exact ⟨(((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (FieldChangeInter.cechIso f M D)).toLinearEquiv.toEquiv).trans
    (cechHEquivCoh R hc hD (LB.toMod M) n).toEquiv⟩

private theorem affine_cover_preimage_of_isAffineHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsAffineHom π] {ι : Type}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) :
    (⨆ i, π ⁻¹ᵁ U i = ⊤) ∧ ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i) := by
  classical
  have key : ∀ s : Finset ι, ⨅ i ∈ s, π ⁻¹ᵁ U i = π ⁻¹ᵁ (⨅ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, ih]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hU]; rfl
  · rw [key s]; exact (hint s hs).preimage π

private theorem fibre_lemma_2 {R : Type} [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ)
    (hV : ∀ p : PrimeSpectrum R, Module.Finite p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q))
    {κ : Type} [Field κ] (g : R →+* κ) :
    Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q) ↔
      Module.finrank (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R
          (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology q) = 0 := by
  let P : PrimeSpectrum R := ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  change _ ↔ Module.finrank P.asIdeal.ResidueField
    ((((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) = 0
  haveI := hV P
  have hunit : P.asIdeal.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid κ) := by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.2 fun h => hx (RingHom.mem_ker.2 h)
  let φ : P.asIdeal.ResidueField →+* κ := Ideal.ResidueField.lift P.asIdeal g le_rfl hunit
  have hcomp : φ.comp (algebraMap R P.asIdeal.ResidueField) = g :=
    RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap _ _ le_rfl hunit r
  letI : Algebra P.asIdeal.ResidueField κ := φ.toAlgebra
  obtain ⟨e⟩ := FieldChangeInter.nonempty_homology_equiv κ
    (((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) q
  have e2 := ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp (algebraMap R P.asIdeal.ResidueField) φ).symm
        (ComplexShape.up ℕ)).app K)).toLinearEquiv
  have e3 : (↑((((ModuleCat.extendScalars (φ.comp (algebraMap R P.asIdeal.ResidueField))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) =
      (↑((((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) := by rw [hcomp]
  rw [← Module.finrank_baseChange (R := κ), Module.finrank_zero_iff]
  exact (((Equiv.cast e3).symm.trans e2.symm.toEquiv).trans e.toEquiv).subsingleton_congr

theorem subsingleton_coh_pull_of_ker_le : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [IsProper f] [Flat f] (M : LB X), M.IsLB → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂]
    (g₁ : R →+* κ₁) (g₂ : R →+* κ₂) (X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ Sp κ₁) (f₂ : X₂ ⟶ Sp κ₂) (π₁ : X₁ ⟶ X)
    (π₂ : X₂ ⟶ X), IsPullback π₁ f₁ f (spMap g₁) → IsPullback π₂ f₂ f (spMap g₂) →
    RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton (coh (LB.toMod (M.pull π₁)) q) →
    Subsingleton (coh (LB.toMod (M.pull π₂)) q) := by
  intro R _ _ X f _ _ M hM κ₁ κ₂ _ _ g₁ g₂ X₁ X₂ f₁ f₂ π₁ π₂ h₁ h₂ hker q hsub
  haveI : CompactSpace X := by
    have : QuasiCompact f := inferInstance
    exact ⟨(QuasiCompact.isCompact_preimage (f := f) _ isOpen_univ isCompact_univ)⟩
  obtain ⟨ι, _, U, hU, hUtop⟩ :=
    GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X) (W := ⊤) isCompact_univ
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hsep : X.IsSeparated := by
    have e : terminal.from X = f ≫ terminal.from _ := terminal.hom_ext _ _
    exact ⟨by rw [e]; infer_instance⟩
  have hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) :=
    (GlobalTheory.cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsep) ι U hU
  have hcov : ⨆ i, U i = ⊤ := hUtop.symm
  haveI : IsAffineHom π₁ := MorphismProperty.of_isPullback h₁.flip inferInstance
  haveI : IsAffineHom π₂ := MorphismProperty.of_isPullback h₂.flip inferInstance
  obtain ⟨hc₁, hi₁⟩ := affine_cover_preimage_of_isAffineHom π₁ U hcov hint
  obtain ⟨hc₂, hi₂⟩ := affine_cover_preimage_of_isAffineHom π₂ U hcov hint
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  haveI : IsFiniteQC (LB.toMod M) :=
    GlobalTheory.QCoh.isFiniteQC_iff_isFiniteType.2 ⟨inferInstance, GlobalTheory.LB.isFiniteType_toMod hM⟩
  have hfin : ∀ p : ℕ, Module.Finite R ((cechLB f M U).homology p) := by
    intro p
    letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
    have e := ((HomologicalComplex.homologyFunctor _ _ p).mapIso
      (FieldChangeInter.cechIso f M U)).toLinearEquiv.trans (cechHEquivCoh R hcov hint (LB.toMod M) p)
    haveI := GlobalTheory.ProperFinite.finite_coh_of_isProper f (LB.toMod M) p
    exact Module.Finite.equiv e.symm
  obtain ⟨K, φ, hKz, hKfin, -, hKproj, -, -, hKq⟩ :=
    exists_finite_projective_complex_quasiIso (cechLB f M U) (Fintype.card ι)
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X f M U hp.le)
      (fun p => GlobalTheory.AbLaw.flat_cechLB_X f hM hint p) hfin
  haveI : ∀ i, Module.Finite R (K.X i) := hKfin
  haveI : ∀ i, Module.Projective R (K.X i) := hKproj
  have hsemi := GlobalTheory.semicontinuity_finite_projective_complex K (Fintype.card ι) hKz
  have hV := fun p => hsemi.1 q p
  have hus := hsemi.2.1 q
  have step : ∀ {κ : Type} [Field κ] (g : R →+* κ) (Y : Scheme.{0}) (fY : Y ⟶ Sp κ) (π : Y ⟶ X),
      IsPullback π fY f (spMap g) → (⨆ i, π ⁻¹ᵁ U i = ⊤) →
      (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i)) →
      (Subsingleton (coh (LB.toMod (M.pull π)) q) ↔
        Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology q)) := by
    intro κ _ g Y fY π h hc hi
    obtain ⟨e1⟩ := nonempty_cechLB_homology_equiv_coh fY (LB.isLB_pull hM π) hc hi q
    have e2 := (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (GlobalTheory.AbLaw.cechLBBaseChangeIso hM h hint)
    letI : Algebra R κ := g.toAlgebra
    haveI : QuasiIso (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) := hKq κ
    have e3 := asIso (HomologicalComplex.homologyMap (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) q)
    exact ((e3.toLinearEquiv.toEquiv.trans e2.toLinearEquiv.toEquiv).trans e1).subsingleton_congr.symm
  have k1 := (fibre_lemma_2 K q hV g₁).1 ((step g₁ X₁ f₁ π₁ h₁ hc₁ hi₁).1 hsub)
  refine (step g₂ X₂ f₂ π₂ h₂ hc₂ hi₂).2 ((fibre_lemma_2 K q hV g₂).2 ?_)
  have hspec : (⟨RingHom.ker g₂, RingHom.ker_isPrime g₂⟩ : PrimeSpectrum R) ⤳
      (⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hker
  have h0 : (fun p : PrimeSpectrum R => Module.finrank p.asIdeal.ResidueField
      ↑((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q)) ⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ < 1 := by
    simp only [k1]; exact Nat.zero_lt_one
  have hlt := ((hus _ 1 h0).filter_mono hspec.nhds_le_nhds).self_of_nhds
  exact Nat.lt_one_iff.1 hlt

end GlobalTheory.SemicontLB
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → RelSnc f d L σ → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) := by
  intro R R' _ _ φ X X' f f' π d s L σ hpb h
  refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (h.isLB i) π, fun x => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (π.base x)
  obtain ⟨C', hC'⟩ := sncChart_baseChange R R' φ X X' f f' π d s L σ C hpb
  exact ⟨C', by rw [hC']; exact hC⟩

end GlobalTheory.LogPair
end

section
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]

end GlobalTheory
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem vanishing_charZero_fibre_of_finiteType : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  intro R k _ _ _ φ X X' f f' π d _ _ hR hφ hpb s L σ h K M A hM hA r b hAmp hr hb hrel q hq
  haveI : IsDomain R := Function.Injective.isDomain φ hφ
  haveI : CharZero R := (RingHom.charZero_iff hφ).mpr inferInstance
  haveI := hR
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI hstab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Flat f := inferInstance
  let KR := FractionRing R
  let ι : KR →+* k := IsFractionRing.lift hφ
  have hφι : φ = ι.comp (algebraMap R KR) := by
    ext x
    simp [ι, IsFractionRing.lift_algebraMap]
  have hsp : spMap φ = spMap ι ≫ spMap (algebraMap R KR) := by
    rw [hφι]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have hAπ : (A.pull π).IsLB := LB.isLB_pull hA π
  have hrelK' : Out.RelAmple (Over.mk f') (A.pull π) :=
    haveI : IsProper (Over.mk f').hom := (inferInstance : IsProper f')
    (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f') hAπ).mpr hAmp
  have hgenPb := IsPullback.of_hasPullback f (spMap (algebraMap R KR))
  have hA1 : (A.pull (pullback.fst f (spMap (algebraMap R KR)))).IsLB := LB.isLB_pull hA _
  have hgen : Out.RelAmple (Over.mk (pullback.snd f (spMap (algebraMap R KR))))
      (A.pull (pullback.fst f (spMap (algebraMap R KR)))) :=
    FibreAmple.relAmple_of_fieldExtension hA ι hgenPb (hsp ▸ hpb) hA1 ((cls_eq_iff hA1 hA1).mp rfl) hrelK'
  obtain ⟨a, ha, hspread⟩ := AmpleSpread.relAmple_spread R KR (Over.mk f) A ‹IsProper f› hA hgen
  obtain ⟨p, hp, hdp, χ, hχ⟩ := exists_ringHom_zmod_prime_sq_isUnit_of_finiteType R hR a ha d
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hY := IsPullback.of_hasPullback f (spMap χ)
  haveI : SmoothOfRelativeDimension d (pullback.snd f (spMap χ)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hY inferInstance
  have h1 := IsPullback.of_hasPullback (pullback.snd f (spMap χ)) (spMap c)
  haveI : SmoothOfRelativeDimension d (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h1 inferInstance
  haveI : IsProper (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) := inferInstance
  have hsp2 : spMap c ≫ spMap χ = spMap (c.comp χ) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hρ : IsPullback (pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ))
      (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) f (spMap (c.comp χ)) :=
    hsp2 ▸ h1.paste_horiz hY
  set ρ := pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ) with hρdef
  set f₁ := pullback.snd (pullback.snd f (spMap χ)) (spMap c) with hf₁
  have hspec := hspread (ZMod p) (c.comp χ) (hχ.map c)
  have hid : spMap (RingHom.id (ZMod p)) ≫ spMap (c.comp χ) = spMap (c.comp χ) := by
    simp [spMap]
  have hAρ : (A.pull ρ).IsLB := LB.isLB_pull hA ρ
  have hamp1 : Out.RelAmple (Over.mk f₁) (A.pull ρ) :=
    FibreAmple.relAmple_of_fieldExtension hA (RingHom.id (ZMod p)) hρ
      (hid.symm ▸ IsPullback.of_hasPullback f (spMap (c.comp χ))) hAρ ((cls_eq_iff hAρ hAρ).mp rfl) hspec
  haveI : IsProper (Over.mk f₁).hom := (inferInstance : IsProper f₁)
  have hampX : IsAmpleLB (A.pull ρ) := (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hAρ).mp hamp1
  have hproj : IsProjOver f₁ := (isProjOver_iff_isProper_and_exists_isAmpleLB f₁).mpr ⟨inferInstance, _, hampX⟩
  have hL := LogPair.relSnc_baseChange R (ZMod (p ^ 2)) χ X _ f _ _ d s L σ hY h
  let K₁ : CanonLB f₁ d := CanonLB.baseChange hρ K
  have hMρ : (M.pull ρ).IsLB := LB.isLB_pull hM ρ
  have hrel1 : r • cls (M.pull ρ) hMρ = r • cls K₁.bundle K₁.isLB +
      ∑ i, b i • pull (pullback.fst (pullback.snd f (spMap χ)) (spMap c))
        (cls ((L i).pull (pullback.fst f (spMap χ))) (LB.isLB_pull (h.isLB i) _)) + cls (A.pull ρ) hAρ := by
    have e := congrArg (pull ρ) hrel
    simp only [map_add, map_nsmul, map_sum] at e
    have eK : cls K₁.bundle K₁.isLB = pull ρ (cls K.bundle K.isLB) := cls_pull K.isLB ρ K₁.isLB
    rw [cls_pull hM ρ, eK, cls_pull hA ρ]
    convert e using 4
    rw [cls_pull (h.isLB _) _, ← pull_comp]
  have hvan := charp_vanishing_liftable p _ _ (pullback.snd f (spMap χ)) f₁
    (pullback.fst (pullback.snd f (spMap χ)) (spMap c)) d h1 hproj hdp s
    (fun i => (L i).pull (pullback.fst f (spMap χ))) (fun i => Cartier.secPull (σ i) _) hL K₁
    (M.pull ρ) (A.pull ρ) hMρ hampX r b hr hb hrel1 q hq
  have hker : RingHom.ker φ ≤ RingHom.ker (c.comp χ) := by
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact SemicontLB.subsingleton_coh_pull_of_ker_le R X f M hM (ZMod p) k (c.comp χ) φ _ X' f₁ f' ρ π hρ hpb hker q hvan

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.kawamata_viehweg_spreading : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  atlas_forward_decl _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType
end
