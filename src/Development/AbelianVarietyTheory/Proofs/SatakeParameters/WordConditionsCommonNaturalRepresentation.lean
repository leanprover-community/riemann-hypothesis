import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), Br.DegW nbr i w hw := by
  first | exact @GlobalTheory.bridge_degW | exact GlobalTheory.bridge_degW | (intros; apply GlobalTheory.bridge_degW <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_of_isSubOfSums : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hJ hRd T hT
  have hO := GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL
  have hW := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR
  have hjump : ∀ a τ, Over W τ a →
      JumpsInV (P.PD K) T.ρ τ {u | u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))} := fun a τ hτ =>
    GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) T.ρ Ms τ _ hT
      (fun x => hJ.jumps x τ (g a) (hRd τ a hτ))
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.CrysSub.isCrys_of_isSubOfSums (P.PD K) hF hO (GRep.ofLat T) Ms hJ.cont hT hJ.crys
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).1
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).2

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.fits_of_isSubOfSums
end

section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hc : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil a).restrictScalars Qp).subtype).comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil (a + 1)).restrictScalars Qp).subtype := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    rfl
  exact ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y,
    LinearMap.congr_fun hc y⟩

theorem fildR_succ_le (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_DdR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a ≤ DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero_of_jump (ρ : Representation LL G V) [Module.Finite LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : multV PD ρ τ a ≠ 0 := by
  intro h0
  apply h
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_DdR PD ρ τ a)
  refine Submodule.eq_of_le_of_finrank_eq (fildR_succ_le PD ρ τ a) ?_
  unfold multV at h0
  omega

end General

theorem jump_multV_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL),
    Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  intro l _ P K LL T hF τ u hJ
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hfin, -⟩, -⟩ := hF ↥LL.1 ↥(OL LL) (GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL) A
  haveI : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) := hfin
  exact multV_ne_zero_of_jump (P.PD K) T.ρ τ u hJ

end GlobalTheory.HTW.Rec
end
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL), Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  atlas_forward_decl GlobalTheory.HTW.Rec.jump_multV_ne_zero
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.fits_lowCount_of_matRep
end

section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_S_eta_m : ∀ {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), ((pageWord L j ε τ φ).S : ℝ) ≤ L.Sc ∧ ((pageWord L j ε τ φ).η : ℝ) ≤ L.etaSz + D.R.t + 2 ∧ (pageWord L j ε τ φ).m = D.R.m := by
  intro D L j ε τ φ
  refine ⟨?_, ?_, rfl⟩
  · exact Nat.floor_le L.Sc_pos.le
  · have h := Nat.floor_le L.etaSz_pos.le
    show ((⌊L.etaSz⌋₊ + D.R.t + 2 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

end GlobalTheory.HTW
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordNum : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨rfl, hg⟩ := hO
  generalize g 0 = τ at hg
  obtain rfl : g = letter τ ψ := funext hg
  have hsm := pageWord_S_eta_m L j ε τ ψ
  refine ⟨?_, ?_, ?_, hsm.1, hsm.2.1, rfl⟩
  · intro a
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a
    rcases GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ ψ hR a with h | h
    · exact Or.inl (hth.2 h)
    · refine Or.inr ?_
      have h' : (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) ≤ ((wHat D : ℕ) : ℤ) := by
        rw [hsz]; exact h
      exact_mod_cast h'
  · have h := bHat_add_etaHat_add_sHat_le_hPage L C hR
    exact h
  · exact (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).2

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordNum_recWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.recWord_wordNum
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocalFrobeniusOrbit

theorem norm_algHom_eq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} [Fact l.Prime]
    (c ρ : E →+* PadicAlgCl l) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ρ x = c (g x) := by
  let Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l) := fun g => c.toRatAlgHom.comp g.toAlgHom
  have hinj : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh
    exact c.injective this
  have hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := hbij.2 ρ.toRatAlgHom
  exact ⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩

theorem embeddings_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  intro R H l _ h2 hq hd c K hc hcl P _ _ s hs
  haveI hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hN0 : ¬ l ∣ H.condN := by
    rw [H.dvd_condN_iff_small Fact.out]; tauto
  have hF := H.der.frob l hN0
  have hco : Nat.Coprime l H.condN := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l H.E c
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI := v.isPrime
  haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)
  have hsv : IsArithFrobAt ℤ s v.asIdeal := (H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)
  have hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ
    rw [((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]
    exact Subgroup.npow_mem_zpowers s k
  have hord : orderOf s = orderOf (H.galE s) :=
    (H.gal.orderOf_eq s).symm
  set N := orderOf (H.galE s) with hN
  have hNpos : 0 < N := hord ▸ orderOf_pos s
  haveI : NeZero N := ⟨hNpos.ne'⟩
  refine ⟨?_, ?_⟩
  · have hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c) := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' l H.E c K.1 hc K.2 hcl
    have hdeg := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group l H.E c v hv
    rw [← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]
  · intro τ
    let ρ : H.E →+* PadicAlgCl l := (τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)
    obtain ⟨g, hg⟩ := exists_aut_comp c ρ
    have hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩ := fun x => rfl
    have hgs : g ∈ Subgroup.zpowers s := by
      rw [← hstab]
      refine Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)
      rw [hv, hv]
      have h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩ := by
        rw [← hρx, hg]; rfl
      rw [h1, norm_algHom_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgs
    have hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ)) := fun j => (zpow_natCast s j.val).symm
    refine ⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩
    · rw [← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
    · have hgj : g = s ^ j.val := by
        refine AlgEquiv.ext fun x => c.injective ?_
        rw [← hg, hρx, hj]
      apply ZMod.val_injective
      have h3 : s ^ j.val = s ^ (k : ZMod N).val := by
        rw [← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
      have h4 := pow_inj_mod.1 h3
      rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h4
      exact h4

end GlobalTheory.LocalFrobeniusOrbit
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_embeddings_single_frobenius_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  atlas_forward_decl GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobPeriod

theorem norm_int_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := map_isIntegral_int c x.isIntegral_coe
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_comp_of_normal {E L : Type} [Field E] [Field L] [CharZero E] [CharZero L]
    [Normal ℚ E] (φ ψ : E →+* L) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E L := φ.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x).symm

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (h : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (algebraMap ℤ (𝓞 E) (l : ℤ)) ∈ v.asIdeal
  simpa using h

theorem card_quot_under {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (Q : Ideal (𝓞 E)) [h : Q.LiesOver (Ideal.span {(l : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = l := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

end GlobalTheory.FrobPeriod

open GlobalTheory.FrobPeriod in

theorem GlobalTheory.FrobPeriod.periodFrob_restrict : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  intro D l _ P K c h2 hq hd x y hy
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let c' : D.host.E →+* PadicAlgCl l := K.1.val.toRingHom.comp c
  have hK : ∀ z, c' z ∈ K0 K := fun z =>
    IntermediateField.mem_inf.2 ⟨(c z).2, GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified D.host l h2 hq hd c' z⟩
  let c0 : D.host.E →+* ↥(K0 K) := c'.codRestrict (K0 K) hK
  have hc0 : ∀ z, ((c0 z : ↥(K0 K)) : PadicAlgCl l) = c' z := fun z => rfl
  have hyx : y = c0 x := Subtype.ext (congrArg (fun t : ↥K.1 => (t : PadicAlgCl l)) hy)
  let σ0 := (P.PD K).σ
  obtain ⟨g, hg⟩ := exists_comp_of_normal c0 ((σ0 : ↥(K0 K) →+* ↥(K0 K)).comp c0)
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l D.host.E c'
  haveI := liesOver_of_mem l v hvl
  have hgl : ∀ z : 𝓞 D.host.E, g • z - z ^ l ∈ v.asIdeal := fun z => by
    refine (hv _).2 ?_
    have h := P.PD_σ K (c0 z) (by rw [hc0]; exact norm_int_le_one c' z)
    have e : ((g • z - z ^ l : 𝓞 D.host.E) : D.host.E) = g (z : D.host.E) - (z : D.host.E) ^ l := by
      push_cast
      rfl
    rw [e, map_sub, map_pow, ← hc0, ← hc0, ← hg]
    exact h
  set F := D.host.sigmaOf (DV.frobG D l) with hFdef
  have hF : ∀ z : 𝓞 D.host.E, F • z - z ^ l ∈ v.asIdeal := fun z => by
    have h := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 v.asIdeal z
    rw [card_quot_under l v.asIdeal] at h
    exact h
  have hin := (D.host.der.frob l hlN v.asIdeal).2.2.2
  have hgF : g * F⁻¹ = 1 := by
    refine (hin _).1 fun z => ?_
    have h := v.asIdeal.sub_mem (hgl (F⁻¹ • z)) (hF (F⁻¹ • z))
    have e : (g * F⁻¹) • z - z = g • F⁻¹ • z - (F⁻¹ • z) ^ l - (F • F⁻¹ • z - (F⁻¹ • z) ^ l) := by
      rw [mul_smul, smul_inv_smul]
      ring
    rw [e]
    exact h
  have hgF' : g = F := by simpa using mul_inv_eq_one.1 hgF
  subst hyx
  apply Subtype.ext
  change (((σ0 (c0 x) : ↥(K0 K)) : PadicAlgCl l)) = c' (F x)
  have := hg x
  simp only [RingHom.comp_apply] at this
  rw [show (σ0 (c0 x)) = c0 (g x) from this, hc0, hgF']
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodDatum_frobenius_restrict_hostField : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  atlas_forward_decl GlobalTheory.FrobPeriod.periodFrob_restrict
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem reads_orbit_invFrob : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  intro D l _ P K LL W c κ h2 hq hd hcl hK
  set φ := DV.frobG D l with hφ
  set n := Module.finrank ℚ_[l] ↥(K0 K) with hn
  have hτ := fun a => GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  have hg := fun τ => GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host K LL c κ τ
  let τa : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := fun a => (hτ a).exists.choose
  have hover : ∀ a, Over W (τa a) a := fun a => (hτ a).exists.choose_spec
  let g : ZMod n → D.R.GG := fun a => (hg (τa a)).exists.choose
  have hread : ∀ a, Reads D.host c κ (τa a) (g a) := fun a => (hg (τa a)).exists.choose_spec
  have smul : ∀ u v : D.R.GG, D.host.sigmaOf (u * v) = D.host.sigmaOf u * D.host.sigmaOf v :=
    fun u v => map_mul (D.host.gal).symm u v
  have hK0 : K0 K = K.1 := inf_eq_left.mpr hK

  have step : ∀ a, g (a + 1) = g a * φ⁻¹ := by
    intro a
    refine (hg (τa (a + 1))).unique (hread (a + 1)) ?_
    intro z
    set x := D.host.sigmaOf φ⁻¹ z with hx
    have hz : D.host.sigmaOf φ x = z := by
      rw [hx, ← AlgEquiv.mul_apply, ← smul, mul_inv_cancel]
      show (D.host.gal).symm 1 z = z
      rw [map_one]; rfl
    let y : ↥(K0 K) := ⟨((c x : ↥K.1) : Om l), ⟨(c x).2, hK (c x).2⟩⟩
    have hy : algebraMap ↥(K0 K) ↥K.1 y = c x := Subtype.ext rfl
    have hσ := GlobalTheory.T.periodDatum_frobenius_restrict_hostField D P K c h2 hq hd x y hy
    have ov : ∀ b (t : ↥(K0 K)), τa b (algebraMap ↥(K0 K) ↥K.1 t) = W.emb b t := by
      intro b t
      have := congrArg (fun f => f t) (hover b)
      simpa using this
    have hemb : W.emb (a + 1) ((P.PD K).σ y) = W.emb a y := by
      have := congrArg (fun f => f y) (W.emb_σ a)
      simpa using this
    calc τa (a + 1) (c z) = τa (a + 1) (c (D.host.sigmaOf φ x)) := by rw [hz]
      _ = τa (a + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y)) := by rw [hσ]
      _ = W.emb (a + 1) ((P.PD K).σ y) := ov _ _
      _ = W.emb a y := hemb
      _ = τa a (algebraMap ↥(K0 K) ↥K.1 y) := (ov _ _).symm
      _ = τa a (c x) := by rw [hy]
      _ = κ (D.host.sigmaOf (g a) x) := hread a x
      _ = κ (D.host.sigmaOf (g a * φ⁻¹) z) := by rw [smul, AlgEquiv.mul_apply]

  have hfr : n = Module.finrank ℚ_[l] ↥K.1 := by
    rw [hn]; exact (IntermediateField.equivOfEq hK0).toLinearEquiv.finrank_eq
  have hlen : n = orderOf φ⁻¹ := by
    rw [orderOf_inv]
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (Ideal.span {(l : ℤ)}) (⊥ : Ideal (𝓞 D.host.E)) (by
        intro x hx
        simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
        have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by simpa using hx)
        rw [this]; exact Ideal.zero_mem _)
    have := hQ
    have : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQc.symm⟩
    have hfrob := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 Q
    let c' : D.host.E →+* PadicAlgCl l := (K.1.val : ↥K.1 →ₐ[ℚ_[l]] Om l).toRingHom.comp c
    have hc' : ∀ x, c' x ∈ K.1 := fun x => (c x).2
    have hcl' : (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c') := hcl
    have := (GlobalTheory.T.completion_embeddings_single_frobenius_orbit D.host l h2 hq hd c' K hc' hcl' Q (D.host.sigmaOf φ) hfrob).1
    have hφg : D.host.galE (D.host.sigmaOf φ) = φ :=
      (D.host.gal).apply_symm_apply φ
    rw [hfr, this, hφg]
  have hpos : 0 < n := by
    rw [hfr]
    have := K.2
    exact Module.finrank_pos
  have : NeZero n := ⟨hpos.ne'⟩
  refine ⟨g, ⟨hlen, ?_⟩, ?_⟩
  · have hk : ∀ k : ℕ, g (k : ZMod n) = g 0 * φ⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, step, ih]
        exact (mul_assoc _ _ _).trans (congrArg _ (pow_succ φ⁻¹ k).symm)
    intro a
    have := hk a.val
    rwa [ZMod.natCast_zmod_val] at this
  · intro τ a h
    have : τ = τa a := (hτ a).unique h (hover a)
    subst this
    exact hread a

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.reads_orbit_invFrob
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia D.nbr i w hw, ?_, GlobalTheory.T.wordNum_recWord L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.wordBase_of_jumpIn
end

section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem one_le_Sc {D : D7} (L : SizeData₂ D) : (1 : ℝ) ≤ L.Sc := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  set τ := D.eTau.symm ⟨plc (1 : D.R.GG), plc_mem 1⟩
  set P := D.hc τ
  have h1 := P.u_gt_v ⟨1, by omega⟩
  have h2 := P.v_gt_u ⟨0, by omega⟩
  obtain ⟨z0, hz0⟩ := P.v_int ⟨0, by omega⟩
  obtain ⟨z1, hz1⟩ := P.v_int ⟨1, by omega⟩
  have c0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have c1 := (L.cloud_v τ ⟨1, by omega⟩).1
  simp only at h1 h2
  have hlt : P.v ⟨1, by omega⟩ < P.v ⟨0, by omega⟩ := lt_trans h1 h2
  rw [hz0, hz1] at hlt
  have hz : z1 < z0 := by exact_mod_cast hlt
  have hz1' : (0 : ℝ) ≤ (z1 : ℝ) := by
    have : (((P.v ⟨1, by omega⟩ : ℚ) : ℝ)) = (z1 : ℝ) := by rw [hz1]; push_cast; rfl
    rw [← this]; exact c1
  have hz0' : (z0 : ℝ) ≤ L.Sc := by
    have : (((P.v ⟨0, by omega⟩ : ℚ) : ℝ)) = (z0 : ℝ) := by rw [hz0]; push_cast; rfl
    rw [← this]; exact c0
  have : (0 : ℤ) ≤ z1 := by exact_mod_cast hz1'
  have : (1 : ℝ) ≤ (z0 : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z0 by omega)
  linarith

theorem recWord_small_pos : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ →
    Small (recWord L j ε g) ∧ 1 ≤ (recWord L j ε g).S ∧ 1 ≤ (recWord L j ε g).η := by
  intro D L C j ε n g ψ hR _
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (1 : D.R.GG) (1 : D.R.GG) hR
  obtain ⟨b1, w1, bw, bη, bS, hsz⟩ := hB
  refine ⟨⟨b1, w1, bw, bη, bS, fun a => ?_⟩, ?_, ?_⟩
  · have hB' := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (g a) (1 : D.R.GG) hR
    have h := hB'.2.2.2.2.2 (0 : ZMod (orderOf (1 : D.R.GG)))
    simp only [pageWord, letter, one_pow, mul_one] at h
    show etaHat L < (szT (hcAt D (g a)) j (pos ε (g a))).toNat
    exact Int.lt_toNat.mpr h
  · show 1 ≤ sHat L
    unfold sHat
    exact Nat.le_floor (by exact_mod_cast one_le_Sc L)
  · show 1 ≤ etaHat L
    unfold etaHat; omega

end GlobalTheory.HTW.Rec
end

section
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem lowCount_eq_smallHodgeTateJumpCountOverLetter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} (W : Wach P K LL)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (η : ℕ) :
    TruncatedSeriesCountingBounds.lowCount W T a η = lowCount W T a η := by
  unfold TruncatedSeriesCountingBounds.lowCount lowCount
  congr 1

theorem recS_wordBase_natural : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i r ρ π w hw Cx hG hR h7 hF hJ hP h2 hq hd
  obtain ⟨ε, κ, hin⟩ := GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  obtain ⟨g, hg, hwb⟩ := GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit L C₀ HW i w hw C hG r ρ π ε κ hR h7 h2 hq hd hin
  refine ⟨ε, g, hg, ?_⟩
  have hsm := GlobalTheory.HTW.Rec.recWord_small_pos L C₀ (liftIdx D i) ε g _ hR hg
  obtain ⟨hdeg, hloc, hnum⟩ := hwb
  refine
    { unram := hloc.unram
      deg := hdeg
      split := hloc.split
      t1 := fun T h => ?_
      t2 := fun T h => ?_
      t2win := fun T h => ?_
      num := hnum
      small := hsm }
  · obtain ⟨h1, h2, h3⟩ := hloc.t1 T h
    exact ⟨h1, h2, h3⟩
  · obtain ⟨⟨h1, _, _⟩, h4⟩ := hloc.t2 T h
    refine ⟨h1, fun ft a => ?_⟩
    rw [lowCount_eq_smallHodgeTateJumpCountOverLetter]
    exact h4 ft a
  · obtain ⟨⟨_, h2, h3⟩, _⟩ := hloc.t2 T h
    exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordConditions_common_natural_representation : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  atlas_forward_decl GlobalTheory.HTW.Rec.recS_wordBase_natural
end
