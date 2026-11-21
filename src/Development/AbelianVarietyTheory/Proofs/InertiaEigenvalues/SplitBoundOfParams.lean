import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RestPt
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointConditionsRangeBoundStatement
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HubXTypePrimeConditions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPointsStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeTwentyFiveMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0WallOfCanon
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TorsionExponentCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWild
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0allCanon
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientConditionsAtGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrCrysAtRangePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TypeUeHalf

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ :=
  fun _ _ _ _ ep τ => GlobalTheory.SplitDecl.embTypeUe_iff ep τ

end GlobalTheory.TypeUeHalf
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  atlas_forward_decl GlobalTheory.TypeUeHalf.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  atlas_forward_decl GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith

open NumberField IsDedekindDomain Module in

theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  first | exact @GlobalTheory.SplitDecl.main | exact GlobalTheory.SplitDecl.main | (intros; apply GlobalTheory.SplitDecl.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem GlobalTheory.AdmissibleCore.main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  intro hC D X hT hA hX i π hπ
  intro hZ
  obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (X.r i π) (X.ρ i π) (D.nd.chi i) e := ⟨e, fun g u => he g u⟩
  have hHG : IsHeckeGalois D.nd i π (X.r i π) := hX.good i π
  have hpt : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (X.ρ i π) := ⟨hX.cont i π, X.r i π, hHG, e, fun g u => he g u⟩
  have hirr := hA i π hπ (X.ρ i π) hpt
  have hLive : GlobalTheory.CoefDuty.Live D.nd i := ⟨π, hZ, X.r i π, X.ρ i π, hHG, hdec, hirr⟩
  obtain ⟨r₀, ρ₀, hg₀, hw₀⟩ := hT i hLive
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hg₀ hw₀ (X.r i) (X.ρ i) (hX.good i) π hZ hdec
  exact ⟨S, hS⟩
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  atlas_forward_decl GlobalTheory.AdmissibleCore.main
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.Assembly

theorem main : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : KillingConditions.RowK) (C : NChoice D) (X : KillingConditions.HubData D) (c : ℝ) (CT : ℕ), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → 1 ≤ L.sc.L → 120 ≤ c → (CT : ℝ) ≤ L.sc.b → AdmissibleParameterJ.AdmJ L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.AdmA D → SumRepresentations.Conclusion41 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionZ D → ResidualIrreducibleRankR D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.CoefDuty.TakenAll D → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → GlobalTheory.HubX.DepthZeroG D → (∀ i, GoodR D.nd i (X.r i)) ∧ (∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes X.r X.ρ ∧ KillingConditions.DataAD L HW X R ∧ GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c ∧ (∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ (∀ i, KillingConditions.RangeAD L X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ hJ : AdmissibleParameterJ.ConclusionJa D, EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ)) ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ (∀ ep, EmbeddingTypes.ambTypeD (D := D) i ep) ∧ (∀ π ∈ D.nd.Zgood i, EmbeddingTypes.UnramifiedTrivialH1f (D := D) i (X.dc i) ∧ EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i) ∧ LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π ∧ ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0) ∧ (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Ce : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Ce.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC Ce (rDuO D.nd i (X.r i) x)))) ∧ KillingConditions.SignatureChoiceCondition X.ρ C ∧ (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U ∧ PairedCharacterCondition.SetSQ i (X.r i)) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro hFB hLF hCh D L HW F R C X c CT hX hPm hL hc hCT hAJ hAP hAA h41 h42 hG5 hZ hRB hOS hTA hNT hTG hST hBC hMU hDZ
  have hJ : AdmissibleParameterJ.JumpConditions L := GlobalTheory.T.statement_J_all D L hAJ
  have hG2 : AdmissibleParameterJ.DeRhamFamilyAway D := hAJ.1
  have htie : SumRepresentations.tie0 D := hAA.1
  have had1 : SumRepresentations.adm1 D := hAA.2.2.1
  have had2 : SumRepresentations.adm2 D := hAA.2.2.2.1
  have had5 : SumRepresentations.adm5 D := hAA.2.2.2.2.2.2
  have hFont : ∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := GlobalTheory.T.fontaineAtPlacesOverL D
  have hfam : GlobalTheory.PtCore.PtFam D X.r X.ρ := hX.fam
  have hcB : ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
    intro i; rw [hX.cB]; exact le_rfl
  have hCl := GlobalTheory.T.joint_conditions_range_bound hFB hLF D HW F L X (fun L' h => GlobalTheory.T.statement_J_all D L' h) hAJ hAP h41 hOS hfam hcB
  have hRes : GlobalTheory.PtCore.ResAbsIrr D := GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred D hRB
  have hGPR : GlobalTheory.PtCore.GoodPtRow D := GlobalTheory.Proof.LocalGlobalAssembly.main D htie h42 hZ
  have hLgc : GlobalTheory.HubX.LgcG D := GlobalTheory.T.local_global_compatibility_all D htie had1 had2 had5
  have hCC := GlobalTheory.HubX.blockAndTorsionExponentBounds_canonicalHubData D L HW R X hX hL c hc
  have hTP := GlobalTheory.hubX_typePrime_conditions D L HW R X hX hPm hJ hAP hG5 hLgc hDZ CT hCT
  refine ⟨hfam.good, GlobalTheory.restPt_atQD hFB D X.r X.ρ hfam h41 hOS,
    GlobalTheory.T.admFon_of_points hFB D L hG2 hJ.1 X.r X.ρ hfam, hX.data, hCC.1, hCC.2,
    GlobalTheory.HubX.jointCond_H0Wall_of_canon hFB D L HW R X hX F hJ h41 hFont,
    GlobalTheory.restPt_of_ptFam hFB D X.r X.ρ hfam h41 hOS, hCl.2.1, ?_,
    GlobalTheory.JointSix.main hCh D C X.r X.ρ hfam hNT hTG hST hGPR hRes, hTP.1, hTP.2⟩
  intro i hTw hg hr hs
  have hsp := GlobalTheory.HubX.SplitDecl.splitRowPrime_of (L := L) (X := X) i hg hr hs
  have hUC := GlobalTheory.HubX.unrCrysAtRangePrime hFB D L X hfam.good htie had2 had5 hG2 hBC hMU i hTw hg hr hs
  refine ⟨fun hJa => (GlobalTheory.HubX.SplitDecl.main D L HW R X hX hJa i hTw hg hr hs).1,
    (GlobalTheory.HubX.SplitDecl.main D L HW R X hX hJ.1 i hTw hg hr hs).2,
    fun ep => GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime D i ep hsp, ?_, hUC.1, hUC.2⟩
  intro π hπ
  have h78 := GlobalTheory.T.ambient_conditions_at_good hFB D L X hG2 hJ.1 hJ.2.2.1 hfam i hg π hπ
  exact ⟨GlobalTheory.T.unramifiedTrivialH1f_of_decl D i (X.dc i), hCl.2.2.1 i hg π hπ, h78.1, h78.2.1, h78.2.2.1, hCl.2.2.2 i π,
    GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live hCh D X hTA hRes hfam i π hπ,
    GlobalTheory.HubX.jointCondH0all_canon hFB D L HW R X hX hJ h41 hFont i hTw hg hr hs π hπ⟩

end GlobalTheory.HubX.Assembly
end
