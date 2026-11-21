import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonzeroIndexPlacesReferenceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLtGrpTrue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsOfMultiplicityEqualStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharWSeedStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw



end GlobalTheory.Mem.R3.Rw

end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

theorem seeds_uniform_exists : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ),
    ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P,
      (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  classical
  intro K P f F
  have key : ∀ c : (Fin 2 → 𝓞 P.host.E) × (P.Word → 𝓞 P.host.E), ∃ (S : Finset ℕ) (S₂ : Finset ℂ),
      (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ Y : PreX P, (Y.piG, Y.piT) = c → (∃ F₀, SeedW K P f F F₀ Y Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ Y (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
    intro c
    by_cases hc : ∃ (X : PreX P) (F₀ : IntermediateField ℚ ℂ), (X.piG, X.piT) = c ∧ SeedW K P f F F₀ X Set.univ ⊤
    · obtain ⟨X, F₀, hX, hs⟩ := hc
      obtain ⟨S, S₂, hS₂, hb⟩ := seedW_bound hs
      refine ⟨S, S₂, hS₂, fun Y hY _ => ⟨F₀, ?_⟩⟩
      have e := hX.trans hY.symm
      exact seedW hb (congrArg Prod.fst e) (congrArg Prod.snd e)
    · exact ⟨∅, ∅, by simp, fun Y hY ⟨F₀, hs⟩ => absurd ⟨Y, F₀, hY, hs⟩ hc⟩
  choose S S₂ hS₂ hS using key
  have hfin := finite_gens P
  refine ⟨hfin.toFinset.biUnion S, hfin.toFinset.biUnion S₂, ?_, fun Y hs => ?_⟩
  · intro z hz
    obtain ⟨c, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS₂ c z hz
  · have hm : (Y.piG, Y.piT) ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨Y, rfl⟩
    obtain ⟨F₀, h⟩ := hS _ Y rfl hs
    refine ⟨F₀, h.mono ?_ (IntermediateField.adjoin.mono _ _ _ ?_)⟩
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)

end GlobalTheory.Mem.R3.Rw.Resize

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_normalisedAdelicSeeds : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ), ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P, (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) → ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff (algebraMap ↥D'.LL0 D'.what₂.LL).injective).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placesOverFixedField_same_coefficient_place : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  atlas_forward_decl GlobalTheory.Mem.Top.Bl.below_of_overOne
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.UntwSat

theorem stepW_seed_fixed : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      (∃ F₀, SeedW K B.toPre f B.KsC F₀ px Set.univ ⊤) → ∃ F₀, SeedW K B.toPre f B.KsC F₀ px ↑T.pl B.fixedCoefficientFieldInComplex := by
  refine evG_all fun K => ?_
  choose S S₁ hS₁ hS using GlobalTheory.T.exists_uniform_normalisedAdelicSeeds K
  refine ⟨fun P f F => S₁ P f F, fun P f F _ => S P f F ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun _ _ _ _ _ => ∅, fun P f F => hS₁ P f F, by simp, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => ?_⟩
  obtain ⟨F₀, h⟩ := hS _ _ _ px hs
  refine ⟨F₀, h.mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.1 z hz

theorem isBaseEnlargementFixedCoefField_of_same_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hLL : B₀.LLC ≤ B.fixedCoefficientFieldInComplex) : Enl0 B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, -, rfl⟩
    exact (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (B.fixedField_le_coefficientField (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩)))

theorem dat_saturated_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧
        DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧
        (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧
        ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep).and stepW_seed_fixed).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨F₀, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, -, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ :=
    hsd w.px ⟨_, hs⟩
  have hE : Enl0 B₀ B := isBaseEnlargementFixedCoefField_of_same_fields hB₀ hKs hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  have hsub : ∀ x : (w₀.D Z₀).what₂.LL, ∃ y ∈ (w.D Z).LL0, (w.D Z).what₂.embLL y = (w₀.D Z₀).what₂.embLL x :=
    fun x => (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine', ?_, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl
  · intro v₁ v₂ hov hv₁
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).1 hv₁ with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v₁
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v₁ hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).2 (Or.inl h))
      have hB₂ := GlobalTheory.T.placesOverFixedField_same_coefficient_place (w₀.D Z₀) (w.D Z) hsub v v₁ v₂ hov hB
      have hv₂ := (hExt.W1 v v₂ hB₂).1 hv
      rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).1 hv₂ with h₂ | h₂
      · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inl h₂)
      · obtain ⟨j, y, -, hne⟩ := h₂
        exact absurd rfl hne
    · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inr (GlobalTheory.Mem.SatForced.mem_W1F_of_overOne K (w.D Z) v₁ v₂ hov h))

end GlobalTheory.Mem.R3.Rw.UntwSat

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteSpaces_standard_and_large : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  first | exact @GlobalTheory.Mem.StdSize.vstd_size_ev | exact GlobalTheory.Mem.StdSize.vstd_size_ev | (intros; apply GlobalTheory.Mem.StdSize.vstd_size_ev <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

open Formalism.L2.Pj GlobalTheory.AtMember

namespace GlobalTheory.Mem.R3.Rw

theorem selHalf_of_pin {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (p : ColPin w) : SelHalf w.I := by
  intro a b P hP P' hP' hq
  obtain ⟨q, hq, hqP, hqP'⟩ := hq
  obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
  obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
  have hab : ∀ v, (w.I.sel v).under (𝓞 B.host.F) = v := fun v => by
    have h := p.above v
    unfold Formalism.L2.Host.aboveF at h
    rw [Set.Finite.mem_toFinset] at h
    exact h
  have hmem : ∀ v, ((q : 𝓞 B.host.E) ∈ (w.I.sel v).asIdeal) → (q : 𝓞 B.host.F) ∈ v.asIdeal := fun v h => by
    rw [← hab v]
    show (q : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal.comap (algebraMap _ _)
    rw [Ideal.mem_comap, map_natCast]
    exact h
  have := p.half v v' q hq (hmem v hqP) (hmem v' hqP')
  exact congrArg HeightOneSpectrum.asIdeal this

theorem isIdG_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl

set_option maxHeartbeats 4000000 in

theorem datExS_evLg (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.CasselmanWallach) (h5 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h6 : GlobalTheory.Published.DiscreteSeriesExists)
    (h7 : GlobalTheory.Published.HarishChandraFinite) :
    EvLg fun K B f T => ∀ w : ColW B f T, Pinned K B f T w → ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f →
      R3.GrpAt (w.st Z) w.I → Formalism.L2.Theta.VolTieG (w.D Z) →
      ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
    (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.T.eventually_definiteSpaces_standard_and_large GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))
  rintro K ⟨hK, hKC, hO⟩
  refine hO.imp ?_
  rintro B f T hOv hOB w ⟨pin⟩ Z hX _ hgrp hVol
  set X : Stages := w.st Z with hXd
  set I := w.I with hId
  set Wt : Set B.places.Pl := {v | B.places.resChar v ∈ T.pl} with hWt
  obtain ⟨hHH, -, -, hPos, hStd, hX', -, -⟩ := hK X hOv
  obtain ⟨hVS, hnV⟩ := hKC X hOv
  have hok := w.ok
  have hC := w.C_eq
  have hrange := w.xi_range
  have hsel : SelHalf I := selHalf_of_pin pin
  have hfin : Wt.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B T.pl
  have hconj : ∀ v ∈ Wt, B.places.conj v ∈ Wt :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f ≤ B.KsC := (GlobalTheory.Mem.Base.KsExact.lower w.exact).2.2.1
  have hval : Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) := w.val _ _ _ _ _ _
  obtain ⟨C, alg, hPin, hCe, hCL, hCK, hCE, hLJ, hAT, hVal, hmu⟩ := GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one X f hch hval hVol
  have hLC := hPin.laws
  have hpb := hPin.pb
  obtain ⟨hVals, hOk3⟩ := hOB w.px I hX hok hC hrange
  have hrange' : Set.range I.xi = T.set I.C := by rw [hC]; exact hrange
  obtain ⟨Xg, tr₀, R₀, cG, hLev, hIdG, hGood, hMu, hIdem, hPre0, hIn, hTup, hAll, hKeep, hBrg⟩ :=
    GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices X w.px I hX T Wt C.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hX' hPos hCK hCE
      (fun L hL hLC' => hmu _ L _ hL (hLC'.trans (by rw [hC])))
  have hValR : Formalism.L2.Host.ValLL X.toD7 R₀.C := by rw [hLev.C, hC]; exact hVal
  have hpbR : C.pb = R₀.C.P.pb := by rw [hLev.C, hC]; exact hpb
  have hExAt : ∀ R : RealDat X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀).A C.Q.c.F,
      R.Pre1 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt :=
    fun R hP hc ht _ _ => GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 X.toD7 _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht
  have hfinT : Finite (TupU I (usedOf I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))).1 ∨ τ ∈ tuOf I (usedOf I T Wt)} : Set _).Finite :=
      (Set.finite_singleton _).union (tuOf I (usedOf I T Wt)).finite_toSet
    exact hs.to_subtype
  have hGeoEx := GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne h3 X.toD7 _ _ _ _ _ C (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 hVol hLJ hLC hAT
    hfinT hVS hnV
  obtain ⟨tr, dict, mu, chiW, x₀, cE, R, cG', hPins, hEx, hLevEq, hEG, hCG, -, hmuEq, htw, hBrgI, hGeo⟩ :=
    GlobalTheory.StandardWeightCharacter.charW_seed_std X w.px I hX (usedOf I T Wt) Xg tr₀ C R₀ cG (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 X.toD7) hIdem hExAt hGeoEx
      hValR hpbR hPre0 hIn hTup hAll hKeep
  have hPg : R.Pg = R₀.Pg := congrArg LevCh.Pg hLevEq
  have hRC : R.C = R₀.C := congrArg LevCh.C hLevEq
  have hgood : GoodSet X (px := w.px) (R.eG.trans cG') Xg := by
    rw [trans_eq_of_heq' X R.eG R₀.eG cG' cG hPg hEG hCG]; exact hGood
  let z : Dat X I hX T Wt :=
    { Xg := Xg, tr := tr, core := GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE,
      alg := inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL), alg_eq := hCe, R := R, cG := cG', geo := hGeo.some,
      pins := hPins, lev := by rw [hLevEq]; exact hLev, idG := isIdG_of_heq' X R.eG R₀.eG hPg hEG hIdG, good := hgood,
      mu := by rw [hmuEq, htw]; exact hMu, fieldValues_mem_fixedField := hCL, Ks_le := hCK }
  have hch' := hPins.char
  have hPre : GlobalTheory.RealGeo.PreChar R.toRealDat :=
    ⟨hch'.base.lev, hch'.base.grp.red_R, hch'.base.grp.red_L, hch'.base.grp.record, hch'.base.fam, hch'.base.models,
      RealDat.chain_of_weak hch'.base.chain hEx, RealDat.thP_of_weak hch'.base.thP hEx⟩
  have hP : CorePin (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE).toCore (Fr.at X f).P.pb :=
    hPin.reCore hGeo.some.fw.laws.toLawsM
  refine ⟨z, hEx, ?_, ⟨hP.laws, hP.canon, hP.rank, hP.pb⟩, hBrgI hBrg⟩
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral h3 X.toD7 _ _ _ _ (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) R.toRealDat
    (fun _ => 1) hGeo.some hPre hch'.base.grp.chiW (by show C.pb = _; rw [hRC]; exact hpbR) hnV).1

theorem datExS_of_harishChandra_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → DatExS :=
  fun h1 h2 h3 h4 h5 h6 h7 =>
    GlobalTheory.Mem.Top.GroupRetwisting.Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg (datExS_evLg h1 h2 h3 h4 h5 h6 h7))

end GlobalTheory.Mem.R3.Rw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExS := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.Mem.R3.Rw.Bare

set_option maxHeartbeats 4000000 in

theorem hasBare_sat : HypA → HypH → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  intro hA hH hE
  have holdsW : WeightCaseCondition := GlobalTheory.T.weight_set_residue_characteristic hH.h1 hH.h2 hH.h3 hH.multW
  have holdsL : LowerUnitaryCaseCondition := GlobalTheory.T.holds_of_multiplicity_equal hH.h1 hH.h2 hH.h3 hH.multL
  have datS : DatExS := GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have hW := GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field hH.h1.q12 datS holdsL hE
  have hPr := GlobalTheory.T.constructionStartingChoices_of_fine_adelicData hA.a8 hA.a9 hA.a10 hA.a6 holdsW
  have pS : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have iS : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have s1 : StepW Start fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) := by
    refine (iS.and ((pS.trans hW).and hPr)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
    obtain ⟨⟨hPin, hSupp, -⟩, hU, hP⟩ := h
    by_cases hT : T = TwDat.untw B T.pl
    · obtain ⟨Z, hX, z, g, gr, ga, ka, hF, hsub, hpsi, hsat⟩ := hU hT
      obtain ⟨P, hZ, hWt, -⟩ := hP Z hX z g gr ga ka hF hsub hpsi
      refine ⟨hPin, P, fun _ => ?_⟩
      rw [hWt, hZ]
      exact hsat
    · rcases hSupp with h | hG
      · exact absurd h hT
      obtain ⟨Z, hX, z, g, gr, ga, ka, ex, ig, core, std, hsub, hpsi⟩ := hG
      obtain ⟨P, -, -, -⟩ := hP Z hX z g gr ga ka ⟨ex, ig, core, std⟩ hsub hpsi
      exact ⟨hPin, P, fun h => absurd h hT⟩
  have hQ : StepW (fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt)) (pinAnd HasPk) :=
    StepW.of_all fun _ _ _ _ _ _ _ h => ⟨h.1, ⟨h.2.choose⟩⟩
  refine s1.trans ((StepW.of_all fun _ _ _ _ _ _ _ h => h).and (hQ.trans GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep) |>.trans
    (StepW.of_all fun K B f T w hO _ h => ?_))
  obtain ⟨⟨-, P, hsat⟩, hN⟩ := h
  obtain ⟨N, hEm, hG, hN⟩ := hN P
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk B w.C (Gc B w.px) P.q.p P.q.e P.q.W₀ P.q.n (fun _ _ => 0)
    (fun _ _ => le_rfl) (frames_unit P.q.t) (fun u => ((w.C.fm u).lat 0).L) (fun _ => 0) (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l P.hX) (rows_le P.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hA.a8 hA.a9 hA.a10 hA.a6 K B f T w P ⟨_, _, V, S, N, P.Z₀.G⟩
    ⟨hV, hG, (hN V S P.Z₀.G).1, (hN V S P.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  refine ⟨P, x, hsat, ?_⟩
  exact Eq.mpr (congrArg (fun o : P.q.Over => IsEmpty o.N.nd.Loc ∧ ∀ j v, o.η j v = 0) hx) ⟨hEm, fun _ _ => rfl⟩

end GlobalTheory.Mem.R3.Rw.Bare
end
