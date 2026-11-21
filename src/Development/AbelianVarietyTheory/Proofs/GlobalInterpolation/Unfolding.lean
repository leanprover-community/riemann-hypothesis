import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerCompletions
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticesUnramifiedPlaceNoHypothesis

section
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ hμ

end GlobalTheory
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  atlas_forward_decl GlobalTheory.normaliseGroupClause_holds
end

section
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureCompact

theorem compactClause : CompactClause := by
  intro G _ _ _ _ _ _ H _ _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  borelize G
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH.isClosed fun h => ?_
  rw [GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact H hH h.2,
    GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact (⊤ : Subgroup H) (by simpa using isCompact_univ)
      (Subgroup.mem_top h)]

end GlobalTheory.QuotientMeasureCompact
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  atlas_forward_decl GlobalTheory.QuotientMeasureCompact.compactClause
end

section
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique

theorem normaliseQuotientClause : NormaliseQuotientClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _
  obtain ⟨⟨μ₀, hμ₀⟩, huniq⟩ := GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'
  obtain ⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀
  set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dg dg₀
  have hdg : dg = c • dg₀ := isMulLeftInvariant_eq_smul dg dg₀
  have hR : IsInvariantRadon H (c • μ₀) := by
    haveI := hμ₀.finiteOnCompacts
    haveI := hμ₀.invariant
    refine ⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩
    · intro h
      apply hμ₀.ne_zero
      have : c⁻¹ • (c • μ₀) = μ₀ := by
        rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      rw [← this, h, smul_zero]
    · simp only [Measure.coe_nnreal_smul_apply]
      rw [SMulInvariantMeasure.measure_preimage_smul g hs]
  have hF : QuotientFormula H dg ν (c • μ₀) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hF₀ f hf
    refine ⟨h1, ?_⟩
    rw [hdg, lintegral_smul_measure, lintegral_smul_measure, h2]
  refine ⟨c • μ₀, ⟨hR, hF⟩, ?_⟩
  rintro μ ⟨hμ, hμF⟩
  obtain ⟨d, -, hd⟩ := huniq _ _ hR hμ
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hKm : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hKm
  have e1 := (hF _ hfm).2
  have e2 := (hμF _ hfm).2
  rw [hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul] at e2
  have hpos : dg K ≠ 0 := (measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
  have hfin : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hd1 : d = 1 := by
    have : (d : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]; exact e2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp this
  rw [hd, hd1, one_smul]

end GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_normalised_by_haar_unique : NormaliseQuotientClause := by
  atlas_forward_decl GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause
end

section
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
end

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula : NormaliseSubgroupClause := by
  atlas_forward_decl GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause
end

section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left : DiscreteClause := by
  first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)
end

section
section
namespace GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular

theorem quotientMeasures : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures :=
  ⟨GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular, GlobalTheory.T.quotientMeasure_normalised_by_haar_unique, GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula, GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula, GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left, GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space,
    GlobalTheory.T.compactSubgroup_quotient_invariant_measure⟩

end GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  atlas_forward_decl GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures
end

section
noncomputable section

namespace GlobalTheory.Proof.SelfDualStabilizer

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

theorem unramifiedAtFinite_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.UnramifiedAtFinite F E := by
  constructor
  · intro h P hP hne
    exact h ⟨P, hP, hne⟩
  · intro h P
    exact @h P.asIdeal P.isPrime P.ne_bot

section Clauses

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [NumberField F] [NumberField E] in

theorem isSelfDualLattice_iff (L : Submodule (𝓞 E) (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.IsSelfDualLat σ J L := Iff.rfl

omit [NumberField F] [NumberField E] in

theorem perpPart_eq (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.perpPart σ J (L : Set (Fin M → E)) x = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.perpIn σ J L x := rfl

omit [NumberField E] in

theorem stabHat_eq (S : Set (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.stabHat σ J S = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.stabLat (Af F) σ J (latHat F E S) :=
  Subgroup.ext fun _ => Iff.rfl

omit [NumberField E] in

theorem orbitClaims_iff (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims σ J (L : Set (Fin M → E)) x β ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl F E σ J L x β := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl
  rw [stabHat_eq, stabHat_eq, perpPart_eq]
  exact Iff.rfl

end Clauses

theorem stabTransitive_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  refine imp_congr (unramifiedAtFinite_iff F E) ?_
  refine forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ =>
    forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_
  exact forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x =>
    imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β

end GlobalTheory.Proof.SelfDualStabilizer
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  first | exact @GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | exact GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | (intros; apply GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas <;> assumption)
end

section
section
namespace GlobalTheory.StabOrbit

theorem stabTransitive : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive :=
  GlobalTheory.Proof.SelfDualStabilizer.stabTransitive_iff.1 (stabTransitive_of_lemmas GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis)

end GlobalTheory.StabOrbit
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  atlas_forward_decl GlobalTheory.StabOrbit.stabTransitive
end

section
namespace GlobalTheory.UnfoldingObj

theorem unfolding : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D := fun D =>
  (GlobalTheory.UnfoldingCompare.unfolding_iff D).1 (GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer GlobalTheory.T.quotientMeasure_integration_formulas_unimodular GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof GlobalTheory.T.stabSelfDualLattice_transitive_on_length D)

end GlobalTheory.UnfoldingObj
end
