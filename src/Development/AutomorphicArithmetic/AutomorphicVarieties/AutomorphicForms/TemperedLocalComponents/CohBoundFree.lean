import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyRankEqHomologyRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyBoundedEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologySumBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepResolutionExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExtVanishingOfResolutionEndo
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RankCohHomOfRankHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermutationModuleHomologyRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PinsOfClosedSubgroupPadicCharacterInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ProjPermOfLiftEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactBaseIntegralToComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExactCOfOfExactBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PermSplitFinSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AltChainOfPermSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepHomAlternatingSumEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepDimensionBounded
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfDegreeBounded
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfSubgroupBounded
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CoindRetractOfFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOverOfSumBoundCoindRetract
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedCommOfBoundedEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BoundedComplexOfBoundedSimplicialComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedOrbitsFiniteRepresentatives
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicBaseChangeRealPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRealPartInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GoodRealFormOfRealPartOfRealInvolution
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealStructureActionOfRealInvolution
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealSpanOfGoodRealForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalOrbitRepresentatives
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalVectorStabilizerProperty
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbReOfMinimalVectorStabilizer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BddFixOfBoundedComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMIntegralOfExistsCM
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingFixedPointsEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartBoundOfSumBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ShapiroFunctorialOfCoinductionBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitBoundOfShapiroFunctorial
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbsoluteBoundOfPartialBoundOfOrbitBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiberCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiniteOrbitBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardOhatQuotientNatCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelSubgroupIndexBoundOfCardOhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicDoubleCosets
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupLevelOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupsCommensurable

section
open NumberField

open CategoryTheory UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_cx : BddCx := by
  intro Γ I _ _ K hx ho hs
  obtain ⟨hst, D, hD⟩ := UpperTheory.adelic_rep_dimension_bounded Γ I K (ho 1) hs
  obtain ⟨h0, h1, h2⟩ := UpperTheory.exactCOf_of_exactBase UpperTheory.exactBase_integral_to_complex Γ I K hx
  obtain ⟨P, hP, he⟩ := UpperTheory.repResolution_exists Γ (fun p => PC Γ (K.Tup p)) K.d (augC Γ (K.Tup 0))
    (fun p => UpperTheory.projPerm_of_liftEquiv UpperTheory.pins_of_closed_subgroup_padic_character_inv Γ _ (hst p)) h0 h1 h2
  obtain ⟨a0, aD⟩ := UpperTheory.rep_hom_alternating_sum_eq_zero Γ I K
  obtain ⟨e, he1, he2⟩ := he K.alt (by rw [a0, Category.id_comp]) (UpperTheory.altChain_of_permSplit UpperTheory.perm_split_fin_succ Γ I K)
  refine UpperTheory.adelic_rep_bounded_of_degree_bounded Γ (fun q => ?_) ⟨D, fun q hq A => UpperTheory.ext_vanishing_of_resolution_endo Γ P e he1 q (he2 q (aD q (hD q hq))) A⟩
  obtain ⟨c, hc⟩ := UpperTheory.permutation_module_homology_rank Γ _ (ho q)
  exact ⟨c, fun A => (UpperTheory.rankCohHom_of_rankHomology UpperTheory.cohomology_rank_eq_homology_rank Γ P q _ (hP q) A).trans (hc A)⟩

open UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_fix : BddFix :=
  have hg : GoodRe := UpperTheory.good_real_form_of_real_part_of_real_involution UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant
  have ha : ActRe := UpperTheory.real_structure_action_of_real_involution UpperTheory.adelic_realPart_invariant
  have hs : SpanRe := UpperTheory.real_span_of_good_real_form UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant hg
  UpperTheory.bddFix_of_bounded_complex UpperTheory.V.Af.bddArith_cx hg ha hs
    (UpperTheory.orbRe_of_minimal_vector_stabilizer UpperTheory.fixedOrbits_finite_representatives UpperTheory.adelic_realPart_invariant ha hs UpperTheory.minimal_orbit_representatives UpperTheory.minimal_vector_stabilizer_property) UpperTheory.minimal_vector_stabilizer_property

theorem UpperTheory.V.Af.bddArith :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Subgroup.Commensurable Γ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)).range → UpperTheory.V.Af.CohB.Bdd ↥Γ := by
  intro F _ _ hF n Γ hΓ
  have hO : UpperTheory.V.Af.CohB.Bdd (GL (Fin n) (𝓞 F)) := by
    rcases hF with hF | hF
    · exact UpperTheory.bounded_complex_of_bounded_simplicial_complex UpperTheory.V.Af.bddArith_cx F n
    · obtain ⟨L, _, _, _, i, σ, hσ, hi, hf⟩ := UpperTheory.exists_CM_integral_of_exists_CM UpperTheory.exists_CM_extension F
      exact UpperTheory.cohomology_bounded_equiv _ _ (UpperTheory.building_fixed_points_equiv _ _ i σ n hi hf) (UpperTheory.V.Af.bddArith_fix L n σ hσ)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)) := by
    intro g k e
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact RingOfIntegers.coe_injective (congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F) a b) e)
  exact UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv UpperTheory.cohomology_bounded_equiv UpperTheory.adelic_rep_bounded_of_subgroup_bounded (UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract UpperTheory.cohomology_sum_bound UpperTheory.coind_retract_of_finite_index) _ Γ _ hΓ
    (UpperTheory.cohomology_bounded_equiv _ _ ⟨MonoidHom.ofInjective hinj⟩ hO)
end

section
open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.CuspRep CategoryTheory UpperTheory.V.Af UpperTheory.V.Af.CohB

@[reducible] private def act {G H : Type} [Group G] [Group H] (ι : H →* G) (Γ : Subgroup H) (U : Subgroup G) :
    MulAction ↥Γ (G ⧸ U) := MulAction.compHom _ (ι.comp Γ.subtype)

private theorem gen (hE : BddEquiv) (hA : AbsBound) (hF : FibCard) {G H : Type} [Group G] [Group H] (ι : H →* G)
    (Γ : Subgroup H) (U : Subgroup G) (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ u ∈ U, g = ι γ * t * u)
    (S : G → Subgroup H) (hS : ∀ g γ, γ ∈ S g ↔ g⁻¹ * ι γ * g ∈ U) (hB : ∀ g, Bdd ↥(Γ ⊓ S g)) :
    ∃ c : ℕ, ∀ U' : Subgroup G, U' ≤ U → U'.relIndex U ≠ 0 → ∀ D : ℕ, U'.relIndex U ≤ D →
      ∀ (d : ℕ) (ξ : ↥Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (@funRep ↥Γ _ (G ⧸ U') (act ι Γ U') d ξ)) ≤ (c * D * d : ℕ) := by
  classical
  letI := act ι Γ U
  have hsm : ∀ (γ : ↥Γ) (g : G), γ • (g : G ⧸ U) = ((ι γ.1 * g : G) : G ⧸ U) := fun _ _ => rfl
  obtain ⟨T, hT'⟩ := hT
  obtain ⟨c, hc⟩ := hA ↥Γ (G ⧸ U)
    ⟨T.image (↑), fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨γ, hγ, t, ht, u, hu, rfl⟩ := hT' g
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, Finset.mem_image.2 ⟨t, ht, ?_⟩⟩
      rw [hsm, QuotientGroup.eq]
      simpa [mul_assoc] using hu⟩
    (fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have e : MulAction.stabilizer ↥Γ (g : G ⧸ U) = (Γ ⊓ S g).subgroupOf Γ := by
        ext γ
        rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hS,
          mul_assoc]
        exact ⟨fun h => ⟨γ.2, h⟩, fun h => h.2⟩
      exact hE ↥(Γ ⊓ S g) _
        ⟨((MulEquiv.subgroupCongr e).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm⟩ (hB g))
  refine ⟨c, fun U' hle h0 D hD d ξ => ?_⟩
  letI := act ι Γ U'
  exact hc (G ⧸ U') (Subgroup.quotientMapOfLE hle)
    (fun γ x => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rfl) D
    (fun y => by rw [hF _ _ _ hle h0 y]; exact_mod_cast hD) d ξ

private theorem levelRep_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F))
    (U : Subgroup (GL (Fin n) (Af F))) {d : ℕ} (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    levelRep Γ U ξ = @funRep ↥Γ _ (GL (Fin n) (Af F) ⧸ U) (act (ratAf F n) Γ U) d (ξ.comp Γ.subtype) := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun f => funext fun x => ?_
  change ξ γ *ᵥ f ((ratAf F n γ.1)⁻¹ • x) = ξ γ *ᵥ f ((ratAf F n (γ.1)⁻¹) • x)
  rw [map_inv]

private theorem cohBound_of (hE : BddEquiv) (hA : AbsBound) (hF : FibCard)
    (hO : FinOrbAbs) (hI : KLevIdx) (hD : FinDC) (h1 : ArithOne) (hC : ArithComm) :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) := by
  intro F _ _ hF' n Γ hΓ
  obtain ⟨c, hc⟩ := gen hE hA hF (ratAf F n) Γ (KLev F n 3)
    (hO _ _ (ratAf F n) Γ (KLev F n 3) (KLev F n 1) hΓ (hI F n 3 (by norm_num)).1 (hD F n))
    (fun g => arith g (KLev F n 3)) (fun g γ => mem_arith) fun g => (bddArith F hF' n _
      (h1 F n ▸ hC F n Γ hΓ g _ (by apply isOpen_KLev; norm_num) (by apply isCompact_KLev; norm_num)))
  refine ⟨c * 3 ^ (Module.finrank ℚ F * (n * n)), Module.finrank ℚ F * (n * n), fun M hM d ξ => ?_⟩
  have hle : KLev F n (3 * M) ≤ KLev F n 3 := KLev_le_of_dvd (dvd_mul_right 3 M)
  have hle1 : KLev F n 3 ≤ KLev F n 1 := KLev_le_of_dvd (one_dvd 3)
  obtain ⟨hi0, hi⟩ := hI F n (3 * M) (by omega)
  have hr0 : (KLev F n (3 * M)).relIndex (KLev F n 3) ≠ 0 := fun h => hi0 (Subgroup.relIndex_eq_zero_of_le_right hle1 h)
  have hr : (KLev F n (3 * M)).relIndex (KLev F n 3) ≤ (3 * M) ^ (Module.finrank ℚ F * (n * n)) :=
    (Subgroup.relIndex_le_of_le_right hle1 hi0).trans hi
  have key := hc _ hle hr0 _ hr d (ξ.comp Γ.subtype)
  rw [← levelRep_eq] at key
  have e : c * 3 ^ (Module.finrank ℚ F * (n * n)) * M ^ (Module.finrank ℚ F * (n * n)) * d =
      c * (3 * M) ^ (Module.finrank ℚ F * (n * n)) * d := by rw [mul_pow, mul_assoc c]
  rw [e]
  exact key

theorem UpperTheory.V.Af.cohBoundFree :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) :=
  cohBound_of UpperTheory.cohomology_bounded_equiv
    (UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound (UpperTheory.cohomology_part_bound_of_sum_bound UpperTheory.cohomology_sum_bound UpperTheory.cohomology_part_split) (UpperTheory.orbit_bound_of_shapiro_functorial (UpperTheory.shapiro_functorial_of_coinduction_bijective UpperTheory.cohomology_to_coinvariants_injective UpperTheory.cohomology_to_coinvariants_surjective)))
    UpperTheory.adelic_cohomology_fiber_card UpperTheory.adelic_cohomology_finite_orbit_bound (UpperTheory.level_subgroup_index_bound_of_card_ohat UpperTheory.card_ohat_quotient_natCast) UpperTheory.finite_adelic_double_cosets UpperTheory.arithmetic_subgroup_level_one UpperTheory.arithmetic_subgroups_commensurable
end
