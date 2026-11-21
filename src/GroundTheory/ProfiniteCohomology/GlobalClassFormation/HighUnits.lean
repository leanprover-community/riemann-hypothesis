import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations.HighFormations

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

noncomputable section

variable {K : FiniteSubfield}

theorem subsingleton_localGaloisCohomology_inr_of_three_le (v : HeightOneSpectrum (𝓞 K.1)) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (localGaloisCohomology K r (.inr v)) := by
  have := subsingleton_cohomology_galUnits_of_three_le (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)) hr
  exact (cohomologyULiftIntAddEquiv (galUnits.{0} (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))) r).symm.injective.subsingleton

theorem subsingleton_localGaloisCohomology_inl_of_isComplex (v : InfinitePlace K.1) (hv : v.IsComplex)
    {r : ℕ} (hr : 1 ≤ r) : Subsingleton (localGaloisCohomology K r (.inl v)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  obtain ⟨F, _, w, ⟨e⟩⟩ := exists_infCompletion_algEquiv v
  have : (w : InfinitePlace F.1).LiesOver v := w.2
  have h1 : Module.finrank v.Completion (AlgebraicClosure v.Completion) = 1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace F.1)).2
      fun h => (InfinitePlace.not_isReal_iff_isComplex.2 hv) h.1
  have hcard : Nat.card Gal(AlgebraicClosure v.Completion/v.Completion) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, h1]
  have : Subsingleton Gal(AlgebraicClosure v.Completion/v.Completion) :=
    (Nat.card_eq_one_iff_unique.1 hcard).1
  exact ModuleCat.isZero_iff_subsingleton.1
    ((isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (cohomologyIsoGroupCohomology _ (n + 1)))

section Real

variable (v : InfinitePlace K.1) (hv : v.IsReal)

include hv in

theorem card_gal_infAlgClosure_of_isReal :
    Fintype.card Gal(AlgebraicClosure v.Completion/v.Completion) = 2 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure v.Completion)
  obtain ⟨σ, hσ⟩ := exists_gal_ne_of_sq_eq_neg_one v hv (s := s) (by rw [sq, ← hs])
  have h1 : 1 < Fintype.card Gal(AlgebraicClosure v.Completion/v.Completion) :=
    Fintype.one_lt_card_iff.2 ⟨σ, 1, fun h => hσ (by rw [h]; rfl)⟩
  have h2 := card_gal_le_two v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
  omega

include hv in

theorem isCyclic_gal_infAlgClosure_of_isReal :
    IsCyclic Gal(AlgebraicClosure v.Completion/v.Completion) :=
  isCyclic_of_prime_card (p := 2)
    (by rw [Nat.card_eq_fintype_card, card_gal_infAlgClosure_of_isReal v hv])

include hv in

theorem natCard_localGaloisCohomology_two_of_isReal :
    Nat.card (localGaloisCohomology K 2 (.inl v)) = 2 := by
  change Nat.card (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) = 2
  have h2 := infAlgClosure_finrank_le_two v
  set x0 := galCupClass v.Completion (AlgebraicClosure v.Completion)
    (quadraticChar v.Completion (AlgebraicClosure v.Completion) h2) (-1) with hx0def
  have hx0 : x0 ≠ 0 := by
    rw [Ne, hx0def, galCupClass_eq_zero_iff_of_injective _ _ _
      (quadraticChar_injective v.Completion (AlgebraicClosure v.Completion) h2)]
    intro hmem
    have h := (infAlgClosure_mem_range_norm_iff_of_isReal v hv (-1)).1 hmem
    rw [Units.val_neg, Units.val_one, map_neg, map_one] at h
    norm_num at h
  rw [Nat.card_eq_two_iff]
  refine ⟨0, x0, hx0.symm, ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hx : x = 0
  · exact Or.inl hx
  · refine Or.inr (quadraticInv_injective v.Completion (AlgebraicClosure v.Completion) h2
      (infAlgClosure_mul_mem_range_norm v) ?_)
    rw [quadraticInv_apply, quadraticInv_apply, quadraticInvFun_of_ne_zero _ _ hx,
      quadraticInvFun_of_ne_zero _ _ hx0]

include hv in

theorem subsingleton_localGaloisCohomology_of_isReal_of_odd {r : ℕ} (hr : Odd r) :
    Subsingleton (localGaloisCohomology K r (.inl v)) := by
  classical
  change Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) r)
  have := isCyclic_gal_infAlgClosure_of_isReal v hv
  let _ : CommGroup Gal(AlgebraicClosure v.Completion/v.Completion) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(AlgebraicClosure v.Completion/v.Completion))
  let A := galUnitsZ v.Completion (AlgebraicClosure v.Completion)
  have h1 : Subsingleton (groupCohomology A 1) :=
    ModuleCat.isZero_iff_subsingleton.1 ((isZero_cohomology_one_galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)).of_iso (cohomologyIsoGroupCohomology A 1).symm)
  let e : cohomology A r ≅ groupCohomology A 1 :=
    cohomologyIsoGroupCohomology A r ≪≫ Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg r hr ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm
  exact e.toLinearEquiv.injective.subsingleton

include hv in

theorem natCard_localGaloisCohomology_of_isReal_of_even {r : ℕ} (hr0 : r ≠ 0) (hr : Even r) :
    Nat.card (localGaloisCohomology K r (.inl v)) = 2 := by
  classical
  have : NeZero r := ⟨hr0⟩
  rw [← natCard_localGaloisCohomology_two_of_isReal v hv]
  change Nat.card (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) r) =
    Nat.card (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2)
  have := isCyclic_gal_infAlgClosure_of_isReal v hv
  let _ : CommGroup Gal(AlgebraicClosure v.Completion/v.Completion) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(AlgebraicClosure v.Completion/v.Completion))
  let A := galUnitsZ v.Completion (AlgebraicClosure v.Completion)
  let e : cohomology A r ≅ cohomology A 2 :=
    cohomologyIsoGroupCohomology A r ≪≫ Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg r hr ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm ≪≫
        (cohomologyIsoGroupCohomology A 2).symm
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end Real

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global FiniteSubfield DirectSum

noncomputable section

variable {K : FiniteSubfield}

theorem bijective_unitsToIdeles_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    Function.Bijective (unitsToIdeles K r).hom := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hC : ∀ m, 3 ≤ m → ∀ c : cohomology (classLimitRep K) m, c = 0 := fun m hm c =>
    (subsingleton_cohomology_classLimitRep_of_three_le K hm).elim c 0
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K n x hx
    rw [hC n (by omega) c, map_zero]
  · exact exists_unitsToIdeles_eq K (n + 1) y (hC _ (by omega) _)

theorem subsingleton_localGaloisCohomology_of_not_isReal {r : ℕ} (hr : 3 ≤ r) :
    ∀ v : Place K.1, (∀ w : InfinitePlace K.1, v = .inl w → w.IsComplex) →
      Subsingleton (localGaloisCohomology K r v)
  | .inl w, h => subsingleton_localGaloisCohomology_inl_of_isComplex w (h w rfl) (by omega)
  | .inr v, _ => subsingleton_localGaloisCohomology_inr_of_three_le v hr

def realLocalization (ι : LocalEmbeddings K) {r : ℕ} (hr : 1 ≤ r) :
    cohomology (unitsLimitRep K) r →+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) where
  toFun x v := idelesLimitCohomologyEquiv ι hr ((unitsToIdeles K r).hom x) (.inl v.1)
  map_zero' := by
    funext v
    simp only [map_zero]
    rfl
  map_add' x y := by
    funext v
    simp only [map_add]
    rfl

theorem bijective_realComponents {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective (fun (ζ : ⨁ v : Place K.1, localGaloisCohomology K r v)
      (v : {v : InfinitePlace K.1 // v.IsReal}) => ζ (.inl v.1)) := by
  classical
  refine ⟨fun ζ ζ' h => ?_, fun f => ?_⟩
  · ext v
    rcases v with w | v
    · by_cases hw : w.IsReal
      · exact congrFun h ⟨w, hw⟩
      · have := subsingleton_localGaloisCohomology_inl_of_isComplex w
          (InfinitePlace.not_isReal_iff_isComplex.1 hw) (r := r) (by omega)
        exact Subsingleton.elim _ _
    · have := subsingleton_localGaloisCohomology_inr_of_three_le v hr
      exact Subsingleton.elim _ _
  · refine ⟨∑ w : {v : InfinitePlace K.1 // v.IsReal},
      DirectSum.of (localGaloisCohomology K r) (.inl w.1) (f w), ?_⟩
    funext w
    change (∑ w' : {v : InfinitePlace K.1 // v.IsReal},
      DirectSum.of (localGaloisCohomology K r) (.inl w'.1) (f w')) (.inl w.1) = f w
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact DirectSum.of_eq_same _ _
    · intro b _ hb
      exact DirectSum.of_eq_of_ne _ _ _ fun h => hb (Subtype.ext (Sum.inl_injective h)).symm
    · intro h
      exact absurd (Finset.mem_univ w) h

theorem bijective_realLocalization (ι : LocalEmbeddings K) {r : ℕ} (hr : 4 ≤ r) :
    Function.Bijective (realLocalization ι (r := r) (by omega)) :=
  (bijective_realComponents (K := K) (r := r) (by omega)).comp
    ((idelesLimitCohomologyEquiv ι (n := r) (by omega)).bijective.comp
      (bijective_unitsToIdeles_of_four_le hr))

theorem subsingleton_cohomology_unitsLimitRep_of_three_le (hK : ∀ v : InfinitePlace K.1, v.IsComplex)
    {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology (unitsLimitRep K) r) := by
  rcases eq_or_lt_of_le hr with rfl | hr4
  · exact subsingleton_cohomology_three_unitsLimitRep K
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  have hloc : ∀ v : Place K.1, Subsingleton (localGaloisCohomology K r v) := fun v =>
    subsingleton_localGaloisCohomology_of_not_isReal hr v fun w _ => hK w
  have : Subsingleton (⨁ v : Place K.1, localGaloisCohomology K r v) :=
    ⟨fun a b => DFinsupp.ext fun v => Subsingleton.elim _ _⟩
  have : Subsingleton (cohomology (limitRep K) r) :=
    (idelesLimitCohomologyEquiv ι (n := r) (by omega)).injective.subsingleton
  exact (bijective_unitsToIdeles_of_four_le (K := K) hr4).1.subsingleton

end

end GroundTheory.ProfCoh
end
