import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.LevelModulesDefs
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledC

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P := by
  intro K S hS hSl hP ιr M _ _ hM
  obtain ⟨r, hr⟩ := hM
  have : Finite S := hS
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact gsEulerRatio_eq_one_of_subsingleton S M ιr
  | succ r ih =>
    letI : Module (ULift.{0} ℤ) M := M.hV2
    let T : Module.End (ULift.{0} ℤ) M := (ℓ : Module.End (ULift.{0} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : Finite (Rep.subrepresentation M ⊤ hD) :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0 :=
      ⟨r + 1, fun m => Subtype.ext (hr m.1)⟩
    have hmul := ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl
    have h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1 := by
      refine h K S hS hSl hP ιr _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr :=
      (gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3, mul_one]


end PositivityTheory.Lit1.GEN.W_devis
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_endx

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem mem_gsOpenSubgroup_placesOver_iff {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (K' L : FiniteSubfield) [Fact (K ≤ K')] [Fact (K ≤ L)] [Fact (K' ≤ L)]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S))
    (τ : galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) :
    τ ∈ gsOpenSubgroup (placesOver S) hL'' ↔
      ((((gsBaseChange S hK').symm τ : (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
        galUnramifiedOutside K.1 ℚ̄ S) ∈ gsOpenSubgroup S hL) := by
  rw [mem_gsOpenSubgroup_iff, mem_gsOpenSubgroup_iff]
  refine forall_congr' fun x => ?_
  rw [Subtype.ext_iff, Subtype.ext_iff, coe_gsBaseChange_symm_apply]
  exact Iff.rfl

theorem ending_lemmaX (hX : GlobalEulerCharCoprime) (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) (hc : ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) :
    ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1 := by
  intro K' _ hK' hle _ hcop ιr'
  have hKL : K' ≤ L := by
    intro x hx
    refine mem_of_forall_gsOpenSubgroup_fixes S hL ⟨x, hK' ⟨x, hx⟩⟩ fun σ hσ => ?_
    have h1 := (mem_gsOpenSubgroup_iff S hK' σ).1 (hle hσ) ⟨x, hx⟩
    exact h1
  have : Fact (K' ≤ L) := ⟨hKL⟩
  have hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S) :=
    fun x => mem_of_restrictScalars_eq' (restrictScalars_maxUnramifiedOutside_eq S hK') (hL x)
  have hcomap : (gsOpenSubgroup (placesOver S) hL'' : Subgroup (galUnramifiedOutside K'.1 ℚ̄ (placesOver S))) =
      ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf
        (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).comap
        (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom := by
    ext τ
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' τ
  haveI hfin : Finite (resTo S K' hK' M) := (inferInstanceAs (Finite M))
  refine hX K' (placesOver S) (placesOver_finite hS) ℓ (natCast_not_mem_of_not_mem_placesOver hSℓ) L hL''
    ?_ ?_ hζ hc ιr' (resTo S K' hK' M) ?_ ?_
  · rw [hcomap]
    exact (hN.subgroupOf _).comap _
  · rw [hcomap, Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)]
    exact hcop
  · intro m
    exact hℓ m
  · intro g hg
    exact htriv _ ((mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' g).1 hg)

end PositivityTheory.Lit1.GEN.W_endx
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_endn

open PositivityTheory.Lit1.GEN.W_killed_a PositivityTheory.Lit1.GEN.W_endx

local notation "ℚ̄" => AlgebraicClosure ℚ


end PositivityTheory.Lit1.GEN.W_endn
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_split

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem isTotallyComplex_of_sq_eq_neg_one {E : Type*} [Field E] (x : E) (hx : x ^ 2 = -1) :
    NumberField.IsTotallyComplex E := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  have hr := InfinitePlace.not_isComplex_iff_isReal.1 hw
  have h := congrArg (InfinitePlace.embedding_of_isReal hr) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hr x)]

set_option maxHeartbeats 800000 in
theorem exists_split (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] :
    ∃ (L : FiniteSubfield) (hKL : Fact (K ≤ L)),
      haveI := hKL
      ∃ hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S,
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal ∧ (∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) ∧
        (ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) ∧ ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1 := by
  classical
  have hℓ := (Fact.out : ℓ.Prime)

  let W : Set (galUnramifiedOutside K.1 ℚ̄ S) := (M.ρ.ker : Set (galUnramifiedOutside K.1 ℚ̄ S))
  have hWo : IsOpen W := isOpen_ker_ρ M
  have hW1 : (1 : galUnramifiedOutside K.1 ℚ̄ S) ∈ W := M.ρ.ker.one_mem
  obtain ⟨E, hEf, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S) W).1
    (hWo.mem_nhds hW1)
  let bE := Module.finBasis K.1 E

  let n : ℕ := if ℓ = 2 then 4 else ℓ
  have hn0 : n ≠ 0 := by
    by_cases h2 : ℓ = 2
    · simp [n, h2]
    · simp only [n, h2, if_false]; exact hℓ.ne_zero
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := by
    intro v hv hmem
    apply hv
    apply hSℓ v
    by_cases h2 : ℓ = 2
    · subst h2
      have h4 : ((4 : ℕ) : 𝓞 K.1) = ((2 : ℕ) : 𝓞 K.1) * ((2 : ℕ) : 𝓞 K.1) := by push_cast; ring
      simp only [n, if_true] at hmem
      rw [h4] at hmem
      rcases v.isPrime.mem_or_mem hmem with h | h <;> exact h
    · simpa [n, h2] using hmem
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have hξS : ξ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S hn0 hnS hξ.pow_eq_one
  let T : Finset ℚ̄ := insert ξ (Finset.univ.image fun i => ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
  have hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · exact h ▸ hξS
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (bE i : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNn, hN, hTN⟩ := exists_galois_level_finset S T hT
  have hL : ∀ x : N.1, algebraMap N.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S := fun x => hN x x.2
  have hξN : ξ ∈ N.1 := hTN ξ (Finset.mem_insert_self _ _)
  refine ⟨N, hKN, hL, gsOpenSubgroup_normal hL, ?_, ?_, ?_⟩
  ·
    by_cases h2 : ℓ = 2
    · subst h2
      refine ⟨-1, ?_⟩
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
    · have hξℓ : IsPrimitiveRoot ξ ℓ := by simpa [n, h2] using hξ
      refine ⟨⟨ξ, hξN⟩, IsPrimitiveRoot.of_map_of_injective (f := algebraMap N.1 ℚ̄) ?_
        (algebraMap N.1 ℚ̄).injective⟩
      exact hξℓ
  · by_cases h2 : ℓ = 2
    · right
      have hξ4 : IsPrimitiveRoot ξ 4 := by simpa [n, h2] using hξ
      refine isTotallyComplex_of_sq_eq_neg_one (⟨ξ, hξN⟩ : N.1) ?_
      apply (algebraMap N.1 ℚ̄).injective
      rw [map_pow, map_neg, map_one]
      change ξ ^ 2 = -1
      have h1 : (ξ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hξ4.pow_eq_one
      have h2' : ξ ^ 2 ≠ 1 := hξ4.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
      have h3 : (ξ ^ 2 - 1) * (ξ ^ 2 + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) h2'
      · exact eq_neg_of_add_eq_zero_left h
    · exact Or.inl h2
  ·
    intro g hg
    have hgE : g ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hb : ∀ i, g (bE i : maxUnramifiedOutside K.1 ℚ̄ S) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        intro i
        have hmem : ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1 :=
          hTN _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
        have key := (mem_gsOpenSubgroup_iff S hL g).1 hg (⟨_, hmem⟩ : N.1)
        have he : gsEmbedding (S := S) hL (⟨_, hmem⟩ : N.1) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) :=
          Subtype.ext (coe_embeddingOfRestrictScalarsEq _ _)
        rw [he] at key
        exact key
      have hsum : x = ∑ i, (bE.repr ⟨x, hx⟩ i) • (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        have := congrArg (fun e : E => (e : maxUnramifiedOutside K.1 ℚ̄ S)) (bE.sum_repr ⟨x, hx⟩)
        simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
        exact this.symm
      rw [hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ∀ (r : K.1) (y : maxUnramifiedOutside K.1 ℚ̄ S), g (r • y) = r • g y from
        fun r y => g.toLinearEquiv.map_smul r y, hb i]
    have hgW := hEU hgE
    exact MonoidHom.mem_ker.1 hgW

end PositivityTheory.Lit1.GEN.W_split
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.GlobalEulerCharacteristicAlt

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 1000000 in
theorem exists_prime_to_part (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (L : FiniteSubfield) [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    ∃ (K'' : FiniteSubfield) (_ : Fact (K ≤ K''))
      (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧
      IsCyclic ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ∧
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ ∧
      ∃ hnorm : ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal,
      (haveI := hnorm; IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) ∧
      ∃ a : ℕ, Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a  := by
  classical
  have hUi : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ≠ 0 := by
    rw [index_gsOpenSubgroup]
    exact Module.finrank_pos.ne'
  have hUo : IsOpen (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
      Set (galUnramifiedOutside K.1 ℚ̄ S)) := (gsOpenSubgroup S hL).isOpen
  generalize (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = U at hN hle hcyc hUi hUo ⊢
  generalize (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = W at hle hcyc ⊢
  haveI : U.FiniteIndex := ⟨hUi⟩
  haveI : (U.subgroupOf W).FiniteIndex := inferInstance
  haveI : Finite (W ⧸ U.subgroupOf W) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcomm : ∀ x y : W ⧸ U.subgroupOf W, x * y = y * x := fun x y =>
    (IsCyclic.commGroup (α := W ⧸ U.subgroupOf W)).mul_comm x y
  obtain ⟨n, hndef⟩ : ∃ n, n = Nat.card (W ⧸ U.subgroupOf W) := ⟨_, rfl⟩
  have hn : n ≠ 0 := hndef ▸ Nat.card_pos.ne'
  have hog : orderOf g = n := hndef ▸ orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨a, hadef⟩ : ∃ a, a = n.factorization ℓ := ⟨_, rfl⟩
  have hdvd : ℓ ^ a ∣ n := hadef ▸ Nat.ordProj_dvd n ℓ
  let C : Subgroup (W ⧸ U.subgroupOf W) := Subgroup.zpowers (g ^ (ℓ ^ a))
  have hCcard : Nat.card C = n / ℓ ^ a := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero) (hog ▸ hdvd), hog]
  have hCN : C.Normal := ⟨fun c hc q => by rw [hcomm q c, mul_assoc, mul_inv_cancel, mul_one]; exact hc⟩
  clear_value C
  let D : Subgroup W := C.comap (QuotientGroup.mk' (U.subgroupOf W))
  have hDN : D.Normal := hCN.comap _
  let V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S) := D.map W.subtype
  have hUV : U ≤ V := by
    intro u hu
    refine ⟨⟨u, hle hu⟩, ?_, rfl⟩
    show QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ ∈ C
    have h1 : QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨u, hle hu⟩ : W)).2 hu
    rw [h1]
    exact C.one_mem
  have hVW : V ≤ W := Subgroup.map_subtype_le D
  have hVopen : IsOpen (V : Set (galUnramifiedOutside K.1 ℚ̄ S)) :=
    Subgroup.isOpen_mono hUV hUo
  obtain ⟨K'', hK''f, hK'', hEq⟩ := exists_gsOpenSubgroup_eq (K := K) (S := S) (V := ⟨V, hVopen⟩)
  refine ⟨K'', hK''f, hK'', ?_⟩
  have hV : (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = V := by
    rw [hEq]
  rw [hV]
  have hVD : V.subgroupOf W = D := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective W) D

  let ψ0 : V →* W ⧸ U.subgroupOf W := (QuotientGroup.mk' (U.subgroupOf W)).comp (Subgroup.inclusion hVW)
  have hψ0 : ∀ v : V, ψ0 v ∈ C := by
    intro v
    obtain ⟨w, hw, hwv⟩ := v.2
    have h1 : Subgroup.inclusion hVW v = w := Subtype.ext hwv.symm
    show QuotientGroup.mk' (U.subgroupOf W) (Subgroup.inclusion hVW v) ∈ C
    rw [h1]
    exact hw
  let ψ : V →* C := ψ0.codRestrict C hψ0
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H w =>
      refine ⟨⟨w.1, ⟨w, hq, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hker : ψ.ker = U.subgroupOf V := by
    ext v
    constructor
    · intro h
      have h1 : ψ0 v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 h)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).1 h1
    · intro h
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).2 h
  let e : V ⧸ U.subgroupOf V ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hcardVU : Nat.card (V ⧸ U.subgroupOf V) = n / ℓ ^ a := (Nat.card_congr e.toEquiv).trans hCcard
  refine ⟨hUV, hVW, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_, ?_⟩
  · show Nat.Coprime (Nat.card (V ⧸ U.subgroupOf V)) ℓ
    rw [hcardVU]
    rw [hadef]; exact (Nat.coprime_ordCompl (Fact.out : ℓ.Prime) hn).symm
  · rw [hVD]
    refine ⟨hDN, ?_, a, ?_⟩
    · let f : (W ⧸ U.subgroupOf W) →* W ⧸ D :=
        QuotientGroup.map (U.subgroupOf W) D (MonoidHom.id W) (by
          intro w hw
          show QuotientGroup.mk' (U.subgroupOf W) w ∈ C
          have h1 : QuotientGroup.mk' (U.subgroupOf W) w = 1 := (QuotientGroup.eq_one_iff w).2 hw
          rw [h1]
          exact C.one_mem)
      refine isCyclic_of_surjective f ?_
      intro x
      induction x using QuotientGroup.induction_on with
      | H w => exact ⟨QuotientGroup.mk w, rfl⟩
    · show D.index = ℓ ^ a
      have h1 : D.index = C.index := Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h2 : Nat.card C * C.index = n := hndef ▸ Subgroup.card_mul_index C
      have h3 : ℓ ^ a * (n / ℓ ^ a) = n := hadef ▸ Nat.ordProj_mul_ordCompl_eq_self n ℓ
      have hpos : 0 < n / ℓ ^ a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (pow_pos (Fact.out : ℓ.Prime).pos _)
      rw [hCcard] at h2
      rw [h1]
      have : (n / ℓ ^ a) * C.index = (n / ℓ ^ a) * ℓ ^ a := by rw [h2, mul_comm, h3]
      exact Nat.eq_of_mul_eq_mul_left hpos this

end PositivityTheory.Lit1.GEN.GlobalEulerCharacteristicAlt
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_b

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 1000000 in

theorem ratio_shortExact_prime (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hℓ : ∃ r : ℕ, ∀ m : T.X₂, (ℓ ^ r) • m = 0) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  haveI : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite S
  have hp : ℓ.Prime := Fact.out
  haveI : Nonempty S := nonempty_of_natCast_mem_of_ne_one (N := ℓ) S hp.one_lt.ne' hSℓ
  obtain ⟨r, hr⟩ := hℓ
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have hsurj : Function.Surjective T.g.hom := (Rep.epi_iff_surjective _).1 hT.epi_g
  haveI : Finite T.X₁ := Finite.of_injective _ hinj
  haveI : Finite T.X₃ := Finite.of_surjective _ hsurj
  haveI : NeZero (ℓ ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K.1), (((ℓ ^ r : ℕ)) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSℓ v
    rw [Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem r hv
  let ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) := fun v =>
    (nonempty_algHom_of_isSepClosed : Nonempty (AlgebraicClosure ℚ →ₐ[K.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).some
  have h1 : ∀ m : T.X₁, (ℓ ^ r) • m = 0 := fun m => hinj (by
    rw [map_nsmul, hr, map_zero])
  have hA := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₁) (hM := h1)
    (r := 3) le_rfl
  have hB := bijective_gsRealRes (S := S) (ιr := ιr) (ιs := ιs) (hS := hSN) (M := T.X₂) (hM := hr)
    (r := 3) le_rfl
  have hpg : IsPGroup ℓ (Multiplicative T.X₂) := fun g => ⟨r, by
    show Multiplicative.toAdd (g ^ (ℓ ^ r)) = Multiplicative.toAdd 1
    rw [toAdd_pow]; exact hr _⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn2 : Nat.card T.X₂ = ℓ ^ n := by rw [← hn]; rfl
  have hn' : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₂ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply hSℓ v
    rw [hn2, Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem n hv
  exact gsEulerRatio_shortExact_of_bijective S ιr hT hn' hA hB

theorem ratio_shortExact_prime_card (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hc : ∃ n : ℕ, Nat.card T.X₂ = ℓ ^ n) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  obtain ⟨n, hn⟩ := hc
  exact ratio_shortExact_prime ℓ K S hS hSℓ ιr T hT ⟨n, fun m => by rw [← hn]; exact card_nsmul_eq_zero'⟩


noncomputable def coindStagesEquiv {k G : Type} [CommRing k] [Group G] (U W : Subgroup G) (hUW : U ≤ W)
    (A : Rep.{0} k G) :
    (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A)))).ρ.Equiv
      (Rep.coind U.subtype (Rep.res U.subtype A)).ρ where
  toFun F := ⟨fun g => (F.1 g).1 1, by
    intro u g
    have h3 : (F.1 (u.1 * g)).1 1 = (F.1 g).1 (1 * ⟨u.1, hUW u.2⟩) :=
      congrArg (fun x => x.1 (1 : W)) (F.2 ⟨u.1, hUW u.2⟩ g)
    have h2 := (F.1 g).2 ⟨⟨u.1, hUW u.2⟩, by simp [Subgroup.mem_subgroupOf]⟩ 1
    rw [one_mul] at h3
    rw [mul_one] at h2
    exact h3.trans h2⟩
  map_add' F F' := Subtype.ext (funext fun g => rfl)
  map_smul' c F := Subtype.ext (funext fun g => rfl)
  invFun f := ⟨fun g => ⟨fun w => f.1 (w.1 * g), by
      intro u' w
      have := f.2 ⟨u'.1.1, u'.2⟩ (w.1 * g)
      simpa [mul_assoc] using this⟩, by
    intro w g
    apply Subtype.ext
    funext x
    change f.1 (x.1 * (w.1 * g)) = f.1 ((x * w).1 * g)
    rw [Subgroup.coe_mul, mul_assoc]⟩
  left_inv F := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext w
    have h := congrArg (fun x => x.1 (1 : W)) (F.2 w g)
    change (F.1 (w.1 * g)).1 1 = (F.1 g).1 (1 * w) at h
    rw [one_mul] at h
    exact h
  right_inv f := by
    apply Subtype.ext
    funext g
    change f.1 ((1 : W).1 * g) = f.1 g
    rw [OneMemClass.coe_one, one_mul]
  isIntertwining' h := LinearMap.ext fun F => Subtype.ext (funext fun g => rfl)

theorem coind_stages {k G : Type} [CommRing k] [Group G] (U W : Subgroup G) (hUW : U ≤ W) (A : Rep.{0} k G) :
    Nonempty (Rep.coind W.subtype (Rep.coind (U.subgroupOf W).subtype
        (Rep.res (U.subgroupOf W).subtype (Rep.res W.subtype A))) ≅
      Rep.coind U.subtype (Rep.res U.subtype A)) :=
  ⟨Rep.mkIso (coindStagesEquiv U W hUW A)⟩

set_option maxHeartbeats 1000000 in

theorem isMultiplicativeOn_ratio_coind (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    IsMultiplicativeOn (fun n => ∃ k, n = ℓ ^ k)
      (fun (X : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep X] =>
        gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype X) ιr) := by
  have hp : ℓ.Prime := Fact.out
  exact
  { iso := fun {A B} _ _ _ _ e =>
      gsEulerRatio_eq_of_iso S _ ιr ((Rep.coindFunctor (ULift.{0} ℤ) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype).mapIso e)
    shortExact := fun {T} _ _ _ _ hT hP => by
      have hT' := shortExact_coindShortComplexOf (G := (galUnramifiedOutside K.1 ℚ̄ S)) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) hT
      obtain ⟨k, hk⟩ := hP
      have hcc := card_coind_gsOpenSubgroup S hL' T.X₂
      have hfin : Finite (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype T.X₂) :=
        Nat.finite_of_card_ne_zero (by rw [hcc, hk]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
      have i1 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₁ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₁
      have i2 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₂
      have i3 : IsDiscreteRep (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₃ :=
        isDiscreteRep_coind (gsOpenSubgroup S hL') T.X₃
      have hfin2 : Finite (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ := hfin
      have hcc2 : Nat.card (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T).X₂ = ℓ ^ (k * Module.finrank K.1 L'.1) := by
        rw [pow_mul, ← hk]; exact hcc
      have key := ratio_shortExact_prime_card ℓ K S hS hSℓ ιr (coindShortComplexOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) T) hT' ⟨_, hcc2⟩
      exact key }

theorem ratio_coind_stage_pow (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (K'' : FiniteSubfield) [Fact (K ≤ K'')] (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    [((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal]
    [IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))]
    {a : ℕ} (hcard : Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] (hℓ : ∀ m : M, ℓ • m = 0) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr ^ (ℓ ^ a) := by
  classical
  have hp : ℓ.Prime := Fact.out
  let W : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S) := gsOpenSubgroup S hL'
  haveI : CompactSpace (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := compactSpace_openSubgroup (gsOpenSubgroup S hL')
  let H : OpenSubgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :=
    ⟨(gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), (gsOpenSubgroup S hK'').isOpen.preimage continuous_subtype_val⟩
  haveI : (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal := inferInstanceAs ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal
  haveI : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :=
    inferInstanceAs (IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))))
  have hχ := isMultiplicativeOn_ratio_coind ℓ K S hS hSℓ ιr L' hL'
  have hPdvd : ∀ m n, m ∣ n → (∃ k, n = ℓ ^ k) → (∃ k, m = ℓ ^ k) := by
    rintro m n hmn ⟨k, rfl⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hmn
    exact ⟨j, rfl⟩
  have hPmul : ∀ m n, (∃ k, m = ℓ ^ k) → (∃ k, n = ℓ ^ k) → (∃ k, m * n = ℓ ^ k) := by
    rintro m n ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (pow_add ℓ i j).symm⟩
  have hcM : ∃ k, Nat.card M = ℓ ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hℓ x)
    rw [hx] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hp).1 this
  have : Finite (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := inferInstanceAs (Finite M)
  have hpow := hχ.coind_res_eq_pow hPdvd hPmul H (p := ℓ) hcard (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) hcM
    (fun m => hℓ m)
  obtain ⟨e⟩ := coind_stages (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) hle M
  have e' : Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M))) ≅
      Rep.coind (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := e
  have hd1 : IsDiscreteRep (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M))) := isDiscreteRep_coind H _
  have hd2 : IsDiscreteRep (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.coind (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype
      (Rep.res (H : Subgroup (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)))) :=
    isDiscreteRep_coind (gsOpenSubgroup S hL') _
  rw [← hpow]
  exact (gsEulerRatio_eq_of_iso S _ ιr e').symm

theorem exists_prime_to_part (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (L : FiniteSubfield) [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    ∃ (K'' : FiniteSubfield) (_ : Fact (K ≤ K''))
      (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧
      IsCyclic ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ∧
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ ∧
      ∃ hnorm : ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal,
      (haveI := hnorm; IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) ∧
      ∃ a : ℕ, Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a :=
  GlobalEulerCharacteristicAlt.exists_prime_to_part ℓ K S L hL L' hL' hle hcyc

theorem exists_ratio_coind_eq_resTo (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (K' : FiniteSubfield) [Fact (K ≤ K')] (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] :
    ∃ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
        gsEulerRatio (placesOver S) (W_killed_a.resTo S K' hK' M) ιr' := by
  obtain ⟨ιr', hsh⟩ := exists_gsEulerRatio_coind_eq S hK' ιr
  have : Finite (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M) := inferInstanceAs (Finite M)
  exact ⟨ιr', hsh _⟩

theorem ratio_coind_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (W_killed_a.resTo S K' hK' M) ιr' = 1)
    (L' : FiniteSubfield) [Fact (K ≤ L')]
    (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr = 1 := by

  classical
  have hp : ℓ.Prime := Fact.out
  haveI := hN
  have : Finite S := hS
  obtain ⟨K'', hKK'', hK'', hUle, hle'', hcyc'', hcop, hnorm, hcycW, a, hcard⟩ :=
    exists_prime_to_part ℓ K S L hL L' hL' hle hcyc
  haveI := hKK''
  haveI := hnorm
  haveI := hcycW
  obtain ⟨ιr'', h3⟩ := exists_ratio_coind_eq_resTo K S ιr K'' hK'' M
  have h1 : gsEulerRatio (placesOver S) (W_killed_a.resTo S K'' hK'' M) ιr'' = 1 :=
    hK K'' hK'' hUle hcyc'' hcop ιr''
  have h2 := ratio_coind_stage_pow ℓ K S hS hSℓ ιr L' hL' K'' hK'' hle'' hcard M hℓ
  have he : gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr ^ (ℓ ^ a) = 1 :=
    h2.symm.trans (h3.trans h1)
  have hcM : ∃ k, Nat.card M = ℓ ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    have : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero (hℓ x)
    rw [hx] at this
    exact (Nat.prime_dvd_prime_iff_eq hd hp).1 this
  obtain ⟨k, hk⟩ := hcM
  have hcc := card_coind_gsOpenSubgroup S hL' (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)
  have hcc' : Nat.card (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) =
      ℓ ^ (k * Module.finrank K.1 L'.1) := by
    rw [hcc, pow_mul, ← hk]
  have : Finite (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcc']; exact pow_ne_zero _ hp.ne_zero)
  have hpos : 0 < gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr := by
    refine gsEulerRatio_pos S _ ιr fun v hv => hSℓ v ?_
    rw [hcc', Nat.cast_pow] at hv
    exact v.isPrime.mem_of_pow_mem _ hv
  exact (pow_eq_one_iff_of_nonneg hpos.le (pow_ne_zero _ hp.ne_zero)).1 he

end PositivityTheory.Lit1.GEN.W_killed_b
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_coinf_b

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem uliftInt_smul {A : Type} [AddCommGroup A] (inst : Module (ULift.{0} ℤ) A) (c : ULift.{0} ℤ) (a : A) :
    inst.smul c a = c.down • a := by
  obtain ⟨n⟩ := c
  have h := Int.cast_smul_eq_zsmul (R := ULift.{0} ℤ) (M := A) n a
  have hn : ((n : ℤ) : ULift.{0} ℤ) = ⟨n⟩ := by ext; simp
  rw [hn] at h
  exact h

section Equiv

variable {G Γ : Type} [Group G] [Group Γ] (π : G →* Γ) (hπ : Function.Surjective π) (D : Subgroup Γ)
  (W : Subgroup G) (hW : W = D.comap π)

noncomputable def cosetEquiv : G ⧸ W ≃ Γ ⧸ D :=
  (Subgroup.quotientEquivOfEq hW).trans (quotientComapEquiv D hπ)

theorem cosetEquiv_mk (g : G) :
    cosetEquiv π hπ D W hW (QuotientGroup.mk g) = QuotientGroup.mk (π g) := rfl

theorem cosetEquiv_smul (g : G) (x : G ⧸ W) :
    cosetEquiv π hπ D W hW (g • x) = π g • cosetEquiv π hπ D W hW x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [MulAction.Quotient.smul_mk, cosetEquiv_mk, cosetEquiv_mk, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

theorem cosetEquiv_symm_smul (g : G) (y : Γ ⧸ D) :
    (cosetEquiv π hπ D W hW).symm (π g • y) = g • (cosetEquiv π hπ D W hW).symm y := by
  apply (cosetEquiv π hπ D W hW).injective
  rw [cosetEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Equiv

set_option maxHeartbeats 1000000 in

theorem coind_eq_infl_funRep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M)
    (hρ : ∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m)
    (D : Subgroup (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))))
    (L' : FiniteSubfield) [Fact (K ≤ L')]
    (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hW : (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = D.comap (QuotientGroup.mk' _)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
      (haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ); gsEulerRatio S (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)) ιr) := by
  have hπ : Function.Surjective (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :=
    QuotientGroup.mk'_surjective _
  let E := cosetEquiv _ hπ D _ hW
  letI i1 : Module (ULift.{0} ℤ) ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) → M) :=
    (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).hV2
  letI i2 : Module (ULift.{0} ℤ) (((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) → M) :=
    (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).hV2
  let eqv : (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).ρ.Equiv
      (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).ρ :=
    { toLinearEquiv :=
        { toFun := fun F y => F (E.symm y)
          invFun := fun F x => F (E x)
          map_add' := fun F F' => rfl
          map_smul' := fun c F => by
            funext y
            exact uliftInt_smul _ c (F (E.symm y))
          left_inv := fun F => by funext x; simp
          right_inv := fun F => by funext y; simp }
      isIntertwining' := fun g => by
        refine LinearMap.ext fun F => funext fun y => ?_
        change M.ρ g (F (g⁻¹ • E.symm y)) = ρ (QuotientGroup.mk g) (F (E.symm ((QuotientGroup.mk g : galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))⁻¹ • y)))
        rw [hρ]
        congr 2
        have := cosetEquiv_symm_smul _ hπ D _ hW g⁻¹ y
        exact this.symm }
  haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)
  exact gsEulerRatio_eq_of_iso S _ ιr (coindResIsoFunDiagRep (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) M ≪≫ Rep.mkIso eqv)

end PositivityTheory.Lit1.GEN.W_coinf_b
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic

local notation "ℚ̄" => AlgebraicClosure ℚ

open W_killed_c

def addAct {G : Type} [Group G] (M : Rep.{0} (ULift.{0} ℤ) G) : G →* AddMonoid.End M where
  toFun g := (M.ρ g).toAddMonoidHom
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp <;> rfl

def zmodRep (n : ℕ) {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod n) V] (φ : G →* AddMonoid.End V) :
    Representation (ZMod n) G V where
  toFun g := (φ g).toZModLinearMap n
  map_one' := by ext x; simp <;> rfl
  map_mul' g h := by ext x; simp only [map_mul]; rfl

theorem nonempty_iso_of_addEquiv {k G : Type} [CommRing k] [Group G] (hk : Function.Surjective (Int.cast : ℤ → k))
    (A B : Rep.{0} k G) (e : A ≃+ B) (h : ∀ (g : G) (x : A), e (A.ρ g x) = B.ρ g (e x)) : Nonempty (A ≅ B) := by
  let f : A ≃ₗ[k] B :=
    { e with
      map_smul' := fun c x => by
        obtain ⟨n, rfl⟩ := hk c
        show e ((n : k) • x) = (n : k) • e x
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }
  exact ⟨Rep.mkIso (Representation.Equiv.mk f fun g => LinearMap.ext fun x => h g x)⟩

set_option maxHeartbeats 800000 in
theorem quotient_representation_open (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have hker : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (zmodRep ℓ (addAct M)).ker := fun g hg => by
    rw [MonoidHom.mem_ker]
    ext x
    change (M.ρ g) x = x
    rw [htriv g hg]
    rfl
  let ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M :=
    QuotientGroup.lift _ (zmodRep ℓ (addAct M)) hker
  refine ⟨ρ, fun g m => rfl, ?_⟩
  haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ
  obtain ⟨e⟩ := nonempty_iso_of_addEquiv (k := ULift.{0} ℤ) (fun c => ⟨c.down, rfl⟩) M (infl (gsOpenSubgroup S hL) ρ)
    (AddEquiv.refl M) (fun _ _ => rfl)
  exact gsEulerRatio_eq_of_iso S M ιr e

theorem quot_rep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1) :
    ∃ (_ : Module (ZMod ℓ) M) (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M),
      (∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m) ∧
      gsEulerRatio S M ιr = (haveI := isDiscreteRep_infl (gsOpenSubgroup S hL) ρ; gsEulerRatio S (infl (gsOpenSubgroup S hL) ρ) ιr) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI inst : Module (ZMod ℓ) M := AddCommGroup.zmodModule hℓ
  exact ⟨inst, quotient_representation_open ℓ K S ιr L hL M htriv⟩

end PositivityTheory.Lit1.GEN.QuotientActionGlobalEulerCharacteristic
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_c

local notation "ℚ̄" => AlgebraicClosure ℚ

section GS

theorem ratio_eq_one_of_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hcyc : ∀ (L' : FiniteSubfield) [Fact (K ≤ L')]
      (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr = 1) :
    gsEulerRatio S M ιr = 1 := by
  haveI := hN
  haveI := finite_quot_gs K S L hL
  obtain ⟨inst, ρ, hρ, he⟩ := QuotientActionGlobalEulerCharacteristic.quot_rep ℓ K S ιr L hL M hℓ htriv
  rw [he]
  exact eq_one_of_forall_isCyclic (gsOpenSubgroup S hL) (gs_multKilled ℓ K S hS hSℓ ιr)
    (gs_posKilled ℓ K S hS hSℓ ιr) ρ (fun D hD' => by
      obtain ⟨L', hKL', hL', hW, hle, hcycW⟩ := exists_field_of_cyclic ℓ K S ιr L hL D hD'
      have := hcyc L' hL' hle hcycW
      rw [W_coinf_b.coind_eq_infl_funRep ℓ K S ιr L hL M ρ hρ D L' hL' hW] at this
      exact this)

end GS

end PositivityTheory.Lit1.GEN.W_killed_c
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_assemble

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ratio_eq_one_of_coprime_cyclic' (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1) :
    gsEulerRatio S M ιr = 1 :=
  W_killed_c.ratio_eq_one_of_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (fun L' _ hL' hle hcyc => W_killed_b.ratio_coind_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hK L' hL' hle hcyc)


theorem ratioOneKilled_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) :
    RatioOneKilled ℓ (fun _ => True) := by
  intro K S hS hSℓ _ ιr M _ _ hℓ
  obtain ⟨L, hKL, hL, hN, hζ, hc, htriv⟩ := W_split.exists_split ℓ K S hS hSℓ M
  exact ratio_eq_one_of_coprime_cyclic' ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (W_endx.ending_lemmaX hX ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hζ hc)

end PositivityTheory.Lit1.GEN.W_assemble
end

section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P :=
  W_devis.ratioOne_of_killed_l ℓ P h

theorem ratioOne_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) : RatioOne ℓ (fun _ => True) :=
  ratioOne_of_killed_l ℓ _ (W_assemble.ratioOneKilled_of_lemmaX ℓ hX)

end PositivityTheory.Lit1.GEN
end
