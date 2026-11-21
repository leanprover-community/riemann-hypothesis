import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.artDec :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (Dec (F := K) A).map (artCl K Ω) = Subgroup.zpowers (primeCl v) := by
  intro K Ω _ _ _ _ _ A v hA
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hσv : artCl K Ω σ = primeCl v := artFrob K Ω A v σ hA hσ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine decGen K Ω A v σ _ hA hσ ?_ ?_ ?_
    · exact (artSurj K Ω).2 (Subgroup.zpowers (primeCl v) : Set (ClassGroup (𝓞 K)))
    · intro g hg
      rw [Subgroup.mem_comap, (artIne K Ω).1 A g hg]
      exact one_mem _
    · rw [Subgroup.mem_comap, hσv]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨σ, hσ.1, hσv⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], N ≠ 0 → (ClDual K N R M).map (clPull K hU R M) ≤ XDual N U R M ∧ (galOf F K Ω ≤ U → Function.Injective (clPull K hU R M)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU N R M _ _ _ hN
  obtain ⟨hD, hI, hc, hH⟩ := toGalDict F Ω K U hU
  obtain ⟨hS, hL⟩ := artSurj K Ω
  obtain ⟨-, hP, hT, hA⟩ := placeDict K Ω
  refine ⟨?_, fun h => ?_⟩
  · rintro _ ⟨θ, ⟨hm, hv⟩, rfl⟩
    let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
      rw [hm, ofAdd_add]
    have h1 : θ 1 = 0 := congrArg Multiplicative.toAdd θ'.map_one
    refine ⟨?_, fun a b => ?_, fun A u hu => ?_, fun A hAN u hu => ?_⟩
    · exact (hL.comp_continuous hc).comp θ
    · rw [clPull_apply, clPull_apply, clPull_apply, map_mul, map_mul, hm]
    · rw [clPull_apply, (artIne K Ω).1 A _ ((hI A u).2 hu), h1]
    · obtain ⟨v, hAv⟩ := hP A (hT A N hN hAN)
      have hvN := (hA A v N hAv).1 hAN
      have hmem : artCl K Ω (toGal K hU u) ∈ Subgroup.zpowers (primeCl v) := by
        rw [← artDec K Ω A v hAv]
        exact Subgroup.mem_map_of_mem _ ((hD A u).2 hu)
      have hle : Subgroup.zpowers (primeCl v) ≤ θ'.ker := by
        rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd (hv v hvN)
      rw [clPull_apply]
      exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 (hle hmem))
  · exact LinearMap.funLeft_injective_of_surjective R M _ (hS.comp (hH h).1.surjective)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.pullOnto :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], N ≠ 0 → galOf F K Ω ≤ U → (IsTotallyComplex K ∨ ∀ m : M, 2 • m = 0 → m = 0) → (ClDual K N R M).map (clPull K hU R M) = XDual N U R M := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU N R M _ _ _ hN hU' hK
  refine le_antisymm (pullMem F Ω K U hU N R M hN).1 fun φ hφ => ?_
  obtain ⟨hlc, hadd, hI, hD⟩ := hφ
  obtain ⟨hDec, hIne, -, -⟩ := toGalDict F Ω K U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  let ι : G K Ω →* U := (galEmb F K Ω).codRestrict U fun σ => hU' (galEmb_mem F K Ω σ)
  have hι : Continuous ι := hE.continuous.subtype_mk _
  have h1 : ∀ σ, toGal K hU (ι σ) = σ := fun σ => AlgEquiv.ext fun x => rfl
  have h2 : ∀ u, ι (toGal K hU u) = u := fun u => Subtype.ext (AlgEquiv.ext fun x => rfl)
  let φ' : U →* Multiplicative M := MonoidHom.mk' (fun u => Multiplicative.ofAdd (φ u)) fun a b => by
    rw [hadd, ofAdd_add]
  let χ : G K Ω →* Multiplicative M := φ'.comp ι
  have hχ : ∀ σ, χ σ = 1 ↔ φ (ι σ) = 0 := fun σ => Iff.rfl
  have hker : (artCl K Ω).ker ≤ χ.ker := by
    refine artKer K Ω (Multiplicative M) χ ?_ (fun A σ hσ => ?_) fun c hc => ?_
    · exact (hlc.comp_continuous hι).isOpen_fiber 0
    · exact (hχ σ).2 (hI A _ ((hIne A _).1 ((h1 σ).symm ▸ hσ)))
    · obtain ⟨j, hj⟩ := hc
      rcases hK with hK | hK
      · refine absurd ?_ (InfinitePlace.not_isReal_iff_isComplex.2
          (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K Ω)))))
        rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
        ext x
        have := hj (algebraMap K Ω x)
        rw [show c.toRingEquiv (algebraMap K Ω x) = algebraMap K Ω x from c.commutes x] at this
        exact this.symm
      · have hcc : c * c = 1 := AlgEquiv.ext fun x => j.injective (by
          have e1 := hj (c x)
          have e2 := hj x
          exact e1.trans ((congrArg _ e2).trans (Complex.conj_conj _)))
        have e : χ c * χ c = 1 := by rw [← map_mul, hcc, map_one]
        refine (hχ c).2 (hK _ ?_)
        rw [two_nsmul]
        exact e
  let θ := MonoidHom.liftOfSurjective (artCl K Ω) (artSurj K Ω).1 ⟨χ, hker⟩
  have hθ : ∀ σ, θ (artCl K Ω σ) = χ σ := fun σ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hker⟩ σ
  refine ⟨fun c => Multiplicative.toAdd (θ c), ⟨fun a b => congrArg Multiplicative.toAdd (θ.map_mul a b), fun v hv => ?_⟩, funext fun u => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    show Multiplicative.toAdd (θ (primeCl v)) = 0
    rw [← artFrob K Ω A v σ hA hσ, hθ]
    exact hD A (((placeDict K Ω).2.2.2 A v N hA).2 hv) _ ((hDec A _).1 ((h1 σ).symm ▸ hσ.1))
  · rw [clPull_apply, hθ]
    exact congrArg φ (h2 u)
end
