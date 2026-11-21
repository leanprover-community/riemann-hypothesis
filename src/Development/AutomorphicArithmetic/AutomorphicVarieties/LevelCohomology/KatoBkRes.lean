import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.resAway :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [AddCommGroup V] [Module C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), (∀ g h, c (g * h) = c g + ρ g (c h)) → (∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := ℚ) A, c s = ρ s x - x) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := K) A, c (s.restrictScalars ℚ) = ρ (s.restrictScalars ℚ) x - x := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ ρ c hc hyp w hw
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  obtain ⟨B, hB⟩ := exists_isPlaceOver (F := K) Ω w
  have hne : w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)
  let p : HeightOneSpectrum (𝓞 ℚ) := ⟨w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)), Ideal.comap_isPrime _ _, hne⟩
  have hBp : IsPlaceOver B p := by
    intro y
    have key := hB (algebraMap (𝓞 ℚ) (𝓞 K) y)
    have hcoe : ((algebraMap (𝓞 ℚ) (𝓞 K) y : 𝓞 K) : K) = algebraMap ℚ K (y : ℚ) := rfl
    rw [hcoe, ← IsScalarTower.algebraMap_apply] at key
    exact key
  have hlp : ((l : ℕ) : 𝓞 ℚ) ∉ p.asIdeal := by
    show _ ∉ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨A, hA, x, hx⟩ := hyp p hlp
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hBp
  refine ⟨B, hB, ρ σ x - c σ, ?_⟩
  intro s hs
  have ht : s.restrictScalars ℚ ∈ Ine (F := ℚ) B := ⟨hs.1, fun y hy => hs.2 y hy⟩
  rw [← hσ] at ht
  have hu := hx _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' ht)
  have htu : s.restrictScalars ℚ * σ = σ * (σ⁻¹ * s.restrictScalars ℚ * σ) := by group
  have e1 := hc (s.restrictScalars ℚ) σ
  have e2 := hc σ (σ⁻¹ * s.restrictScalars ℚ * σ)
  rw [htu] at e1
  have hct := eq_sub_of_add_eq (e1.symm.trans e2)
  have hm : ρ σ (ρ (σ⁻¹ * s.restrictScalars ℚ * σ) x) = ρ (s.restrictScalars ℚ) (ρ σ x) := by
    rw [← Module.End.mul_apply, ← map_mul, ← htu, map_mul, Module.End.mul_apply]
  rw [hct, hu, map_sub, hm, map_sub]
  abel
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.embConj :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (j₀ : Ω →+* Om l) (τ : K →+* Om l), ∃ g : G ℚ Ω, (j₀.comp (g : Ω →+* Ω)).comp (algebraMap K Ω) = τ := by
  intro l _ K Ω _ _ _ _ _ _ _ j₀ τ
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hsub : ∀ x : K, ∃ b : Ω, j₀ b = τ x := by
    intro x
    have hp : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hrat : j₀.comp (algebraMap ℚ Ω) = τ.comp (algebraMap ℚ K) := Subsingleton.elim _ _
    have hroot : τ x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j₀).roots := by
      rw [Polynomial.map_map, Polynomial.mem_roots_map hp, hrat, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    rw [(IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ Ω))).roots_map j₀] at hroot
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hroot
    exact ⟨b, hb⟩
  choose f hf using hsub
  let τ' : K →+* Ω :=
    { toFun := f
      map_one' := j₀.injective (by rw [hf, map_one, map_one])
      map_mul' := fun a b => j₀.injective (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := j₀.injective (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => j₀.injective (by rw [hf, map_add, map_add, hf, hf]) }
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let g0 : Ω →ₐ[ℚ] Ω := (τ'.toRatAlgHom).liftNormal Ω
  refine ⟨AlgEquiv.ofBijective g0 (Algebra.IsAlgebraic.algHom_bijective g0), ?_⟩
  ext x
  show j₀ (g0 (algebraMap K Ω x)) = τ x
  rw [AlgHom.liftNormal_commutes]
  exact hf x
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkRes :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), c ∈ Z1 ρ → IsBK l ρ c → (fun s : G K Ω => c (s.restrictScalars ℚ)) ∈ Z1 (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧ IsBK l (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (fun s : G K Ω => c (s.restrictScalars ℚ)) := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ _ _ _ _ _ _ ρ c hc hbk
  obtain ⟨hcont, hcc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  have hcont' : Continuous fun s : G K Ω => c (s.restrictScalars ℚ) :=
    hcont.comp (continuous_restrictScalarsHom ℚ K Ω)
  have hcc' : ∀ s t : G K Ω, c ((s * t).restrictScalars ℚ) =
      c (s.restrictScalars ℚ) + ρ (s.restrictScalars ℚ) (c (t.restrictScalars ℚ)) :=
    fun s t => hcc (s.restrictScalars ℚ) (t.restrictScalars ℚ)
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨hcont', hcc'⟩,
    UpperTheory.V.X.Kato.resAway l K Ω C V ρ c hcc hbk.away, fun τ => ?_⟩
  obtain ⟨j₀, -, -, x, hx⟩ := hbk.above (τ.comp (algebraMap ℚ K))
  obtain ⟨g, hg⟩ := UpperTheory.V.X.Kato.embConj l K Ω j₀ τ
  refine ⟨j₀.comp (g : Ω →+* Ω), hg, ⟨hcont'.comp (continuous_fst.comp continuous_subtype_val),
    fun s t => hcc' s.1.1 t.1.1⟩,
    TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id x - c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l), ?_⟩
  rintro ⟨⟨s, σ⟩, hs⟩
  have ht : (g * s.restrictScalars ℚ * g⁻¹, σ) ∈ decJ ℚ j₀ := by
    intro y
    have h := hs (g⁻¹ y)
    change σ (j₀ (g (g.symm y))) = j₀ (g (s (g.symm y))) at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h
  have h1 := hx ⟨_, ht⟩
  change c (s.restrictScalars ℚ) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (s.restrictScalars ℚ)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap _ - _
  change c (g * s.restrictScalars ℚ * g⁻¹) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (g * s.restrictScalars ℚ * g⁻¹))
      ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap x - x at h1
  generalize s.restrictScalars ℚ = u at h1 ⊢
  have e1 : g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ := by group
  have e2 := hcc g⁻¹ (g * u * g⁻¹)
  rw [e1, hcc] at e2
  have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
      TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id
        (TensorProduct.AlgebraTensorModule.map (ρ (g * u * g⁻¹)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap y) =
      TensorProduct.AlgebraTensorModule.map (ρ u) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap
        (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹)
    (LinearMap.id : UpperTheory.V.Loc.Bcr l →ₗ[ℚ_[l]] UpperTheory.V.Loc.Bcr l)) h1
  rw [map_sub, key, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h2
  rw [map_sub, TensorProduct.AlgebraTensorModule.map_tmul, eq_sub_of_add_eq e2, TensorProduct.sub_tmul,
    TensorProduct.add_tmul, h2]
  simp only [AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_one]
  abel
end
