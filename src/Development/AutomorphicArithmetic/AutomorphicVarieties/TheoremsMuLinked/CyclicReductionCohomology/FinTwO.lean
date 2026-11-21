import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fin_step {A : Type} [AddCommGroup A] (l : ℕ) (h1 : {a : A | l • a = 0}.Finite) (j : ℕ) :
    {a : A | l ^ j • a = 0}.Finite := by
  induction j with
  | zero =>
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro a ha
    simp only [Set.mem_setOf_eq, pow_zero, one_smul] at ha
    simp [ha]
  | succ j ih =>
    have hsub : {a : A | l ^ (j + 1) • a = 0} ⊆ (fun a => l • a) ⁻¹' {a : A | l ^ j • a = 0} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_preimage] at ha ⊢
      rw [smul_smul, ← pow_succ]; exact ha
    refine Set.Finite.subset (Set.Finite.preimage' ih ?_) hsub
    intro b _
    by_cases hne : ((fun a : A => l • a) ⁻¹' {b}).Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      refine Set.Finite.subset (h1.image (fun x => x + a0)) ?_
      intro a ha
      refine ⟨a - a0, ?_, by simp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha0
      simp only [Set.mem_setOf_eq, smul_sub, ha, ha0, sub_self]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; exact Set.finite_empty

theorem UpperTheory.V.Th.finZK :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l ^ k • m = 0) → Finite (Zl ρ) := by
  intro l _ k R Γ M _ _ _ _ _ _ _ _ ρ hphi hlc htors
  classical
  let M1 : Submodule R M :=
    { carrier := {m | l • m = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun r {m} hm => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm, hm, smul_zero] }
  have hst : ∀ g, ∀ m ∈ M1, ρ g m ∈ M1 := by
    intro g m hm
    show l • ρ g m = 0
    rw [← map_nsmul, show l • m = 0 from hm, map_zero]
  let ρ1 : Representation R Γ M1 :=
    { toFun := fun g => (ρ g).restrict (hst g)
      map_one' := by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp }
  have hlc1 : LC ρ1 := fun m => IsLocallyConstant.desc _ Subtype.val (hlc m.1) Subtype.val_injective
  have htors1 : ∀ m : M1, l • m = 0 := by
    intro m
    have h : l • (m : M) = 0 := m.2
    apply Subtype.ext
    simpa using h
  have hfin1 : Finite (Zl ρ1) := (finZ l R Γ M1 ρ1 hphi hlc1 htors1).1
  have hl : {a : Zl ρ | l • a = 0}.Finite := by
    have hval : ∀ a : {a : Zl ρ // l • a = 0}, ∀ g, (a.1 : Γ → M) g ∈ M1 := by
      intro a g
      have h := congrArg (fun x : Zl ρ => (x : Γ → M) g) a.2
      show l • (a.1 : Γ → M) g = 0
      simpa using h
    have hmemF : ∀ a : {a : Zl ρ // l • a = 0},
        (fun g => (⟨(a.1 : Γ → M) g, hval a g⟩ : M1)) ∈ Zl ρ1 := by
      intro a
      obtain ⟨hlc', hcoc⟩ := (mem_Zl ρ).mp a.1.2
      exact (mem_Zl ρ1).mpr ⟨IsLocallyConstant.desc _ Subtype.val hlc' Subtype.val_injective,
        fun g h => Subtype.ext (hcoc g h)⟩
    let F : {a : Zl ρ // l • a = 0} → Zl ρ1 := fun a => ⟨_, hmemF a⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext; funext g
      have := congrFun (congrArg Subtype.val hab) g
      exact congrArg Subtype.val this
    haveI : Finite ↥{a : Zl ρ | l • a = 0} := Finite.of_injective F hF
    exact Set.toFinite _
  have hk := fin_step l hl k
  have huniv : {a : Zl ρ | l ^ k • a = 0} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext g
    simp [htors]
  rw [huniv] at hk
  exact Set.finite_univ_iff.mp hk
end

section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem phiCond_of_isOpen_subgroup {Γ : Type} [Group Γ] [TopologicalSpace Γ] (l : ℕ) (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : PhiCond Γ l) : PhiCond K l := by
  intro H hH
  let H' : Subgroup Γ := H.map K.subtype
  have hH' : IsOpen (H' : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hK.isOpenMap_subtype_val _ hH
  haveI := h H' hH'
  let e : H ≃* H' := H.equivMapOfInjective K.subtype K.subtype_injective
  have hEq : ∀ x : H', (((e.symm x : K) : Γ)) = (x : Γ) := fun x => by
    conv_rhs => rw [← e.apply_symm_apply x]
    rfl
  have hc : Continuous (fun x : H' => e.symm x) := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.congr (fun x => (hEq x).symm)
  refine Finite.of_injective
    (fun φ : {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H)} =>
      (⟨φ.1.comp e.symm.toMonoidHom, by
        rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
        exact φ.2.preimage hc⟩ :
        {ψ : H' →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set H')})) ?_
  intro φ ψ hφψ
  apply Subtype.ext
  ext y
  have := DFunLike.congr_fun (congrArg Subtype.val hφψ) (e y)
  simpa using this

theorem UpperTheory.V.Th.finTwO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), PhiCond G0.Γ l → (Tw y m).Finite := by
  intro l _ L G0 O _ _ _ _ _ n y m hphi
  classical
  obtain ⟨-, hom⟩ := omFacts l O
  obtain ⟨hfin, -, hkill, -, -⟩ := hom m
  obtain ⟨-, ⟨rep, hrep⟩, hlc⟩ := adExP l L G0 G0 (Glob.Hom.refl G0) O n y m
  have hLC := hlc rep (Or.inr hrep)
  have hKo : IsOpen (G0.η.ker : Set G0.Γ) := G0.η_open
  have hKc : IsClosed (G0.η.ker : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
  haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
  let rep0 : Representation O G0.G₀ (Mm O n m) := rep.comp G0.η.ker.subtype
  have hLC0 : LC rep0 := fun Z => (hLC Z).comp_continuous continuous_subtype_val
  have hphi0 : PhiCond G0.G₀ l := phiCond_of_isOpen_subgroup l G0.η.ker hKo hphi
  haveI : Finite (Om O m) := hfin
  have hZ := finZK l m O G0.G₀ (Mm O n m) rep0 hphi0 hLC0
    (fun Z => by
      ext i j
      simpa using hkill (Z i j))
  refine Set.Finite.subset (Set.finite_coe_iff.mp hZ) ?_
  rintro z ⟨hz1, hz2, -⟩
  refine ⟨hz1, fun g h => ?_⟩
  rw [hz2 g h]
  congr 1
  exact (hrep.1 g (z h)).symm
end
