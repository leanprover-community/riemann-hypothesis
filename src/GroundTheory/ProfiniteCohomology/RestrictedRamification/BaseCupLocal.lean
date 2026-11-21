import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSUnram
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSPresentation
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridge
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.LocalField
  Function

noncomputable section

universe u

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_restrictNormalHom (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) (g : Gal(Ω/F)) :
    restrictAb E h (AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) g) =
      AlgEquiv.restrictNormalHom E g := by
  rw [← topologicalAbelianizationEquiv_mk, restrictAb_topologicalAbelianizationEquiv]

end Restrict

theorem zmod_pow_eq_one {n : ℕ} (z : Multiplicative (ZMod n)) : z ^ n = 1 := by
  change Multiplicative.ofAdd (n • Multiplicative.toAdd z) = Multiplicative.ofAdd 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

section Character

variable (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))

def charAbs : Gal(Ω/K) →* Multiplicative (ZMod n) :=
  χ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S))

theorem charAbs_apply (g : Gal(Ω/K)) :
    charAbs χ g = χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) :=
  rfl

theorem continuous_charAbs : Continuous (charAbs χ) :=
  χ.continuous.comp (InfiniteGalois.restrictNormalHom_continuous _)

theorem isOpen_ker_charAbs : IsOpen ((charAbs χ).ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage (continuous_charAbs χ)

theorem isClosed_ker_charAbs : IsClosed ((charAbs χ).ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isClosed_discrete {1}).preimage (continuous_charAbs χ)

theorem closure_commutator_le_ker_charAbs :
    (commutator Gal(Ω/K)).topologicalClosure ≤ (charAbs χ).ker :=
  Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) (isClosed_ker_charAbs χ)

def charAb : (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Multiplicative (ZMod n) :=
  (QuotientGroup.lift _ (charAbs χ) (closure_commutator_le_ker_charAbs χ)).comp
    (topologicalAbelianizationEquiv K Ω).symm.toMulEquiv.toMonoidHom

theorem charAb_restrictNormalHom (g : Gal(Ω/K)) :
    charAb χ (AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g) = charAbs χ g := by
  rw [← topologicalAbelianizationEquiv_mk]
  change QuotientGroup.lift _ (charAbs χ) (closure_commutator_le_ker_charAbs χ)
    ((topologicalAbelianizationEquiv K Ω).symm (topologicalAbelianizationEquiv K Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

def charField : IntermediateField K Ω := fixedField (charAbs χ).ker

theorem fixingSubgroup_charField : (charField χ).fixingSubgroup = (charAbs χ).ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨(charAbs χ).ker, isClosed_ker_charAbs χ⟩

instance finiteDimensional_charField : FiniteDimensional K (charField χ) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by rw [fixingSubgroup_charField]; exact isOpen_ker_charAbs χ)

instance isGalois_charField : IsGalois K (charField χ) := IsGalois.of_fixedField_normal_subgroup _

theorem charAbs_eq_one_iff (g : Gal(Ω/K)) :
    charAbs χ g = 1 ↔ AlgEquiv.restrictNormalHom (charField χ) g = 1 := by
  rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    fixingSubgroup_charField]

instance isAbelianGalois_charField : IsAbelianGalois K (charField χ) := by
  have : IsMulCommutative (charField χ ≃ₐ[K] charField χ) := ⟨⟨fun τ₁ τ₂ ↦ by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← charAbs_eq_one_iff,
      map_mul, map_inv, map_mul, map_mul]
    exact mul_inv_eq_one.2 (mul_comm _ _)⟩⟩
  exact ⟨⟩

theorem charField_le : charField χ ≤ maxUnramifiedOutside K Ω S := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (maxUnramifiedOutside K Ω S),
    IntermediateField.mem_fixedField_iff]
  intro g hg
  have h1 : AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  have h2 : charAbs χ g = 1 := by rw [charAbs_apply, h1, map_one]
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx g (MonoidHom.mem_ker.2 h2)

theorem isUnramifiedOutside_charField : IsUnramifiedOutside S (charField χ) :=
  (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 (charField_le χ)

theorem charAb_eq_one_of_restrictAb
    {σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (h : restrictAb (charField χ) (le_maximalAbelianExtension _) σ = 1) : charAb χ σ = 1 := by
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) σ
  rw [restrictAb_restrictNormalHom] at h
  rw [charAb_restrictNormalHom, charAbs_eq_one_iff]
  exact h

theorem sIdeleSubgroupPos_le_ker :
    sIdeleSubgroupPos S ≤ (((charAb χ).comp (artinMap K Ω)).comp (IdeleClassGroup.mk K)).ker := by
  refine sup_le ?_ fun u hu ↦ ?_
  · rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, IdeleClassGroup.mk_diagonal,
      map_one, map_one]
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
    apply charAb_eq_one_of_restrictAb
    rw [restrictAb_artinMap, reciprocityMap_mk]
    exact unitsOutsidePos_le_ker_ideleSymbol_of_isUnramifiedOutside S _
      (isUnramifiedOutside_charField χ) hu

def charToSIdelePos : SIdeleClassGroupPos S →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (((charAb χ).comp (artinMap K Ω)).comp (IdeleClassGroup.mk K))
    (sIdeleSubgroupPos_le_ker χ)

theorem charToSIdelePos_mk (x : IdeleGroup K) :
    charToSIdelePos χ (SIdeleClassGroupPos.mk S x) = charAb χ (artinMap K Ω (IdeleClassGroup.mk K x)) :=
  rfl

theorem charToSIdelePos_mk_eq (x : IdeleGroup K) (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (artinMap K Ω (IdeleClassGroup.mk K x) ⟨y, hy⟩ : Ω)) :
    charToSIdelePos χ (SIdeleClassGroupPos.mk S x) =
      χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) := by
  have : AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g =
      artinMap K Ω (IdeleClassGroup.mk K x) :=
    AlgEquiv.ext fun y ↦ Subtype.ext (by rw [AlgEquiv.restrictNormalHom_apply, hg y y.2])
  rw [charToSIdelePos_mk, ← this, charAb_restrictNormalHom]
  rfl

end Character

omit [NumberField K] in

theorem liftNormal_apply_of_mem (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)
    (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω) :
    σ.liftNormal Ω y = (σ ⟨y, hy⟩ : Ω) :=
  AlgEquiv.liftNormal_commutes σ Ω ⟨y, hy⟩

variable (K Ω S n) in

def charToSIdelePosHom :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) →*
      (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) where
  toFun := charToSIdelePos
  map_one' := by
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)
    change charToSIdelePos 1 (SIdeleClassGroupPos.mk S x) = 1
    rw [charToSIdelePos_mk_eq 1 x _ (liftNormal_apply_of_mem _)]
    rfl
  map_mul' χ₁ χ₂ := by
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)
    change charToSIdelePos (χ₁ * χ₂) (SIdeleClassGroupPos.mk S x) =
      charToSIdelePos χ₁ (SIdeleClassGroupPos.mk S x) * charToSIdelePos χ₂ (SIdeleClassGroupPos.mk S x)
    rw [charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _),
      charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _),
      charToSIdelePos_mk_eq _ x _ (liftNormal_apply_of_mem _), ContinuousMonoidHom.mul_apply]

variable (S) in

def ofIdeleClassPos : IdeleClassGroup K →* SIdeleClassGroupPos S :=
  QuotientGroup.map _ _ (MonoidHom.id _) le_sup_left

theorem ofIdeleClassPos_mk (x : IdeleGroup K) :
    ofIdeleClassPos S (IdeleClassGroup.mk K x) = SIdeleClassGroupPos.mk S x :=
  rfl

theorem charToSIdelePosHom_injective [IsAlgClosure K Ω] :
    Injective (charToSIdelePosHom K Ω S n) := by
  rw [injective_iff_map_eq_one]
  intro χ hχ
  refine ContinuousMonoidHom.ext fun τ ↦ ?_
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ
  obtain ⟨c, hc⟩ := artinMap_surjective (K := K) (Ω := Ω)
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) g)
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have h := charToSIdelePos_mk_eq (S := S) χ x g fun y hy ↦ by
    rw [hc, AlgEquiv.restrictNormalHom_apply]
  rw [← h]
  exact DFunLike.congr_fun hχ _

theorem charToSIdelePosHom_surjective [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    Surjective (charToSIdelePosHom K Ω S n) := by
  intro ψ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hn : n ≠ 0 := NeZero.ne n
  set ψC := ψ.comp (ofIdeleClassPos S) with hψC
  have hpow : ∀ c : IdeleClassGroup K, c ^ n ∈ ψC.ker := fun c ↦ by
    rw [MonoidHom.mem_ker, map_pow]
    exact zmod_pow_eq_one _
  have hU : ∀ x ∈ unitsOutsidePos S, IdeleClassGroup.mk K x ∈ ψC.ker := fun x hx ↦ by
    rw [MonoidHom.mem_ker, hψC, MonoidHom.comp_apply, ofIdeleClassPos_mk,
      SIdeleClassGroupPos.mk_eq_one_of_mem S hx, map_one]
  have hNo := isOpen_of_pow_mem_of_unitsOutsidePos hS hn ψC.ker hpow hU
  have := finiteIndex_of_pow_mem_of_unitsOutsidePos hS hn ψC.ker hpow hU
  obtain ⟨E, _, _, hE⟩ :=
    exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) ψC.ker hNo
  have hEu : IsUnramifiedOutside S E := isUnramifiedOutside_of_range_ideleClassNorm hS hn E
    (by rw [hE]; exact hpow) (by rw [hE]; exact hU)
  have hES : E ≤ maxUnramifiedOutside K Ω S :=
    (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).1 hEu
  have hρ : Surjective (reciprocityMap K E) := reciprocityMap_surjective
  have hker : (reciprocityMap K E).ker ≤ ψC.ker := by rw [ker_reciprocityMap, hE]
  let χE : Gal(E/K) →* Multiplicative (ZMod n) :=
    (reciprocityMap K E).liftOfRightInverse (surjInv hρ) (rightInverse_surjInv hρ) ⟨ψC, hker⟩
  have hχE : ∀ c, χE (reciprocityMap K E c) = ψC c := fun c ↦
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  let χΩ : Gal(Ω/K) →* Multiplicative (ZMod n) := χE.comp (AlgEquiv.restrictNormalHom E)
  have hχΩc : Continuous χΩ := by
    rw [MonoidHom.coe_comp]
    exact (continuous_of_discreteTopology (f := ⇑χE)).comp (InfiniteGalois.restrictNormalHom_continuous E)
  have hres : RightInverse (fun τ : galUnramifiedOutside K Ω S ↦ τ.liftNormal Ω)
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)) := fun τ ↦
    AlgEquiv.restrict_liftNormal (E := Ω) τ
  have hkerS : (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).ker ≤ χΩ.ker := by
    intro g hg
    rw [IntermediateField.restrictNormalHom_ker] at hg
    have h1 : AlgEquiv.restrictNormalHom E g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_antitone hES hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  let χS : galUnramifiedOutside K Ω S →* Multiplicative (ZMod n) :=
    (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).liftOfRightInverse _ hres ⟨χΩ, hkerS⟩
  have hχS : ∀ g, χS (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) = χΩ g := fun g ↦
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hq : Topology.IsQuotientMap
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) : Gal(Ω/K) → _) := by
    have : T2Space (galUnramifiedOutside K Ω S) := krullTopology_t2
    have hc := InfiniteGalois.restrictNormalHom_continuous (k := K) (K := Ω)
      (maxUnramifiedOutside K Ω S)
    exact hc.isClosedMap.isQuotientMap hc (AlgEquiv.restrictNormalHom_surjective Ω)
  have hcont : Continuous χS := by
    rw [hq.continuous_iff]
    have : (χS ∘ AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)) = χΩ := funext hχS
    rw [this]
    exact hχΩc
  refine ⟨⟨χS, hcont⟩, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_)⟩
  set σ := artinMap K Ω (IdeleClassGroup.mk K x)
  change charToSIdelePos _ (SIdeleClassGroupPos.mk S x) = ψ (SIdeleClassGroupPos.mk S x)
  rw [charToSIdelePos_mk_eq _ x (σ.liftNormal Ω) (liftNormal_apply_of_mem σ)]
  change χS _ = _
  rw [hχS]
  have hg' : AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) (σ.liftNormal Ω) = σ :=
    AlgEquiv.restrict_liftNormal (E := Ω) σ
  change χE (AlgEquiv.restrictNormalHom E (σ.liftNormal Ω)) = _
  rw [← restrictAb_restrictNormalHom E (le_maximalAbelianExtension E), hg', restrictAb_artinMap, hχE]
  rfl

theorem charToSIdelePosHom_bijective [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    Bijective (charToSIdelePosHom K Ω S n) :=
  ⟨charToSIdelePosHom_injective, charToSIdelePosHom_surjective hS⟩

variable (Ω) in

def charEquivPos [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) :=
  MulEquiv.ofBijective _ (charToSIdelePosHom_bijective hS)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.LocalField Function

noncomputable section

universe u

section Units

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

theorem sq_mem_unitsOutsidePos {u : IdeleGroup K} (hu : u ∈ unitsOutside S) :
    u ^ 2 ∈ unitsOutsidePos S := by
  refine mem_unitsOutsidePos.2 ⟨pow_mem hu 2, fun w ↦ ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, map_pow]
  have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 u : (w.1.Completion)ˣ) : w.1.Completion) ≠ 0 :=
    (map_ne_zero _).2 (Units.ne_zero _)
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))

theorem mem_unitsOutsidePos_of_isTotallyComplex [IsTotallyComplex K] {u : IdeleGroup K}
    (hu : u ∈ unitsOutside S) : u ∈ unitsOutsidePos S :=
  mem_unitsOutsidePos.2 ⟨hu, fun w ↦
    absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))⟩

end Units

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {n : ℕ} (hn : Odd n) {z : G}
    (h2 : z ^ 2 = 1) (hz : z ^ n = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hz
  exact hz

variable {K : Type u} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)

def precompPos :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) →* (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) where
  toFun f := f.comp (SIdeleClassGroupPos.toSIdeleClassGroup S)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem precompPos_apply (f : SIdeleClassGroup S →* Multiplicative (ZMod n)) (x : IdeleGroup K) :
    precompPos S n f (SIdeleClassGroupPos.mk S x) = f (SIdeleClassGroup.mk S x) :=
  rfl

theorem precompPos_injective : Injective (precompPos S n) := fun _ _ h ↦
  (MonoidHom.cancel_right (SIdeleClassGroupPos.toSIdeleClassGroup_surjective S)).1 h

theorem precompPos_surjective (h : Odd n ∨ IsTotallyComplex K) : Surjective (precompPos S n) := by
  intro ψ
  have hle : sIdeleSubgroup S ≤ (ψ.comp (SIdeleClassGroupPos.mk S)).ker := by
    refine sup_le ?_ fun u hu ↦ ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, SIdeleClassGroupPos.mk_diagonal, map_one]
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      rcases h with hn | hK
      · refine eq_one_of_sq_eq_one_of_odd hn ?_ (zmod_pow_eq_one _)
        rw [← map_pow, ← map_pow, SIdeleClassGroupPos.mk_eq_one_of_mem S (sq_mem_unitsOutsidePos hu),
          map_one]
      · rw [SIdeleClassGroupPos.mk_eq_one_of_mem S (mem_unitsOutsidePos_of_isTotallyComplex hu),
          map_one]
  exact ⟨QuotientGroup.lift _ _ hle, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun _ ↦ rfl)⟩

def precompPosEquiv (h : Odd n ∨ IsTotallyComplex K) :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) ≃* (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) :=
  MulEquiv.ofBijective (precompPos S n) ⟨precompPos_injective S n, precompPos_surjective S n h⟩

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

variable (Ω) {S n} in

def charEquiv [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K) :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  (charEquivPos Ω hS).trans (precompPosEquiv S n h).symm

variable {S n}

theorem precompPos_charEquiv [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n))) :
    precompPos S n (charEquiv Ω hS h χ) = charToSIdelePos χ :=
  (precompPosEquiv S n h).apply_symm_apply _

theorem charEquiv_mk_eq [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n))) (x : IdeleGroup K)
    (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (artinMap K Ω (IdeleClassGroup.mk K x) ⟨y, hy⟩ : Ω)) :
    charEquiv Ω hS h χ (SIdeleClassGroup.mk S x) =
      χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) := by
  rw [← precompPos_apply, precompPos_charEquiv, charToSIdelePos_mk_eq χ x g hg]

variable (S n)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
  GroundTheory.Global.IdeleGroup Function

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

universe u

section QZ

variable {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}

def charQZ (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) : Additive G →ₜ+ QZ where
  toFun x := zmodToQZ n (Multiplicative.toAdd (χ (Additive.toMul x)))
  map_zero' := by simp
  map_add' x y := by simp [toMul_add, map_mul]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun z : Multiplicative (ZMod n) ↦ zmodToQZ n z.toAdd)).comp
      (χ.continuous.comp continuous_toMul)

theorem charQZ_apply (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) (g : G) :
    charQZ χ (Additive.ofMul g) = zmodToQZ n (Multiplicative.toAdd (χ g)) :=
  rfl

end QZ

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem decompHom_apply_of_localArtinMap (v : HeightOneSpectrum (𝓞 K))
    (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (b : (v.adicCompletion K)ˣ)
    {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)))
    (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω) :
    decompHom (v.adicCompletion K) ι g y =
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  have := NumberField.of_module_finite K L
  let j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K) := ι.comp L.val
  have e := artinMap_finiteEmbedding_apply L v (placeOfAlgHom j) (completionEmbeddingOfAlgHom j) b
    ⟨y, hyL⟩
  have hmem : ι y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) := by
    have := apply_mem_maximalAbelianExtension (completionEmbeddingOfAlgHom j)
      (algebraMap L ((placeOfAlgHom j).1.adicCompletion L) ⟨y, hyL⟩)
    rwa [completionEmbeddingOfAlgHom_algebraMap] at this
  have e2 : (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨ι y, hmem⟩ :
      AlgebraicClosure (v.adicCompletion K)) =
      completionEmbeddingOfAlgHom j (algebraMap L ((placeOfAlgHom j).1.adicCompletion L)
        (restrictAb L (le_maximalAbelianExtension L)
          (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩)) := by
    rw [e]
    exact congrArg (fun z ↦ (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b z :
      AlgebraicClosure (v.adicCompletion K)))
      (Subtype.ext (completionEmbeddingOfAlgHom_algebraMap j ⟨y, hyL⟩).symm)
  have key : ι (decompHom (v.adicCompletion K) ι g y) =
      ι (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
    rw [decompHom_apply, hg _ hmem, e2, completionEmbeddingOfAlgHom_algebraMap]
    change ι ((restrictAb L (le_maximalAbelianExtension L)
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩ : L) : Ω) = _
    rw [restrictAb_apply]
  exact ι.injective key

theorem liftNormal_localArtinMap_apply (v : HeightOneSpectrum (𝓞 K)) (b : (v.adicCompletion K)ˣ)
    (y : AlgebraicClosure (v.adicCompletion K))
    (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) :
    (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b).liftNormal
        (AlgebraicClosure (v.adicCompletion K)) y =
      (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)) :=
  AlgEquiv.liftNormal_commutes (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b)
    (AlgebraicClosure (v.adicCompletion K)) ⟨y, hy⟩

variable {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}


theorem charEquiv_finiteEmbedding [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (b : (v.adicCompletion K)ˣ) {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K))) :
    charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v b)) =
      χ (decompHomS (v.adicCompletion K) S ι g) := by
  rw [charEquiv_mk_eq hS h χ _ (decompHom (v.adicCompletion K) ι g)
    (decompHom_apply_of_localArtinMap v ι b hg), decompHomS_eq]
  rfl

section Cup

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

theorem brauerInvZ_galCupClass_decompHomS [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (a : (v.adicCompletion K)ˣ) :
    brauerInvZOfIsSepClosure (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (galCupClass (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
          (contCharComp (charQZ χ) (decompHomS (v.adicCompletion K) S ι)
            (continuous_decompHomS (Kv := v.adicCompletion K) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v a)))) := by
  rw [brauerInvZOfIsSepClosure_galCupClass _ a _ (liftNormal_localArtinMap_apply v a),
    contCharComp_apply, charEquiv_finiteEmbedding hS h χ v ι a (liftNormal_localArtinMap_apply v a)]
  rfl

theorem placeInv_galCupClass_decompHomS {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}
    (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (w : HeightOneSpectrum (𝓞 K.1)) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (w.adicCompletion K.1))
    (a : (w.adicCompletion K.1)ˣ) :
    placeInv (K := K) (.inr w)
        (galCupClass (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1))
          (contCharComp (charQZ χ) (decompHomS (w.adicCompletion K.1) S ι)
            (continuous_decompHomS (Kv := w.adicCompletion K.1) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ hS h χ (SIdeleClassGroup.mk S (finiteEmbedding w a)))) :=
  brauerInvZ_galCupClass_decompHomS hS h χ w ι a

end Cup

section Frobenius


variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {n : ℕ}

theorem sPresentation_single [Finite S] (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) :
    sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1)) =
      SIdeleClassGroup.mk S (finiteEmbedding v (localUniformizer v)) := by
  rw [sPresentation_apply, map_one, one_mul, toAdd_ofAdd, divisorIdele_single, zpow_one]

set_option maxHeartbeats 4000000 in

theorem charEquiv_sPresentation_single_of (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (σ g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hσ : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) (localUniformizer v)
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1)))
    (hdeg : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) g =
      Multiplicative.ofAdd 1) :
    have := hS.to_subtype
    χ (decompHomS (v.adicCompletion K.1) S ι σ) =
      charEquiv ℚ̄ hS h χ (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) := by
  intro _
  have h1 : unramifiedDegree (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) (σ⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hσ, hdeg, inv_mul_cancel]
  have h2 := decompHomS_eq_one_of_unramifiedDegree_eq_one S ι hv _ h1
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [sPresentation_single, charEquiv_finiteEmbedding hS h χ v ι (localUniformizer v) hg, h2]


end Frobenius

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

section ULiftCompareAlong

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  {B : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep B] {C : Rep.{0} ℤ H} [IsDiscreteRep C]

theorem cohomologyMap_uliftInt_cohomologyMapAlong_of (f : Rep.res φ A ⟶ B) (g : uliftIntToIntRep B ⟶ C)
    (f₂ : Rep.res φ (uliftIntToIntRep A) ⟶ C) (hf : ∀ a : A, g.hom (f.hom a) = f₂.hom a) (m : ℕ)
    (x : cohomology A m) :
    (cohomologyMap g m).hom (cohomologyULiftIntAddEquiv B m ((cohomologyMapAlong φ hφ f m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv A m x) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
  funext h
  exact hf _

end ULiftCompareAlong

section Bock

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

theorem exists_cocycle_δ_bockSeq (hn : n ≠ 0) (z : cocycles (zmodRep.{0} G n) 1) :
    ∃ x₁ : cocycles (intRepTriv G) 2,
      cohomologyπ _ 2 x₁ = (δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z) ∧
      ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down = bockInt (zmodCocycleHom z) g h := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{0} ℤ))
  let x₂ : (cochainsComplex (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (cochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  refine ⟨x₁, hδ.symm, fun g h => ?_⟩
  have e : cochainOf (bockSeq G n).X₂ ((cochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
      cochainOf (bockSeq G n).X₂ (((cochainsComplex (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
    congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
  rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
  have e2 := congrArg ULift.down e
  change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
    ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
      ((zmodCocycleHom z g).val : ℤ) at e2
  have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
  rw [nsmul_eq_mul] at e2
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
  rw [e2, e3]
  ring

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G)

def resIntRepTriv : Rep.res ψ (intRepTriv G) ⟶ intRepTriv H :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def mulIntRight (A : Rep.{0} (ULift.{0} ℤ) H) : A ⊗ Rep.res ψ (intRepTriv G) ⟶ A :=
  (β_ A (Rep.res ψ (intRepTriv G))).hom ≫ (resIntRepTriv ψ ⊗ₘ 𝟙 A) ≫ intMulPairing H A

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mulIntRight_tmul (A : Rep.{0} (ULift.{0} ℤ) H) (a : A) (m : ℤ) :
    (mulIntRight ψ A).hom (a ⊗ₜ[ULift.{0} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)) :
      (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  intMulPairing_tmul H A m a

end Bock

section Inv

variable (F E : Type) [Field F] [Field E] [Algebra F E]

def galUnitsToZ : uliftIntToIntRep (galUnits.{0} F E) ⟶ galUnitsZ F E :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Eˣ)).toIntLinearMap, fun _ => rfl⟩

variable {K : FiniteSubfield}

instance isDiscreteRep_uliftIntToIntRep_galUnits_adic (v : HeightOneSpectrum (𝓞 K.1)) :
    IsDiscreteRep (uliftIntToIntRep (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))) :=
  ⟨fun a => isOpen_stabilizer (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) a⟩

def localInvU (v : HeightOneSpectrum (𝓞 K.1)) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2 →+ QZ :=
  (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
    ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
      (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom)

theorem localInvU_eq (v : HeightOneSpectrum (𝓞 K.1)) :
    localInvU v = (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom) :=
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem localInvU_cohomologyMapAlong_gsUnitsLocalMor (v : S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsUnitsLocalMor S ιs v) 2).hom x) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2 x)) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine Eq.trans ?_ (placeInv_inr_apply _ _).symm
  refine congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  exact cohomologyMap_uliftInt_cohomologyMapAlong_of (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (gsUnitsLocalMor S ιs v) (galUnitsToZ _ _) (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x

theorem localInvU_cohomologyMapAlong_gsSUnitsLocalMor (v : S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsSUnitsLocalMor S ιs v) 2).hom y) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  exact (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1)))
    (cohomologyMapAlong_cohomologyMap_apply (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (gsUnitsLocalMor S ιs v) 2 y).symm).trans
    (localInvU_cohomologyMapAlong_gsUnitsLocalMor S ιs v _)

theorem two_nsmul_placeInv_inl (v : InfinitePlace K.1) (y : localGaloisCohomology K 2 (.inl v)) :
    2 • placeInv (.inl v) y = 0 := by
  by_cases hc : v.IsComplex
  · have := subsingleton_cohomology_two_of_isComplex v hc
    rw [show y = 0 from Subsingleton.elim (α := cohomology (galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)) 2) y 0, map_zero, smul_zero]
  · by_cases hy0 : y = 0
    · rw [hy0, map_zero, smul_zero]
    · change 2 • quadraticInvFun v.Completion (AlgebraicClosure v.Completion) y = 0
      rw [quadraticInvFun_of_ne_zero _ _ hy0, two_nsmul, QZ.mk_half_add_mk_half]

variable [Fintype S]



end Inv

end

end GroundTheory.ProfCoh
end
