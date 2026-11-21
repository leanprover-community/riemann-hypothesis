import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.RestrictedRamification.EqZeroOfPowNsmulCohomologySUnitsOfOdd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section NSMul

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem tateCompactCochainsMap_nsmul_id (m : ℕ)
    (hg : ∀ v, a v ≫ (m • 𝟙 (Aᵥ v)) = (Rep.resFunctor (φ v).toMonoidHom).map (m • 𝟙 A) ≫ a v)
    (hgr : ∀ w, ar w ≫ (m • 𝟙 (Aᵣ w)) = (Rep.resFunctor (ψ w).toMonoidHom).map (m • 𝟙 A) ≫ ar w) :
    tateCompactCochainsMap φ ψ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w)) hg hgr =
      m • 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  obtain ⟨⟨x, e⟩, y⟩ := p
  have h1 : ((cochainsMap (m • 𝟙 A)).f n).hom x = m • x := by
    rw [cochainsMap_nsmul, cochainsMap_id]
    simp
  have h2 : ((degZeroMap (piRepHom fun w => m • 𝟙 (Aᵣ w))).f n).hom e = m • e := by
    cases n with
    | zero =>
      funext w
      exact nsmul_id_hom_apply (Aᵣ w) m _
    | succ n => exact Subsingleton.elim _ _
  have h3 : (shiftNegOneMapF (tateLocalMap (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w))) n).hom y =
      m • y := by
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨y1, y2⟩ := y
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · change ((cochainsMap (m • 𝟙 (Aᵥ v))).f n).hom (y1 v) = m • y1 v
        rw [cochainsMap_nsmul, cochainsMap_id]
        simp
      · change ((cochainsMap (m • 𝟙 (Aᵣ w))).f n).hom (y2 w) = m • y2 w
        rw [cochainsMap_nsmul, cochainsMap_id]
        simp
  have hr : ((m • 𝟙 (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar)).f n).hom ((x, e), y) = m • ((x, e), y) := by
    rw [HomologicalComplex.nsmul_f_apply, ModuleCat.hom_nsmul]
    rfl
  rw [hr]
  change ((((cochainsMap (m • 𝟙 A)).f n).hom x,
    ((degZeroMap (piRepHom fun w => m • 𝟙 (Aᵣ w))).f n).hom e),
    (shiftNegOneMapF (tateLocalMap (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w))) n).hom y) = _
  rw [h1, h2, h3]
  rfl

theorem tateCompactCohomologyMap_nsmul_id (m n : ℕ)
    (hg : ∀ v, a v ≫ (m • 𝟙 (Aᵥ v)) = (Rep.resFunctor (φ v).toMonoidHom).map (m • 𝟙 A) ≫ a v)
    (hgr : ∀ w, ar w ≫ (m • 𝟙 (Aᵣ w)) = (Rep.resFunctor (ψ w).toMonoidHom).map (m • 𝟙 A) ≫ ar w) :
    tateCompactCohomologyMap φ ψ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w)) hg hgr n =
      m • 𝟙 _ := by
  unfold tateCompactCohomologyMap
  rw [tateCompactCochainsMap_nsmul_id]
  have := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).map_nsmul
    (f := 𝟙 (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar)) (n := m)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_id] at this
  exact this

end NSMul

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

section LocalMor

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra Kv Ωv]
  (θ : Gal(Ωv/Kv) →* galUnramifiedOutside K.1 ℚ̄ S) (j : maxUnramifiedOutside K.1 ℚ̄ S →+* Ωv)
  (hj : ∀ σ y, j (θ σ y) = σ (j y))

def sUnitsLocalMor : Rep.res θ (galSUnitsMax K.1 ℚ̄ S) ⟶ galUnits.{0} Kv Ωv :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := Ωvˣ)
      ((Units.map j.toMonoidHom).comp (sUnitsMax K.1 ℚ̄ S).subtype)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (hj σ
      (((Additive.toMul x : sUnitsMax K.1 ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩


def rootsLocalMor : Rep.res θ (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) ⟶ galUnits.{0} Kv Ωv :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))
      (β := Ωvˣ) ((Units.map j.toMonoidHom).comp (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (hj σ
      (((Additive.toMul x : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem rootsLocalMor_hom_apply (x : Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))) :
    ((Additive.toMul ((rootsLocalMor S θ j hj).hom x) : Ωvˣ) : Ωv) =
      j (((Additive.toMul x : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) :=
  rfl

def localKummerSeq : ShortComplex (Rep.{0} (ULift.{0} ℤ) Gal(Ωv/Kv)) :=
  ShortComplex.mk (rootsLocalMor S θ j hj) (2 • 𝟙 (galUnits.{0} Kv Ωv)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (2 • 𝟙 (galUnits.{0} Kv Ωv)).hom ((rootsLocalMor S θ j hj).hom x) = 0
    rw [nsmul_id_hom_apply]
    apply Additive.toMul.injective
    apply Units.ext
    have hx2 : ((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) x :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) ^ 2 = 1 := (mem_rootsOfUnity 2 _).1 (Additive.toMul x).2
    change ((Additive.toMul ((rootsLocalMor S θ j hj).hom x) : Ωvˣ) : Ωv) ^ 2 = 1
    rw [rootsLocalMor_hom_apply, ← map_pow, ← Units.val_pow_eq_pow_val, hx2, Units.val_one, map_one])



theorem localKummerSeq_shortExact [IsAlgClosed Ωv] : (localKummerSeq S θ j hj).ShortExact := by
  have h2' : (2 : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := two_ne_zero
  have h2 : (2 : Ωv) ≠ 0 := by
    have : (2 : Ωv) = j 2 := by rw [map_ofNat]
    rw [this]
    exact (map_ne_zero j).2 h2'
  have hmono : Mono (localKummerSeq S θ j hj).f := by
    refine (Rep.mono_iff_injective _).2 fun x y hxy => ?_
    have h := congrArg (fun t : Additive Ωvˣ => ((Additive.toMul t : Ωvˣ) : Ωv)) hxy
    change j (((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) x :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S) =
      j (((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) y :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S) at h
    exact Additive.toMul.injective (Subtype.ext (Units.ext (j.injective h)))
  have hepi : Epi (localKummerSeq S θ j hj).g :=
    (Rep.epi_iff_surjective _).2 (nsmul_id_galUnits_surjective 2 h2)
  refine { exact := ?_ }
  · refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
    let x' : Additive Ωvˣ := x
    have hx' : 2 • x' = 0 :=
      (nsmul_id_hom_apply (galUnits.{0} Kv Ωv) 2 x).symm.trans hx
    have hsq : ((Additive.toMul (α := Ωvˣ) x : Ωvˣ) : Ωv) * ((Additive.toMul (α := Ωvˣ) x : Ωvˣ) : Ωv) = 1 := by
      have e : (2 • x' : Additive Ωvˣ) = x' + x' := two_nsmul x'
      rw [e] at hx'
      have := congrArg (fun t : Additive Ωvˣ => ((Additive.toMul t : Ωvˣ) : Ωv)) hx'
      simp only [toMul_add, toMul_zero, Units.val_mul, Units.val_one] at this
      exact this
    have hneg : (-1 : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ∈ rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S) := by
      rw [mem_rootsOfUnity]
      exact neg_one_sq
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · refine ⟨0, ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      change ((Additive.toMul ((rootsLocalMor S θ j hj).hom 0) : Ωvˣ) : Ωv) = _
      rw [map_zero]
      exact h.symm
    · refine ⟨(Additive.ofMul (⟨-1, hneg⟩ : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))), ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      change j ((-1 : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) = _
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
      exact h.symm

def kummerLocalMap :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2).map (Rep.resFunctor θ) ⟶
      localKummerSeq S θ j hj where
  τ₁ := 𝟙 _
  τ₂ := sUnitsLocalMor S θ j hj
  τ₃ := sUnitsLocalMor S θ j hj
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (2 • 𝟙 (galUnits.{0} Kv Ωv)).hom ((sUnitsLocalMor S θ j hj).hom x) =
      (sUnitsLocalMor S θ j hj).hom ((2 • 𝟙 (galSUnitsMax K.1 ℚ̄ S)).hom x)
    erw [nsmul_id_hom_apply, nsmul_id_hom_apply, map_nsmul]

end LocalMor

section Compat

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv)

theorem gsRestrict_globalDecomp (σ : Gal(Ωv/Kv)) :
    gsRestrict K S (globalDecomp Kv ι σ) = decompHomS Kv S ι σ := by
  ext y
  apply ι.injective
  change ι ((gsRestrict K S (globalDecomp Kv ι σ) y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
    ι ((decompHomS Kv S ι σ y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [gsRestrict_apply, globalDecomp_apply]
  exact (decompHom_apply (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ y).symm

theorem decompHomS_apply (σ : Gal(Ωv/Kv)) (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS Kv S ι σ y) =
      σ ((ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom y) :=
  decompHom_apply _ σ y

def sUnitsToUnitsZ : uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S) ⟶
    uliftIntToIntRep (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (sUnitsMax K.1 ℚ̄ S).subtype).toIntLinearMap, fun _ => LinearMap.ext fun _ => rfl⟩

def sUnitsLocalMorZ : Rep.res (decompHomS Kv S ι) (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) ⟶
    galUnitsZ Kv Ωv :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := Ωvˣ)
    ((Units.map (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
      (sUnitsMax K.1 ℚ̄ S).subtype)).toIntLinearMap,
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (decompHomS_apply S ι σ
      (((Additive.toMul x : sUnitsMax K.1 ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩

instance isDiscreteRep_uliftIntToIntRep_galSUnitsMax :
    IsDiscreteRep (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) :=
  isDiscreteRep_uliftIntToIntRep _

variable [Algebra.IsIntegral Kv Ωv]

theorem unitsLocalRes_gsBrauerInfl_sUnitsToUnitsZ (r : ℕ)
    (x : cohomology (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) r) :
    (unitsLocalRes Kv ι r).hom ((gsBrauerInfl K S r).hom
      ((cohomologyMap (sUnitsToUnitsZ S) r).hom x)) =
      (cohomologyMapAlong (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
        (sUnitsLocalMorZ S ι) r).hom x := by
  unfold unitsLocalRes gsBrauerInfl
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine congrArg (fun g => g.hom x) (?_ : _ = cohomologyMapAlong (decompHomS Kv S ι)
    (continuous_decompHomS (Kv := Kv) S ι) (sUnitsLocalMorZ S ι) r)
  apply cohomologyMapAlong_congr
  · ext σ : 1
    exact gsRestrict_globalDecomp S ι σ
  · intro a
    rfl

set_option maxHeartbeats 2000000 in

theorem unitsLocalRes_sUnitsInfl (r : ℕ) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    (unitsLocalRes Kv ι r).hom (sUnitsInfl K S r y) =
      cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ωv) r
        ((cohomologyMapAlong (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
          (sUnitsLocalMor S (decompHomS Kv S ι) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom
            (decompHomS_apply S ι)) r).hom y) := by
  have h1 := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galSUnitsMax K.1 ℚ̄ S)
    (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
    (sUnitsLocalMor S (decompHomS Kv S ι) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom
      (decompHomS_apply S ι)) (sUnitsLocalMorZ S ι) (fun _ => rfl) r y
  have h2 := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galSUnitsMax K.1 ℚ̄ S)
    (MonoidHom.id _) continuous_id (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (sUnitsToUnitsZ S)
    (fun _ => rfl) r y
  rw [cohomologyMapAlong_id_eq_cohomologyMap, cohomologyMapAlong_id_eq_cohomologyMap] at h2
  rw [sUnitsInfl_apply, gsUnitsInfl_apply]
  refine Eq.trans ?_ h1.symm
  rw [h2]
  exact unitsLocalRes_gsBrauerInfl_sUnitsToUnitsZ S ι r _

end Compat

def realLocalEmbeddings (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) :
    LocalEmbeddings K where
  fin _ := Classical.choice nonempty_algHom_of_isSepClosed
  inf v := by
    classical
    exact if h : v.IsReal then ιr ⟨v, h⟩ else Classical.choice nonempty_algHom_of_isSepClosed


end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Setup

abbrev finUnitsMor (v : S) :=
  sUnitsLocalMor S (gsFinFamily S ιs v).toMonoidHom
    ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιs v))

abbrev realUnitsMor (w : {v : InfinitePlace K.1 // v.IsReal}) :=
  sUnitsLocalMor S (gsRealFamily S ιr w).toMonoidHom
    ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))

abbrev finUnits (v : S) : Rep.{0} (ULift.{0} ℤ)
    Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) :=
  galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

abbrev realUnits (w : {v : InfinitePlace K.1 // v.IsReal}) :
    Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure w.1.Completion / w.1.Completion) :=
  galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)

instance isDiscreteRep_finUnits (v : S) : IsDiscreteRep (finUnits S v) :=
  isDiscreteRep_galUnits (K := (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (L := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

instance isDiscreteRep_realUnits (w : {v : InfinitePlace K.1 // v.IsReal}) : IsDiscreteRep (realUnits w) :=
  isDiscreteRep_galUnits (K := w.1.Completion) (L := AlgebraicClosure w.1.Completion)

abbrev unitsTateCohomology (n : ℕ) : ModuleCat (ULift.{0} ℤ) :=
  tateCompactCohomology (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n

theorem subsingleton_finLocal (v : S) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (cohomology (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) n) :=
  subsingleton_cohomology_galUnits_of_three_le _ _ hn

abbrev realLocalEquiv (w : {v : InfinitePlace K.1 // v.IsReal}) (n : ℕ) :
    cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n ≃+
      localGaloisCohomology K n (.inl w.1) :=
  cohomologyULiftIntAddEquiv (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n

abbrev finLocalEquiv (v : HeightOneSpectrum (𝓞 K.1)) (n : ℕ) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n ≃+
      localGaloisCohomology K n (.inr v) :=
  cohomologyULiftIntAddEquiv (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n

theorem subsingleton_realLocal_of_odd (w : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ} (hn : Odd n) :
    Subsingleton (cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n) := by
  have := subsingleton_localGaloisCohomology_of_isReal_of_odd w.1 w.2 hn
  exact (realLocalEquiv w n).injective.subsingleton

set_option maxHeartbeats 1000000 in

theorem two_nsmul_realLocal (w : {v : InfinitePlace K.1 // v.IsReal}) {n : ℕ} (hn : 1 ≤ n)
    (t : cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) n) : 2 • t = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · have hc := natCard_localGaloisCohomology_of_isReal_of_even w.1 w.2 (by omega) he
    have : Finite (localGaloisCohomology K n (.inl w.1)) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    apply (realLocalEquiv w n).injective
    rw [map_nsmul, map_zero]
    have h := card_nsmul_eq_zero' (G := localGaloisCohomology K n (.inl w.1)) (x := realLocalEquiv w n t)
    rw [hc] at h
    exact h
  · have := subsingleton_realLocal_of_odd w ho
    exact Subsingleton.elim _ _

end Setup

section Real

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

abbrev realUnitsRes (r : ℕ) (w : {v : InfinitePlace K.1 // v.IsReal}) :
    cohomology (galSUnitsMax K.1 ℚ̄ S) r ⟶
      cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) r :=
  cohomologyMapAlong (gsRealFamily S ιr w).toMonoidHom (continuous_toMonoidHom _) (realUnitsMor S ιr w) r

theorem realUnitsRes_eq (r : ℕ) (w : {v : InfinitePlace K.1 // v.IsReal}) :
    realUnitsRes S ιr r w =
      cohomologyMapAlong (decompHomS w.1.Completion S (ιr w)) (continuous_decompHomS (Kv := w.1.Completion) S (ιr w))
        (sUnitsLocalMor S (decompHomS w.1.Completion S (ιr w))
          ((ιr w).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS_apply S (ιr w))) r :=
  rfl

theorem realLocalEquiv_realUnitsRes (ι : LocalEmbeddings K) {r : ℕ} (hr : 1 ≤ r)
    (w : {v : InfinitePlace K.1 // v.IsReal}) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    realLocalization ι hr (sUnitsInfl K S r y) w = realLocalEquiv w r ((realUnitsRes S ιr r w).hom y) := by
  refine (idelesLimitCohomologyEquiv_unitsToIdeles_inl ι hr w.1 (sUnitsInfl K S r y)).trans ?_
  refine (congrArg (fun f => f.hom (sUnitsInfl K S r y))
    (unitsLocalRes_eq_of_algHom w.1.Completion (ιr w) (ι.inf w.1) r)).trans ?_
  exact (unitsLocalRes_sUnitsInfl S (ιr w) r y).trans
    (congrArg (realLocalEquiv w r) (congrArg (fun f => f.hom y) (realUnitsRes_eq S ιr r w).symm))

set_option maxHeartbeats 1000000 in
include h2S in

theorem eq_zero_of_realUnitsRes_eq_zero {r : ℕ} (hr : 4 ≤ r) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r)
    {k : ℕ} (hk : 2 ^ k • y = 0) (h : ∀ w, (realUnitsRes S ιr r w).hom y = 0) : y = 0 := by
  have hinj := (sUnitsRealPrimaryEquiv K S (nonempty_localEmbeddings K).some h2S hr).injective
  have h0 : (⟨y, k, hk⟩ : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2) = 0 := by
    apply hinj
    rw [map_zero]
    funext w
    rw [sUnitsRealPrimaryEquiv_apply, realLocalEquiv_realUnitsRes S ιr (nonempty_localEmbeddings K).some (by omega) w y, h w, map_zero]
    rfl
  exact congrArg Subtype.val h0

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_realUnitsRes_eq {r : ℕ} (hr : 4 ≤ r)
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal},
      cohomology (galUnits.{0} w.1.Completion (AlgebraicClosure w.1.Completion)) r) :
    ∃ y, ∀ w, (realUnitsRes S ιr r w).hom y = t w := by
  obtain ⟨⟨y, _⟩, hy⟩ := (sUnitsRealPrimaryEquiv K S (nonempty_localEmbeddings K).some h2S hr).surjective
    (fun w => realLocalEquiv w r (t w))
  refine ⟨y, fun w => (realLocalEquiv w r).injective ?_⟩
  rw [← realLocalEquiv_realUnitsRes S ιr (nonempty_localEmbeddings K).some (by omega) w y]
  rw [sUnitsRealPrimaryEquiv_apply] at hy
  exact congrFun hy w

set_option maxHeartbeats 1000000 in

theorem realUnitsRes_tateToGlobal (n : ℕ) (x : unitsTateCohomology S ιr ιs (n + 1))
    (w : {v : InfinitePlace K.1 // v.IsReal}) :
    (realUnitsRes S ιr (n + 1) w).hom ((tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr)
      (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (n + 1)).hom x) =
        0 :=
  congrFun (congrArg Prod.snd (hom_apply_hom_apply_of_comp_eq (tateToGlobal_tateGlobalToLocal
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) n) x)) w

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_realUnitsRes_eq_of_three_le {m : ℕ} (hm : 3 ≤ m + 1)
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1)) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1), ∀ w, (realUnitsRes S ιr (m + 1) w).hom y = t w := by
  rcases Nat.even_or_odd (m + 1) with he | ho
  · exact exists_realUnitsRes_eq S ιr h2S (r := m + 1) (by obtain ⟨j, hj⟩ := he; omega) t
  · exact ⟨0, fun w => @Subsingleton.elim _ (subsingleton_realLocal_of_odd w ho) _ _⟩

set_option maxHeartbeats 2000000 in

theorem tateGlobalToLocal_units_eq {m : ℕ} (hm : 3 ≤ m + 1)
    (t : (∀ v : S, cohomology (finUnits S v) (m + 1)) ×
      (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1)))
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1)) (hy : ∀ w, (realUnitsRes S ιr (m + 1) w).hom y = t.2 w) :
    (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1)).hom y = t := by
  have h1 : (globalToLocal (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
      (m + 1)).hom y = t.1 := funext fun v => @Subsingleton.elim _ (subsingleton_finLocal S v hm) _ _
  exact Prod.ext h1 (funext hy)

include h2S in

theorem exists_tateGlobalToLocal_eq {m : ℕ} (hm : 3 ≤ m + 1)
    (t : (∀ v : S, cohomology (finUnits S v) (m + 1)) ×
      (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) (m + 1))) :
    ∃ g : cohomology (galSUnitsMax K.1 ℚ̄ S) (m + 1),
      (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
        (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1)).hom g = t :=
  (exists_realUnitsRes_eq_of_three_le S ιr h2S hm t.2).imp fun y hy =>
    tateGlobalToLocal_units_eq S ιr ιs hm t y hy

set_option maxHeartbeats 1000000 in
include h2S in

theorem tateToGlobal_units_eq_zero {n : ℕ} (hn : 3 ≤ n) (x : unitsTateCohomology S ιr ιs (n + 1))
    {k : ℕ} (hk : 2 ^ k • x = 0) :
    (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (n + 1)).hom x = 0 := by
  refine eq_zero_of_realUnitsRes_eq_zero S ιr h2S (by omega) _ (k := k) ?_ fun w => ?_
  · rw [← map_nsmul, hk, map_zero]
  · exact realUnitsRes_tateToGlobal S ιr ιs n x w

set_option maxHeartbeats 1000000 in
include h2S in

theorem eq_zero_of_tateToGlobal_units_eq_zero {m : ℕ} (hm : 3 ≤ m + 1)
    (x : unitsTateCohomology S ιr ιs (m + 1 + 1))
    (hx : (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
      (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) (m + 1 + 1)).hom x = 0) : x = 0 := by
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_compact
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
    realUnits (realUnitsMor S ιr) (m + 1)) x hx
  obtain ⟨g, hg⟩ := exists_tateGlobalToLocal_eq S ιr ιs h2S hm t
  rw [← ht, ← hg]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact (gsFinFamily S ιs)
    (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) m) g

include h2S in

theorem eq_zero_unitsTateCohomology_of_two_pow_nsmul {r : ℕ} (hr : 4 ≤ r) (x : unitsTateCohomology S ιr ιs r)
    {k : ℕ} (hk : 2 ^ k • x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + 1 := ⟨r - 2, by omega⟩
  exact eq_zero_of_tateToGlobal_units_eq_zero S ιr ιs h2S (by omega) x
    (tateToGlobal_units_eq_zero S ιr ιs h2S (by omega) x hk)

end Real

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem exists_two_mem_place (K : FiniteSubfield) :
    ∃ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((2 : ℕ) : 𝓞 K.1) := by
    rintro ⟨u, hu⟩
    have h : ((2 : ℕ) : 𝓞 K.1) * ((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) = 1 := by
      rw [← hu]
      exact u.mul_inv
    have hK : ((2 : ℕ) : K.1) * (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = 1 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h
      rwa [map_mul, map_natCast, map_one] at this
    have hint : IsIntegral ℤ (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) :=
      NumberField.RingOfIntegers.isIntegral_coe _
    have heq : (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = algebraMap ℚ K.1 (1 / 2) := by
      rw [eq_inv_of_mul_eq_one_right hK]
      simp
    rw [heq, isIntegral_algebraMap_iff (algebraMap ℚ K.1).injective] at hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hy' : ((2 * y : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, show ((y : ℤ) : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
      norm_num
    have h2 : 2 * y = 1 := by exact_mod_cast hy'
    omega
  have hne : Ideal.span {((2 : ℕ) : 𝓞 K.1)} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have h2M : ((2 : ℕ) : 𝓞 K.1) ∈ M := hle (Ideal.subset_span rfl)
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at h2M
    have : ((2 : ℕ) : K.1) = 0 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h2M
      rwa [map_natCast, map_zero] at this
    norm_num at this
  exact ⟨⟨M, hM.isPrime, hMbot⟩, h2M⟩

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 1000000 in

theorem exists_two_nsmul_finLocal (v : HeightOneSpectrum (𝓞 K.1))
    (a : cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2) :
    ∃ u, 2 • u = a := by
  obtain ⟨u₀, hu₀⟩ := (placeInv_bijective_inr (K := K) v).2
    (qzDiv 2 (placeInv (K := K) (.inr v) (finLocalEquiv (K := K) v 2 a)))
  refine ⟨(finLocalEquiv (K := K) v 2).symm u₀, (finLocalEquiv (K := K) v 2).injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  apply (placeInv_bijective_inr (K := K) v).1
  rw [map_nsmul, hu₀, nsmul_qzDiv two_ne_zero]

section Maps

abbrev UnitsLoc (n : ℕ) : Type :=
  (∀ v : S, cohomology (finUnits S v) n) × (∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) n)

def unitsToGlobal (n : ℕ) : unitsTateCohomology S ιr ιs n →+ cohomology (galSUnitsMax K.1 ℚ̄ S) n :=
  (tateToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

def unitsGlobalToLocal (n : ℕ) : cohomology (galSUnitsMax K.1 ℚ̄ S) n →+ UnitsLoc S n :=
  (tateGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

def unitsLocalToCompact (n : ℕ) : UnitsLoc S n →+ unitsTateCohomology S ιr ιs (n + 1) :=
  (tateLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S)
    (finUnitsMor S ιs) realUnits (realUnitsMor S ιr) n).hom.toAddMonoidHom

set_option maxHeartbeats 1000000 in
theorem exists_unitsLocalToCompact_eq (n : ℕ) (x : unitsTateCohomology S ιr ιs (n + 1))
    (hx : unitsToGlobal S ιr ιs (n + 1) x = 0) : ∃ t, unitsLocalToCompact S ιr ιs n t = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_compact
    (gsFinFamily S ιs) (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs)
    realUnits (realUnitsMor S ιr) n) x hx

set_option maxHeartbeats 1000000 in
theorem unitsLocalToCompact_unitsGlobalToLocal (n : ℕ) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) (n + 1)) :
    unitsLocalToCompact S ιr ιs (n + 1) (unitsGlobalToLocal S ιr ιs (n + 1) g) = 0 :=
  hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact (gsFinFamily S ιs)
    (gsRealFamily S ιr) (galSUnitsMax K.1 ℚ̄ S) (finUnits S) (finUnitsMor S ιs) realUnits
    (realUnitsMor S ιr) n) g

set_option maxHeartbeats 1000000 in
theorem unitsLocalToCompact_two_unitsGlobalToLocal (g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    unitsLocalToCompact S ιr ιs 2 (unitsGlobalToLocal S ιr ιs 2 g) = 0 :=
  unitsLocalToCompact_unitsGlobalToLocal S ιr ιs 1 g


theorem unitsGlobalToLocal_snd (n : ℕ) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) n) (w) :
    (unitsGlobalToLocal S ιr ιs n g).2 w = (realUnitsRes S ιr n w).hom g :=
  rfl

end Maps

section Div

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 2000000 in
include h2S in

theorem exists_realUnitsRes_two_eq
    (t : ∀ w : {v : InfinitePlace K.1 // v.IsReal}, cohomology (realUnits w) 2) :
    ∃ g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2, ∀ w, (realUnitsRes S ιr 2 w).hom g = t w := by
  classical
  let ι : LocalEmbeddings K := (nonempty_localEmbeddings K).some
  obtain ⟨v₀, hv₀⟩ := exists_two_mem_place K
  have hv₀S : v₀ ∈ S := h2S v₀ hv₀
  let s : QZ := ∑ w, placeInv (K := K) (.inl w.1) (realLocalEquiv w 2 (t w))
  obtain ⟨c, hc⟩ := (placeInv_bijective_inr (K := K) v₀).2 (-s)
  let T : ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
    (∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
      DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c
  have h2t : ∀ w, 2 • realLocalEquiv w 2 (t w) = 0 := fun w => by
    rw [← map_nsmul, two_nsmul_realLocal w (by norm_num) (t w), map_zero]
  have h2s : 2 • s = 0 := by
    change 2 • (∑ w, placeInv (K := K) (.inl w.1) (realLocalEquiv w 2 (t w))) = 0
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun w _ => by rw [← map_nsmul, h2t w, map_zero]
  have h2c : 2 • c = 0 := by
    apply (placeInv_bijective_inr (K := K) v₀).1
    rw [map_nsmul, hc, map_zero, smul_neg, h2s, neg_zero]
  have hT : T ∈ localPrimaryKernel K S 2 := by
    refine ⟨⟨1, ?_⟩, fun v hv => ?_, ?_⟩
    · rw [pow_one]
      change 2 • ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
        DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) = 0
      rw [smul_add, Finset.smul_sum, ← map_nsmul, h2c, map_zero, add_zero]
      exact Finset.sum_eq_zero fun w _ => by rw [← map_nsmul, h2t w, map_zero]
    · change ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
        DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) (.inr v) = 0
      rw [DirectSum.add_apply, DFinsupp.finsetSum_apply,
        Finset.sum_eq_zero fun w _ => DirectSum.of_eq_of_ne _ _ _ (by simp),
        DirectSum.of_eq_of_ne _ _ _ (fun (h : (Sum.inr v : Place K.1) = .inr v₀) =>
          hv (by rw [Sum.inr_injective h]; exact hv₀S)), add_zero]
    · change sumPlaceInv K ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1)
        (realLocalEquiv w 2 (t w))) + DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) = 0
      rw [map_add, map_sum, sumPlaceInv_of, hc]
      simp only [sumPlaceInv_of]
      exact add_neg_cancel s
  let g₀ := (sUnitsH2PrimaryEquiv K S 2 Nat.prime_two h2S ι).symm ⟨T, hT⟩
  refine ⟨g₀.1, fun w => (realLocalEquiv w 2).injective ?_⟩
  have hg : brauerLocal ι (sUnitsBrauer K S g₀.1) = T := by
    have := coe_sUnitsH2PrimaryEquiv_apply K S 2 Nat.prime_two h2S ι g₀
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  have hw : brauerLocal ι (sUnitsBrauer K S g₀.1) (.inl w.1) =
      realLocalization ι (by norm_num : 1 ≤ 2) (sUnitsInfl K S 2 g₀.1) w := rfl
  rw [← realLocalEquiv_realUnitsRes S ιr ι (by norm_num) w, ← hw, hg]
  change ((∑ w, DirectSum.of (localGaloisCohomology K 2) (.inl w.1) (realLocalEquiv w 2 (t w))) +
    DirectSum.of (localGaloisCohomology K 2) (.inr v₀) c) (.inl w.1) = _
  rw [DirectSum.add_apply, DFinsupp.finsetSum_apply, DirectSum.of_eq_of_ne _ _ _ (by simp), add_zero,
    Finset.sum_eq_single w]
  · exact DirectSum.of_eq_same _ _
  · intro w' _ hw'
    exact DirectSum.of_eq_of_ne _ _ _ fun h => hw' (Subtype.ext (Sum.inl_injective h).symm)
  · intro h
    exact absurd (Finset.mem_univ w) h

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_eq_two_nsmul_add_unitsGlobalToLocal (t : UnitsLoc S 2) :
    ∃ (t' : UnitsLoc S 2) (g : cohomology (galSUnitsMax K.1 ℚ̄ S) 2),
      t = 2 • t' + unitsGlobalToLocal S ιr ιs 2 g := by
  refine (exists_realUnitsRes_two_eq S ιr h2S t.2).elim fun g hg => ?_
  have hu : ∀ v : S, ∃ u : cohomology (finUnits S v) 2, 2 • u = t.1 v - (unitsGlobalToLocal S ιr ιs 2 g).1 v :=
    fun v => exists_two_nsmul_finLocal (K := K) v.1 _
  choose u hu using hu
  refine ⟨(u, 0), g, Prod.ext (funext fun v => ?_) (funext fun w => ?_)⟩
  · change t.1 v = 2 • u v + (unitsGlobalToLocal S ιr ιs 2 g).1 v
    rw [hu v, sub_add_cancel]
  · change t.2 w = 2 • (0 : cohomology (realUnits w) 2) + (unitsGlobalToLocal S ιr ιs 2 g).2 w
    rw [smul_zero, zero_add, unitsGlobalToLocal_snd, hg w]

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_two_nsmul_unitsTate_three (z : unitsTateCohomology S ιr ιs (2 + 1)) : ∃ z', 2 • z' = z := by
  obtain ⟨N, hN⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isTorsion_cohomology (galSUnitsMax K.1 ℚ̄ S) (n := 2 + 1) (by norm_num) (unitsToGlobal S ιr ιs (2 + 1) z))
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hN.1.ne'
  have hby : unitsToGlobal S ιr ιs (2 + 1) (b • z) = 0 := by
    rw [map_nsmul]
    refine eq_zero_of_h3_sUnits K S 2 Nat.prime_two h2S _ a ?_
    rw [smul_smul, ← hab, hN.2]
  obtain ⟨t, ht⟩ := exists_unitsLocalToCompact_eq S ιr ιs 2 (b • z) hby
  obtain ⟨t', g, htg⟩ := exists_eq_two_nsmul_add_unitsGlobalToLocal S ιr ιs h2S t
  have hbz : b • z = 2 • unitsLocalToCompact S ιr ιs 2 t' :=
    ht.symm.trans ((congrArg (unitsLocalToCompact S ιr ιs 2) htg).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) (map_nsmul _ 2 t') (unitsLocalToCompact_two_unitsGlobalToLocal S ιr ιs g)).trans
        (add_zero _))))
  obtain ⟨c, rfl⟩ := hb
  refine ⟨unitsLocalToCompact S ιr ιs 2 t' - c • z, ?_⟩
  refine (smul_sub 2 (unitsLocalToCompact S ιr ιs 2 t') (c • z)).trans ?_
  refine (congrArg₂ (· - ·) hbz.symm (smul_smul 2 c z)).trans ?_
  rw [add_smul, one_smul, add_sub_cancel_left]

set_option maxHeartbeats 1000000 in
include h2S in

theorem exists_two_nsmul_unitsTate_of_four_le {m : ℕ} (hm : 3 ≤ m + 1)
    (x : unitsTateCohomology S ιr ιs (m + 1 + 1)) : ∃ x', 2 • x' = x := by
  obtain ⟨N, hN⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
    (isTorsion_cohomology (galSUnitsMax K.1 ℚ̄ S) (n := m + 1 + 1) (by omega)
      (unitsToGlobal S ιr ιs (m + 1 + 1) x))
  obtain ⟨t, ht⟩ := exists_unitsLocalToCompact_eq S ιr ιs (m + 1) (N • x) (by rw [map_nsmul, hN.2])
  have h2t : 2 • t = 0 := Prod.ext
    (funext fun v => @Subsingleton.elim _ (subsingleton_finLocal S v hm) _ _)
    (funext fun w => two_nsmul_realLocal w (by omega) (t.2 w))
  have hx : (2 * N) • x = 0 := by
    rw [mul_smul, ← ht, ← map_nsmul, h2t, map_zero]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : 2 * N ≠ 0)
  have hbx : b • x = 0 := eq_zero_unitsTateCohomology_of_two_pow_nsmul S ιr ιs h2S (by omega) (b • x)
    (k := a) (by rw [smul_smul, ← hab, hx])
  obtain ⟨c, rfl⟩ := hb
  refine ⟨(c + 1) • x, ?_⟩
  rw [smul_smul, show 2 * (c + 1) = (2 * c + 1) + 1 by ring, add_smul, hbx, one_smul, zero_add]

include h2S in

theorem exists_two_nsmul_unitsTateCohomology {r : ℕ} (hr : 3 ≤ r) (x : unitsTateCohomology S ιr ιs r) :
    ∃ x', 2 • x' = x := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + 1 := ⟨r - 2, by omega⟩
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    exact exists_two_nsmul_unitsTate_three S ιr ιs h2S x
  · exact exists_two_nsmul_unitsTate_of_four_le S ιr ιs h2S (by omega) x

end Div

end

end GroundTheory.ProfCoh
end
