import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighInfl
import GroundTheory.ProfiniteCohomology.RestrictedRamification.CohomologyMapAlongInvariantsGsKernelMorCompGsBra
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnits
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.ColimitUnion
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Primary

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {ℓ : ℕ} {f : X →+ Y}

theorem IsIsoModCoprime.eq_zero_of_pow_nsmul (h : IsIsoModCoprime ℓ f) {x : X} (hx : f x = 0) {k : ℕ}
    (hk : ℓ ^ k • x = 0) : x = 0 := by
  obtain ⟨m, hm, hmx⟩ := h.1 x hx
  exact eq_zero_of_coprime_nsmul_eq_zero hm hmx hk

theorem IsIsoModCoprime.exists_pow_nsmul (h : IsIsoModCoprime ℓ f) (hℓ : ℓ.Prime) (hX : IsAddTorsion X)
    {y : Y} {k : ℕ} (hk : ℓ ^ k • y = 0) : ∃ x, (∃ j : ℕ, ℓ ^ j • x = 0) ∧ f x = y := by
  obtain ⟨m, hm, x, hx⟩ := h.2 y
  obtain ⟨u, w, huw⟩ : IsCoprime (m : ℤ) ((ℓ ^ k : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (hm.pow_right k)
  have hy : f (u • x) = y := by
    rw [map_zsmul, hx]
    calc u • (m • y) = (u * m) • y := by rw [mul_smul, natCast_zsmul]
      _ = (u * m + w * ((ℓ ^ k : ℕ) : ℤ)) • y := by
        rw [add_smul, mul_smul w, natCast_zsmul, hk, smul_zero, add_zero]
      _ = y := by rw [huw, one_smul]
  obtain ⟨x', hx', hfx'⟩ := exists_primary_map_eq f hℓ (hX (u • x)) (k := k) (by rw [hy]; exact hk)
  exact ⟨x', hx', hfx'.trans hy⟩

def primaryComponentMap (ℓ : ℕ) (f : X →+ Y) :
    AddCommGroup.primaryComponent X ℓ →+ AddCommGroup.primaryComponent Y ℓ :=
  (f.comp (AddCommGroup.primaryComponent X ℓ).subtype).codRestrict _ fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, (map_nsmul f _ _).symm.trans ((congrArg f hk).trans (map_zero f))⟩


theorem IsIsoModCoprime.bijective_primaryComponentMap (h : IsIsoModCoprime ℓ f) (hℓ : ℓ.Prime)
    (hX : IsAddTorsion X) : Function.Bijective (primaryComponentMap ℓ f) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨k, hk⟩ := x.2
    exact Subtype.ext (h.eq_zero_of_pow_nsmul (congrArg Subtype.val hx) hk)
  · obtain ⟨k, hk⟩ := y.2
    obtain ⟨x, ⟨j, hj⟩, hx⟩ := h.exists_pow_nsmul hℓ hX hk
    exact ⟨⟨x, j, hj⟩, Subtype.ext hx⟩

end Primary

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

section Kernel

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem eq_zero_cohomology_gsKernel_of_three_le {r : ℕ} (hr : 3 ≤ r)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) r) : y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) r y
  obtain ⟨L, hL, hLS, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum L F₂
  have : Fact (F₂ ≤ E) := CyclotomicSymbol.fact_le_compositum_right L F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 E.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ E)
  have : IsTotallyComplex E.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) E.1
  have hLE : Fact (L ≤ E) := CyclotomicSymbol.fact_le_compositum_left L F₂
  have : Fact (K ≤ E) := ⟨hL.out.trans hLE.out⟩
  have hES : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    have hle : E.1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
      change L.1 ⊔ F₂.1 ≤ _
      refine sup_le (fun x hx => hLS x hx) fun x hx => ?_
      exact mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS 2 x hx
    exact fun x hx => hle hx
  have hNE : gsKernel K S ≤ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (mem_gsKernel_iff K S σ).1 hσ x (hES x hx)
  have hEL := fixingSubgroup_subgroupOf_mono (K := K) hLE.out
  have hz : (cohomologyResLE (unitsLimitRep K) hEL r).hom y' = 0 := by
    apply unitsSubgroupOfMap_injective E r
    have : Subsingleton (cohomology (unitsLimitRep E) r) :=
      subsingleton_cohomology_unitsLimitRep_of_three_le (fun v => IsTotallyComplex.isComplex v) hr
    exact Subsingleton.elim _ _
  rw [← cohomologyResLE_comp (unitsLimitRep K) hEL hNE r, ConcreteCategory.comp_apply, hz, map_zero]

include hℓ hS in

theorem exists_coprime_nsmul_cohomology_gsKernel {i : ℕ} (hi : 1 ≤ i)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) i) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · have := ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_gsKernel K S)
    exact ⟨1, Nat.coprime_one_left ℓ, Subsingleton.elim _ _⟩
  · exact exists_coprime_smul_cohomology_two_gsKernel K S hℓ hS y
  · exact ⟨1, Nat.coprime_one_left ℓ, by rw [eq_zero_cohomology_gsKernel_of_three_le K S hℓ hS h3 y, smul_zero]⟩

end Kernel

def gsUnitsInfl (r : ℕ) :
    cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r →+ cohomology (unitsLimitRep K) r :=
  (gsBrauerInfl K S r).hom.toAddMonoidHom.comp
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r).toAddMonoidHom

theorem gsUnitsInfl_apply (r : ℕ) (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) :
    gsUnitsInfl K S r x =
      (gsBrauerInfl K S r).hom (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r x) :=
  rfl

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem isIsoModCoprime_gsUnitsInfl {r : ℕ} (hr : 1 ≤ r) : IsIsoModCoprime ℓ (gsUnitsInfl K S r) := by
  have h := isIsoModCoprime_cohomologyInfl (isClosed_gsKernel K S) ℓ hr
    (fun i hi y => exists_coprime_nsmul_cohomology_gsKernel K S hℓ hS hi y)
  have hsurj : Function.Surjective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have he : ∀ x, (cohomologyInfl (unitsLimitRep K) (gsKernel K S) r).hom x =
      (gsBrauerInfl K S r).hom ((cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
        (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom x) := fun x =>
    (congrArg (fun φ => φ.hom x) (cohomologyMapAlong_invariantsGsKernelMor_comp_gsBrauerInfl K S r)).symm
  have h' : IsIsoModCoprime ℓ (gsBrauerInfl K S r).hom.toAddMonoidHom :=
    IsIsoModCoprime.of_comp_surjective (e := (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) r).hom.toAddMonoidHom) (h.congr he) hsurj
  exact h'.comp (IsIsoModCoprime.of_bijective
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r).bijective)

include hℓ hS in

theorem eq_zero_of_gsUnitsInfl_eq_zero {r : ℕ} (hr : 1 ≤ r)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) (hx : gsUnitsInfl K S r x = 0) {k : ℕ}
    (hk : ℓ ^ k • x = 0) : x = 0 :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).eq_zero_of_pow_nsmul hx hk

include hℓ hS in

theorem exists_gsUnitsInfl_eq {r : ℕ} (hr : 1 ≤ r) (y : cohomology (unitsLimitRep K) r) {k : ℕ}
    (hk : ℓ ^ k • y = 0) : ∃ x, (∃ j : ℕ, ℓ ^ j • x = 0) ∧ gsUnitsInfl K S r x = y :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).exists_pow_nsmul hℓ (isTorsion_cohomology _ hr) hk

noncomputable def gsUnitsInflPrimaryEquiv {r : ℕ} (hr : 1 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) ℓ :=
  AddEquiv.ofBijective (primaryComponentMap ℓ (gsUnitsInfl K S r))
    ((isIsoModCoprime_gsUnitsInfl K S hℓ hS hr).bijective_primaryComponentMap hℓ (isTorsion_cohomology _ hr))


end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem exists_coprime_nsmul_of_primary_eq_zero {M : Type*} [AddCommGroup M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hM : ∀ y : M, ∀ k : ℕ, ℓ ^ k • y = 0 → y = 0) {x : M} (hx : IsOfFinAddOrder x) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • x = 0 := by
  have hn : addOrderOf x ≠ 0 := hx.addOrderOf_pos.ne'
  have hnm : ℓ ^ (addOrderOf x).factorization ℓ * (addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ) =
      addOrderOf x := Nat.ordProj_mul_ordCompl_eq_self _ ℓ
  refine ⟨addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ, (Nat.coprime_ordCompl hℓ hn).symm,
    hM _ ((addOrderOf x).factorization ℓ) ?_⟩
  rw [smul_smul, hnm]
  exact addOrderOf_nsmul_eq_zero x

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hD : ∀ p : ℕ, 2 ≤ p → ∀ x : cohomology (gsDiv K S ιs QZ) p, ∀ k : ℕ, ℓ ^ k • x = 0 → x = 0)

include hℓ hD in

theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_int {q : ℕ} (hq : 3 ≤ q) (x : cohomology (gsDiv K S ιs ℤ) q)
    (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  have hX := divFunSequence_shortExact (gsDecomp K S ιs)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hzero : IsZero (cohomology (divFunSequence (gsDecomp K S ιs)).X₂ (p + 1)) :=
    isZero_cohomology_of_bijective_nsmul_ulift _ (fun n hn => bijective_nsmul_divFun_rat _ hn) (by omega)
  have hs := ModuleCat.subsingleton_of_isZero hzero
  let x' : cohomology (divFunSequence (gsDecomp K S ιs)).X₁ (p + 1) := x
  obtain ⟨y, hy⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hX p (p + 1) rfl x' (Subsingleton.elim _ _)
  have hx' : ℓ ^ k • x' = 0 := hx
  have hk : ℓ ^ k • (δ hX p (p + 1) rfl).hom.toAddMonoidHom y = 0 :=
    (congrArg (fun t => ℓ ^ k • t) hy).trans hx'
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (δ hX p (p + 1) rfl).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ (by omega) y) hk
  have h0 : y' = 0 := hD p (by omega) y' j hj
  have e : x' = (δ hX p (p + 1) rfl).hom y' := hy.symm.trans hy'.symm
  rw [h0, map_zero] at e
  exact e

include hℓ hS hD in

theorem eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits {q : ℕ} (hq : 3 ≤ q)
    (x : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  have hP := picSequence_shortExact K S ιs
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  let x' : cohomology (picSequence K S ιs).X₁ (p + 1) := x
  have hx' : ℓ ^ k • x' = 0 := hx
  have hxD : (cohomologyMap (picSequence K S ιs).f (p + 1)).hom x' = 0 :=
    eq_zero_of_pow_nsmul_cohomology_gsDiv_int K S ιs hℓ hD hq _ k
      ((map_nsmul (cohomologyMap (picSequence K S ιs).f (p + 1)).hom (ℓ ^ k) x').symm.trans
        ((congrArg _ hx').trans (map_zero _)))
  exact eq_zero_of_mem_range_δ_of_coprime hP p (p + 1) rfl
    (exists_δ_eq_of_cohomologyMap_f_eq_zero hP p (p + 1) rfl x' hxD) ℓ
    (fun r => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
      (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) p r) k hx

include hℓ hS hD in

theorem isIsoModCoprime_sUnitsToUnits {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom := by
  have hQ := sUnitsQuotSequence_shortExact K.1 ℚ̄ S
  have hP : ∀ q, 3 ≤ q → ∀ w : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q,
      ∃ m : ℕ, m.Coprime ℓ ∧ m • w = 0 := fun q hq w =>
    exists_coprime_nsmul_of_primary_eq_zero hℓ
      (fun w' k hk => eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits K S ιs hℓ hS hD hq w' k hk)
      (isTorsion_cohomology _ (by omega) w)
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine ⟨fun z hz => ?_, fun y => ?_⟩
  · let z' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ (p + 1) := z
    obtain ⟨w, hw⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hQ p (p + 1) rfl z' hz
    obtain ⟨m, hm, hmw⟩ := hP p (by omega) w
    refine ⟨m, hm, ?_⟩
    have e : m • z' = 0 := by
      rw [← hw, ← map_nsmul]
      exact (congrArg _ hmw).trans (map_zero _)
    exact e
  · let y' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ (p + 1) := y
    obtain ⟨m, hm, hmy⟩ := hP (p + 1) (by omega) ((cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom y')
    have hg : (cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom (m • y') = 0 :=
      (map_nsmul _ m y').trans hmy
    obtain ⟨z, hz⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero hQ (p + 1) (m • y') hg
    exact ⟨m, hm, z, hz⟩

def sUnitsInfl (r : ℕ) : cohomology (galSUnitsMax K.1 ℚ̄ S) r →+ cohomology (unitsLimitRep K) r :=
  (gsUnitsInfl K S r).comp (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom

theorem sUnitsInfl_apply (r : ℕ) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    sUnitsInfl K S r y = gsUnitsInfl K S r ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom y) :=
  rfl

include hℓ hS hD in

theorem isIsoModCoprime_sUnitsInfl_of_divisor {r : ℕ} (hr : 4 ≤ r) : IsIsoModCoprime ℓ (sUnitsInfl K S r) :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS (by omega)).comp (isIsoModCoprime_sUnitsToUnits K S ιs hℓ hS hD hr)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

noncomputable section

section Primary

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

def PrimaryVanishes (ℓ p : ℕ) (M : Rep.{0} k G) [IsDiscreteRep M] : Prop :=
  ∀ (x : cohomology M p) (k : ℕ), ℓ ^ k • x = 0 → x = 0

theorem PrimaryVanishes.of_shortExact {S : ShortComplex (Rep.{0} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : 1 ≤ p)
    (h₁ : PrimaryVanishes ℓ p S.X₁) (h₃ : PrimaryVanishes ℓ p S.X₃) : PrimaryVanishes ℓ p S.X₂ := by
  intro x k hx
  have hg : (cohomologyMap S.g p).hom x = 0 :=
    h₃ _ k (by rw [← map_nsmul, hx, map_zero])
  obtain ⟨y, rfl⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero hS p x hg
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (cohomologyMap S.f p).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ hp y) (k := k) hx
  have : y' = 0 := h₁ y' j hj
  refine hy'.symm.trans ?_
  change (cohomologyMap S.f p).hom y' = 0
  rw [this, map_zero]

theorem PrimaryVanishes.of_union (M : Rep.{0} k G) [IsDiscreteRep M] {ι : Type} [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] (W : ι → Submodule k M) (hW : Monotone W)
    (hstable : ∀ i g, W i ≤ (W i).comap (M.ρ g)) (hunion : ∀ a : M, ∃ i, a ∈ W i) {ℓ p : ℕ}
    (hW' : ∀ i (y : cohomology (M.subrepresentation (W i) (hstable i)) p) (k : ℕ), ℓ ^ k • y = 0 →
      ∃ (j : ι) (h : i ≤ j), (cohomologyMap (subrepInclusion M W hW hstable h) p).hom y = 0) :
    PrimaryVanishes ℓ p M := by
  intro x k hx
  obtain ⟨i, y, rfl⟩ := exists_cohomologyMap_subtype_eq M W hW hstable hunion p x
  have hy : (cohomologyMap (Rep.subtype M (W i) (hstable i)) p).hom (ℓ ^ k • y) = 0 := by
    rw [map_nsmul]
    exact hx
  obtain ⟨j, hij, hj⟩ := exists_cohomologyMap_subrepInclusion_eq_zero M W hW hstable hunion p i _ hy
  rw [map_nsmul] at hj
  obtain ⟨l, hjl, hl⟩ := hW' j _ k hj
  have e : subrepInclusion M W hW hstable hij ≫ subrepInclusion M W hW hstable hjl ≫
      Rep.subtype M (W l) (hstable l) = Rep.subtype M (W i) (hstable i) := by
    rw [subrepInclusion_comp_subtype, subrepInclusion_comp_subtype]
  rw [← e, cohomologyMap_comp, cohomologyMap_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hl, map_zero]

end Primary

section Single

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {H₀ : Type} [Group H₀] (ψ : H₀ →* G)

abbrev divFunRepOne : Rep.{0} (ULift.{0} ℤ) G :=
  divFunRep (I := PUnit) (H := fun _ => H₀) (fun _ => ψ) QZ

def OpenSubgroupAbove (Z : Subgroup G) : Type :=
  {U : OpenSubgroup G // Z ≤ (U : Subgroup G)}

instance (Z : Subgroup G) : Preorder (OpenSubgroupAbove Z) where
  le a b := (b.1 : Subgroup G) ≤ a.1
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab

instance (Z : Subgroup G) : Nonempty (OpenSubgroupAbove Z) :=
  ⟨⟨⊤, le_top⟩⟩

instance (Z : Subgroup G) : IsDirectedOrder (OpenSubgroupAbove Z) :=
  ⟨fun a b => ⟨⟨a.1 ⊓ b.1, fun z hz => ⟨a.2 hz, b.2 hz⟩⟩, fun x hx => hx.1, fun x hx => hx.2⟩⟩

abbrev trivQZRes (U : OpenSubgroup G) : Rep.{0} (ULift.{0} ℤ) (U : Subgroup G) :=
  Rep.res (U : Subgroup G).subtype (trivRep G QZ)

instance isDiscreteRep_trivQZRes (U : OpenSubgroup G) : IsDiscreteRep (trivQZRes U) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_coind_trivQZRes (U : OpenSubgroup G) :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (trivQZRes U)) :=
  isDiscreteRep_coind U _

instance isDiscreteRep_res_subtype_trivRepQZ (Z : Subgroup G) :
    IsDiscreteRep (Rep.res Z.subtype (trivRep G QZ)) :=
  isDiscreteRep_res_subtype _ _

def coindToDivFunOne (U : OpenSubgroup G) (hU : ψ.range ≤ (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype (trivQZRes U) ⟶ divFunRepOne ψ :=
  Rep.ofHom ⟨{
      toFun := fun F => ⟨fun _ => F.1, Set.toFinite _, fun _ =>
        ⟨isLocallyConstant_coind U (trivQZRes U) F, fun h x => by
          have := F.2 ⟨ψ h, hU ⟨h, rfl⟩⟩ x
          exact this⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

theorem coindToDivFunOne_injective (U : OpenSubgroup G) (hU : ψ.range ≤ (U : Subgroup G)) :
    Function.Injective (coindToDivFunOne ψ U hU).hom := fun F F' h =>
  Subtype.ext (congrFun (congrArg Subtype.val h) PUnit.unit)

end Single

section SingleVanish

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {H₀ : Type} [Group H₀] (ψ : H₀ →* G)

def coindIncl {U U' : OpenSubgroup G} (h : (U' : Subgroup G) ≤ U) :
    Rep.coind (U : Subgroup G).subtype (trivQZRes U) ⟶ Rep.coind (U' : Subgroup G).subtype (trivQZRes U') :=
  Rep.ofHom ⟨{
      toFun := fun F => ⟨F.1, fun g x => F.2 ⟨g, h g.2⟩ x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

theorem cohomologyMap_coindIncl_comp_shapiroMap {U U' : OpenSubgroup G} (h : (U' : Subgroup G) ≤ U) (n : ℕ) :
    cohomologyMap (coindIncl h) n ≫ shapiroMap U' (trivQZRes U') n =
      shapiroMap U (trivQZRes U) n ≫ cohomologyResLE (trivRep G QZ) h n := by
  rw [shapiroMap, shapiroMap, cohomologyResLE, ← cohomologyMapAlong_id_eq_cohomologyMap,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

def divFunOneLevel (a : OpenSubgroupAbove ψ.range) : Submodule (ULift.{0} ℤ) (divFunRepOne ψ) :=
  LinearMap.range (coindToDivFunOne ψ a.1 a.2).hom.toLinearMap

theorem divFunOneLevel_stable (a : OpenSubgroupAbove ψ.range) (g : G) :
    divFunOneLevel ψ a ≤ (divFunOneLevel ψ a).comap ((divFunRepOne ψ).ρ g) :=
  range_repHom_le_comap _ g

instance isDiscreteRep_divFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    IsDiscreteRep ((divFunRepOne ψ).subrepresentation (divFunOneLevel ψ a) (divFunOneLevel_stable ψ a)) :=
  isDiscreteRep_subrepresentation _ _ _

theorem divFunOneLevel_mono : Monotone (divFunOneLevel ψ) := by
  intro a b hab
  rintro _ ⟨F, rfl⟩
  exact ⟨(coindIncl hab).hom F, rfl⟩

omit [TotallyDisconnectedSpace G] in

theorem exists_mem_divFunOneLevel [TotallyDisconnectedSpace G] (f : divFunRepOne ψ) :
    ∃ a, f ∈ divFunOneLevel ψ a := by
  obtain ⟨hlc, hinv⟩ := f.2.2 PUnit.unit
  obtain ⟨V, hV, hVf⟩ := exists_mem_nhds_one_forall_mul_eq hlc
  obtain ⟨W, hWV, hWo, h1W⟩ := mem_nhds_iff.1 hV
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  let U : OpenSubgroup G := ⟨ψ.range ⊔ (N : Subgroup G), Subgroup.isOpen_mono le_sup_right N.isOpen'⟩
  have hU : ψ.range ≤ (U : Subgroup G) := le_sup_left
  have hF : ∀ (g : (U : Subgroup G)) (x : G), (f : PUnit → G → QZ) PUnit.unit ((U : Subgroup G).subtype g * x) =
      (trivQZRes U).ρ g ((f : PUnit → G → QZ) PUnit.unit x) := by
    intro g x
    obtain ⟨m, ⟨h, rfl⟩, v, hv, hmv⟩ := Subgroup.mem_sup_of_normal_right.1 g.2
    change (f : PUnit → G → QZ) PUnit.unit ((g : G) * x) = (f : PUnit → G → QZ) PUnit.unit x
    have hv' : x⁻¹ * v * x ∈ (N : Subgroup G) := by
      have := Subgroup.Normal.conj_mem inferInstance v hv x⁻¹
      rwa [inv_inv] at this
    rw [← hmv, show ψ h * v * x = ψ h * (x * (x⁻¹ * v * x)) by group, hinv,
      hVf x _ (hWV (hN hv'))]
  refine ⟨⟨U, hU⟩, ⟨⟨(f : PUnit → G → QZ) PUnit.unit, hF⟩, ?_⟩⟩
  apply Subtype.ext
  funext u
  rfl

def coindToDivFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    Rep.coind (a.1 : Subgroup G).subtype (trivQZRes a.1) ⟶
      (divFunRepOne ψ).subrepresentation (divFunOneLevel ψ a) (divFunOneLevel_stable ψ a) :=
  Rep.ofHom ⟨LinearMap.codRestrict (divFunOneLevel ψ a) (coindToDivFunOne ψ a.1 a.2).hom.toLinearMap
      (fun F => ⟨F, rfl⟩), fun _ => rfl⟩

theorem coindToDivFunOneLevel_bijective (a : OpenSubgroupAbove ψ.range) :
    Function.Bijective (coindToDivFunOneLevel ψ a).hom :=
  ⟨fun F F' h => coindToDivFunOne_injective ψ a.1 a.2 (congrArg Subtype.val h), fun y => by
    obtain ⟨F, hF⟩ := y.2
    exact ⟨F, Subtype.ext hF⟩⟩

instance isIso_coindToDivFunOneLevel (a : OpenSubgroupAbove ψ.range) :
    IsIso (coindToDivFunOneLevel ψ a) := by
  have : Mono (coindToDivFunOneLevel ψ a) :=
    (Rep.mono_iff_injective _).2 (coindToDivFunOneLevel_bijective ψ a).1
  have : Epi (coindToDivFunOneLevel ψ a) :=
    (Rep.epi_iff_surjective _).2 (coindToDivFunOneLevel_bijective ψ a).2
  exact isIso_of_mono_of_epi _

theorem coindToDivFunOneLevel_comp_subrepInclusion {a b : OpenSubgroupAbove ψ.range} (hab : a ≤ b) :
    coindToDivFunOneLevel ψ a ≫ subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab =
      coindIncl hab ≫ coindToDivFunOneLevel ψ b :=
  rfl

theorem bijective_cohomologyMap_of_isIso {k : Type} [CommRing k] {A B : Rep.{0} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (f : A ⟶ B) [IsIso f] (n : ℕ) : Function.Bijective (cohomologyMap f n).hom := by
  have : IsIso (cohomologyMap f n) :=
    ⟨cohomologyMap (inv f) n, by rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id],
      by rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]⟩
  exact ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

theorem primaryVanishes_divFunRepOne (hZ : IsClosed (ψ.range : Set G)) {ℓ p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ x : cohomology (Rep.res ψ.range.subtype (trivRep G QZ)) p, (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0) :
    PrimaryVanishes ℓ p (divFunRepOne ψ) := by
  refine PrimaryVanishes.of_union (divFunRepOne ψ) (divFunOneLevel ψ) (divFunOneLevel_mono ψ)
    (divFunOneLevel_stable ψ) (exists_mem_divFunOneLevel ψ) fun a y k hy => ?_
  obtain ⟨x, rfl⟩ := (bijective_cohomologyMap_of_isIso (coindToDivFunOneLevel ψ a) p).2 y
  have hx : ℓ ^ k • x = 0 := (bijective_cohomologyMap_of_isIso (coindToDivFunOneLevel ψ a) p).1
    (by rw [map_nsmul, hy, map_zero])
  set z := (shapiroMap a.1 (trivQZRes a.1) p).hom x with hzdef
  have hz : ℓ ^ k • z = 0 := by rw [hzdef, ← map_nsmul, hx, map_zero]
  have hw : (cohomologyResLE (trivRep G QZ) a.2 p).hom z = 0 :=
    hloc _ ⟨k, by rw [← map_nsmul, hz, map_zero]⟩
  rw [cohomologyResLE_apply_eq_zero_iff] at hw
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hZc : IsClosed ((ψ.range.subgroupOf (a.1 : Subgroup G) : Subgroup (a.1 : Subgroup G)) :
      Set (a.1 : Subgroup G)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hZ.preimage continuous_subtype_val
  obtain ⟨U₀, hU₀o, hZU₀, hU₀⟩ := exists_cohomologyRes_eq_zero (M := trivQZRes a.1) hZc q z hw
  have hopen : IsOpen ((U₀.map (a.1 : Subgroup G).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact (a.1.isOpen).isOpenMap_subtype_val _ hU₀o
  let U' : OpenSubgroup G := ⟨U₀.map (a.1 : Subgroup G).subtype, hopen⟩
  have hU'a : (U' : Subgroup G) ≤ a.1 := Subgroup.map_subtype_le U₀
  have hZU' : ψ.range ≤ (U' : Subgroup G) := fun z hz =>
    ⟨⟨z, a.2 hz⟩, hZU₀ (show (⟨z, a.2 hz⟩ : (a.1 : Subgroup G)) ∈ ψ.range.subgroupOf (a.1 : Subgroup G) from hz), rfl⟩
  let b : OpenSubgroupAbove ψ.range := ⟨U', hZU'⟩
  have hab : a ≤ b := hU'a
  have : IsDiscreteRep (Rep.coind (b.1 : Subgroup G).subtype (trivQZRes b.1)) :=
    isDiscreteRep_coind_trivQZRes b.1
  have hres : (cohomologyResLE (trivRep G QZ) hU'a (q + 1)).hom z = 0 := by
    rw [cohomologyResLE_apply_eq_zero_iff]
    have e : (U' : Subgroup G).subgroupOf (a.1 : Subgroup G) = U₀ :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) U₀
    rw [e]
    exact hU₀
  have hsh : (shapiroMap b.1 (trivQZRes b.1) (q + 1)).hom ((cohomologyMap (coindIncl hab) (q + 1)).hom x) = 0 := by
    have := congrArg (fun φ => φ.hom x) (cohomologyMap_coindIncl_comp_shapiroMap hab (q + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    exact hres
  have hinj : Function.Injective (shapiroMap b.1 (trivQZRes b.1) (q + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h0 : (cohomologyMap (coindIncl hab) (q + 1)).hom x = 0 := hinj (hsh.trans (map_zero _).symm)
  refine ⟨b, hab, ?_⟩
  calc (cohomologyMap (subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab) (q + 1)).hom
        ((cohomologyMap (coindToDivFunOneLevel ψ a) (q + 1)).hom x)
      = (cohomologyMap (coindToDivFunOneLevel ψ a ≫
          subrepInclusion _ _ (divFunOneLevel_mono ψ) (divFunOneLevel_stable ψ) hab) (q + 1)).hom x := by
        rw [cohomologyMap_comp]
        rfl
    _ = (cohomologyMap (coindIncl hab ≫ coindToDivFunOneLevel ψ b) (q + 1)).hom x := by
        rw [coindToDivFunOneLevel_comp_subrepInclusion]
    _ = 0 := by
        rw [cohomologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h0, map_zero]

end SingleVanish

section Family

attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {I : Type} {H : I → Type} [∀ i, Group (H i)] (φ : ∀ i, H i →* G)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem ker_repHom_le_comap {k : Type} [CommRing k] {A B : Rep.{0} k G} (f : A ⟶ B) (g : G) :
    LinearMap.ker f.hom.toLinearMap ≤ (LinearMap.ker f.hom.toLinearMap).comap (A.ρ g) := by
  intro a ha
  change f.hom (A.ρ g a) = 0
  rw [Rep.hom_comm_apply]
  change B.ρ g (f.hom a) = 0
  rw [show f.hom a = 0 from ha, map_zero]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem mem_divFun_ite (T : Finset I) (f : divFun φ QZ) :
    (fun i => if i ∈ T then 0 else (f : I → G → QZ) i) ∈ divFun φ QZ := by
  refine ⟨f.2.1.subset fun i hi => ?_, fun i => ?_⟩
  · intro hc
    apply hi
    simp only [hc, ite_self]
  · by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩
    · simp only [hi, if_false]
      exact f.2.2 i

def divFunOutside (T : Finset I) : divFunRep φ QZ ⟶ divFunRep φ QZ :=
  Rep.ofHom ⟨{
      toFun := fun f => ⟨_, mem_divFun_ite φ T f⟩
      map_add' := fun f f' => by
        apply Subtype.ext
        funext i x
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi]
      map_smul' := fun c f => by
        apply Subtype.ext
        funext i x
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi] }, fun g => by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext i x
    show ((if i ∈ T then 0 else ((divFunAction φ QZ g f : divFun φ QZ) : I → G → QZ) i) : G → QZ) x =
      (if i ∈ T then (0 : G → QZ) else (f : I → G → QZ) i) (x * g)
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [hi, coe_divFunAction_apply]⟩

def divFunSupp (T : Finset I) : Submodule (ULift.{0} ℤ) (divFunRep φ QZ) :=
  LinearMap.ker (divFunOutside φ T).hom.toLinearMap

theorem mem_divFunSupp_iff (T : Finset I) (f : divFunRep φ QZ) :
    f ∈ divFunSupp φ T ↔ ∀ i, i ∉ T → (f.1 : I → G → QZ) i = 0 := by
  constructor
  · intro hf i hi
    have := congrFun (congrArg Subtype.val (show (divFunOutside φ T).hom f = 0 from hf)) i
    simpa [divFunOutside, hi] using this
  · intro hf
    apply Subtype.ext
    funext i
    change (if i ∈ T then 0 else (f : I → G → QZ) i) = 0
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [hi, hf i hi]

theorem divFunSupp_stable (T : Finset I) (g : G) :
    divFunSupp φ T ≤ (divFunSupp φ T).comap ((divFunRep φ QZ).ρ g) :=
  ker_repHom_le_comap _ g

instance isDiscreteRep_divFunSupp (T : Finset I) :
    IsDiscreteRep ((divFunRep φ QZ).subrepresentation (divFunSupp φ T) (divFunSupp_stable φ T)) :=
  isDiscreteRep_subrepresentation _ _ _

theorem divFunSupp_mono : Monotone (divFunSupp φ) := fun T T' h f hf =>
  (mem_divFunSupp_iff φ T' f).2 fun i hi => (mem_divFunSupp_iff φ T f).1 hf i fun hiT => hi (h hiT)

def divFunSuppComponent (T : Finset I) (j : I) :
    (divFunRep φ QZ).subrepresentation (divFunSupp φ (insert j T)) (divFunSupp_stable φ _) ⟶
      divFunRepOne (φ j) :=
  Rep.ofHom ⟨{
      toFun := fun f => ⟨fun _ => ((f.1 : divFun φ QZ) : I → G → QZ) j, Set.toFinite _, fun _ => f.1.2.2 j⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun _ => rfl⟩

def divFunSuppSequence (T : Finset I) (j : I) (hj : j ∉ T) : ShortComplex (Rep.{0} (ULift.{0} ℤ) G) :=
  ShortComplex.mk (subrepInclusion (divFunRep φ QZ) (divFunSupp φ) (divFunSupp_mono φ) (divFunSupp_stable φ)
      (Finset.subset_insert j T)) (divFunSuppComponent φ T j) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext _ x
    exact congrFun ((mem_divFunSupp_iff φ T f.1).1 f.2 j hj) x)

instance isDiscreteRep_divFunSuppSequence_X₁ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₁ :=
  isDiscreteRep_divFunSupp φ T

instance isDiscreteRep_divFunSuppSequence_X₂ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₂ :=
  isDiscreteRep_divFunSupp φ (insert j T)

instance isDiscreteRep_divFunSuppSequence_X₃ (T : Finset I) (j : I) (hj : j ∉ T) :
    IsDiscreteRep (divFunSuppSequence φ T j hj).X₃ :=
  (inferInstance : IsDiscreteRep (divFunRepOne (φ j)))

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem single_mem_divFun (j : I) (F : G → QZ) (hF : IsLocallyConstant F ∧ ∀ (h : H j) (x : G), F (φ j h * x) = F x) :
    (Pi.single j F : I → G → QZ) ∈ divFun φ QZ := by
  refine ⟨(Set.finite_singleton j).subset fun i hi => ?_, fun i => ?_⟩
  · by_contra h
    have h' : i ≠ j := fun e => h (Set.mem_singleton_iff.2 e)
    exact hi (by simp [Pi.single_apply, h'])
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same]
      exact hF
    · simp only [Pi.single_eq_of_ne h]
      exact ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩

theorem divFunSuppSequence_shortExact (T : Finset I) (j : I) (hj : j ∉ T) :
    (divFunSuppSequence φ T j hj).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f hf
    have hj0 : ((f.1 : divFun φ QZ) : I → G → QZ) j = 0 := congrFun (congrArg Subtype.val hf) PUnit.unit
    refine ⟨⟨f.1, (mem_divFunSupp_iff φ T f.1).2 fun i hi => ?_⟩, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact hj0
    · exact (mem_divFunSupp_iff φ _ f.1).1 f.2 i (by simp [hij, hi])
  mono_f := (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (by
    have h' := congrArg Subtype.val h
    exact h')
  epi_g := (Rep.epi_iff_surjective _).2 fun e => by
    refine ⟨⟨⟨Pi.single j ((e.1 : PUnit → G → QZ) PUnit.unit),
      single_mem_divFun φ j _ (e.2.2 PUnit.unit)⟩, (mem_divFunSupp_iff φ _ _).2 fun i hi => ?_⟩, ?_⟩
    · have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self j T)
      change (Pi.single j ((e.1 : PUnit → G → QZ) PUnit.unit) : I → G → QZ) i = 0
      simp [Pi.single_apply, hij]
    · apply Subtype.ext
      funext u
      exact Pi.single_eq_same j _

theorem primaryVanishes_divFunSupp (hZ : ∀ i, IsClosed ((φ i).range : Set G)) {ℓ p : ℕ} (hℓ : ℓ.Prime)
    (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (T : Finset I) :
    PrimaryVanishes ℓ p ((divFunRep φ QZ).subrepresentation (divFunSupp φ T) (divFunSupp_stable φ T)) := by
  induction T using Finset.induction_on with
  | empty =>
    have : Subsingleton ((divFunRep φ QZ).subrepresentation (divFunSupp φ ∅) (divFunSupp_stable φ ∅)) :=
      ⟨fun a b => Subtype.ext (Subtype.ext (funext fun i =>
        ((mem_divFunSupp_iff φ ∅ a.1).1 a.2 i (by simp)).trans
          ((mem_divFunSupp_iff φ ∅ b.1).1 b.2 i (by simp)).symm))⟩
    intro x k hx
    have := subsingleton_cohomology_of_subsingleton
      ((divFunRep φ QZ).subrepresentation (divFunSupp φ ∅) (divFunSupp_stable φ ∅)) p
    exact Subsingleton.elim _ _
  | insert j T hj ih =>
    exact PrimaryVanishes.of_shortExact (divFunSuppSequence_shortExact φ T j hj) hℓ hp ih
      (primaryVanishes_divFunRepOne (φ j) (hZ j) hp (hloc j))

theorem eq_zero_of_pow_nsmul_cohomology_divFunRep' (hZ : ∀ i, IsClosed ((φ i).range : Set G)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) {p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (x : cohomology (divFunRep φ QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  refine PrimaryVanishes.of_union (divFunRep φ QZ) (divFunSupp φ) (divFunSupp_mono φ) (divFunSupp_stable φ)
    (fun a => ⟨a.2.1.toFinset, (mem_divFunSupp_iff φ _ a).2 fun i hi => ?_⟩)
    (fun T y k hy => ⟨T, le_rfl, ?_⟩) x k hx
  · by_contra h
    exact hi (a.2.1.mem_toFinset.2 h)
  · rw [primaryVanishes_divFunSupp φ hZ hℓ hp hloc T y k hy, map_zero]

theorem eq_zero_of_pow_nsmul_cohomology_divFunRep [T2Space G] [∀ i, TopologicalSpace (H i)]
    [∀ i, CompactSpace (H i)] (hφ : ∀ i, Continuous (φ i)) {ℓ : ℕ} (hℓ : ℓ.Prime) {p : ℕ} (hp : 1 ≤ p)
    (hloc : ∀ i (x : cohomology (Rep.res (φ i).range.subtype (trivRep G QZ)) p), (∃ k : ℕ, ℓ ^ k • x = 0) → x = 0)
    (x : cohomology (divFunRep φ QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_pow_nsmul_cohomology_divFunRep' φ (fun i => by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (hφ i)).isClosed) hℓ hp hloc x k hx

end Family

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

structure IsPrimePowGenerator {G : Type*} [Group G] [TopologicalSpace G] (ℓ : ℕ) (σ : G) : Prop where

  dense : IsTopologicalGenerator σ

  exists_hom : ∀ b : ℕ, ∃ φ : G →* Multiplicative (ZMod (ℓ ^ b)),
    IsOpen (φ.ker : Set G) ∧ φ σ = Multiplicative.ofAdd 1

section Quotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem IsTopologicalGenerator.exists_zpow_mk_eq {σ : G} (hσ : IsTopologicalGenerator σ) (U : Subgroup G)
    [U.Normal] (hU : IsOpen (U : Set G)) (y : G ⧸ U) : ∃ m : ℤ, (QuotientGroup.mk σ : G ⧸ U) ^ m = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have ho : IsOpen {x : G | g⁻¹ * x ∈ U} := hU.preimage (continuous_const.mul continuous_id)
  obtain ⟨x, hxσ, hx⟩ := hσ.exists_mem_open ho ⟨g, by simp [U.one_mem]⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxσ
  refine ⟨m, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  have hx' : g⁻¹ * σ ^ m ∈ U := hx
  simpa using inv_mem hx'

variable [CompactSpace G]

theorem IsTopologicalGenerator.exists_hom_zmod_orderOf {σ : G} (hσ : IsTopologicalGenerator σ) (U : Subgroup G)
    [U.Normal] (hU : IsOpen (U : Set G)) :
    ∃ φ : G →* Multiplicative (ZMod (orderOf (QuotientGroup.mk σ : G ⧸ U))),
      U ≤ φ.ker ∧ φ σ = Multiplicative.ofAdd 1 := by
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  set τ : G ⧸ U := QuotientGroup.mk σ with hτ
  set L := orderOf τ with hL
  let f : ℤ →+ Additive (G ⧸ U) := zmultiplesHom (Additive (G ⧸ U)) (Additive.ofMul τ)
  have hf : f (L : ℤ) = 0 := by
    change (L : ℤ) • Additive.ofMul τ = 0
    rw [natCast_zsmul, ← ofMul_pow, hL, pow_orderOf_eq_one, ofMul_one]
  let ψ : ZMod L →+ Additive (G ⧸ U) := ZMod.lift L ⟨f, hf⟩
  have hψ : ∀ m : ℤ, ψ (m : ZMod L) = Additive.ofMul (τ ^ m) := fun m => by
    change ZMod.lift L ⟨f, hf⟩ (m : ZMod L) = _
    rw [ZMod.lift_coe]
    change m • Additive.ofMul τ = _
    rw [← ofMul_zpow]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    rw [hψ, ← ofMul_one, Additive.ofMul.injective.eq_iff] at hk
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact orderOf_dvd_iff_zpow_eq_one.2 hk
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, hm⟩ := hσ.exists_zpow_mk_eq U hU (Additive.toMul y)
    exact ⟨m, by rw [hψ, hm]; rfl⟩
  let e : ZMod L ≃+ Additive (G ⧸ U) := AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  let φ : G →* Multiplicative (ZMod L) :=
    (AddMonoidHom.toMultiplicativeRight e.symm.toAddMonoidHom).comp (QuotientGroup.mk' U)
  refine ⟨φ, fun u hu => ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (e.symm (Additive.ofMul (QuotientGroup.mk u : G ⧸ U))) = 1
    rw [(QuotientGroup.eq_one_iff u).2 hu, ofMul_one, map_zero, ofAdd_zero]
  · change Multiplicative.ofAdd (e.symm (Additive.ofMul τ)) = _
    congr 1
    rw [AddEquiv.symm_apply_eq]
    change Additive.ofMul τ = ψ 1
    have h1 := hψ 1
    rw [Int.cast_one, zpow_one] at h1
    exact h1.symm

end Quotient

section Cocycle

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Rep.{u} k G} {σ : G} [IsDiscreteRep A]

theorem IsTopologicalGenerator.exists_cocycle_of_hom (hσ : IsTopologicalGenerator σ) (L : ℕ) [NeZero L]
    (φ : G →* Multiplicative (ZMod L)) (hφo : IsOpen (φ.ker : Set G)) (hφσ : φ σ = Multiplicative.ofAdd 1)
    (a : A) (hmem : σ ^ L ∈ stabilizer A.ρ a) (hsum : ∑ i ∈ Finset.range L, A.ρ (σ ^ i) a = 0) :
    ∃ f : (Fin 1 → G) → A, IsLocallyConstant f ∧ (inhomogeneousCochains.d A 1).hom f = 0 ∧
      f (fun _ => σ) = a := by
  have hρ : ∀ (x y : ℤ) (v : A), A.ρ (σ ^ x) (A.ρ (σ ^ y) v) = A.ρ (σ ^ (x + y)) v := by
    intro x y v
    rw [zpow_add, map_mul, Module.End.mul_apply]
  have hper : ∀ q : ℤ, A.ρ (σ ^ ((L : ℤ) * q)) a = a := by
    intro q
    have : σ ^ ((L : ℤ) * q) = (σ ^ L) ^ q := by
      rw [← zpow_natCast σ L, ← zpow_mul]
    rw [this]
    exact (mem_stabilizer _ _ _).1 (zpow_mem hmem _)
  obtain ⟨c, hc⟩ : ∃ c : ℤ → A, ∀ n, c n = ∑ i ∈ Finset.range ((n : ZMod L).val), A.ρ (σ ^ i) a :=
    ⟨_, fun _ => rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hrec : ∀ n : ℤ, c (n + 1) = c n + A.ρ (σ ^ n) a := by
    intro n
    obtain ⟨r, hr⟩ : ∃ r, r = (n : ZMod L).val := ⟨_, rfl⟩
    have hrL : r < L := hr ▸ ZMod.val_lt _
    have hrn : A.ρ (σ ^ n) a = A.ρ (σ ^ r) a := by
      have h1 : (r : ℤ) = n % L := by rw [hr, ZMod.val_intCast]
      have h2 : n = r + L * (n / L) := by rw [h1]; exact (Int.emod_add_mul_ediv n L).symm
      conv_lhs => rw [h2]
      rw [zpow_add, map_mul, Module.End.mul_apply, hper, zpow_natCast]
    have hval : ((n + 1 : ℤ) : ZMod L).val = (r + 1) % L := by
      rw [Int.cast_add, Int.cast_one, ZMod.val_add, ZMod.val_one_eq_one_mod, ← hr, Nat.add_mod_mod]
    rw [hc, hc, hval, hrn, ← hr]
    rcases Nat.lt_or_ge (r + 1) L with h | h
    · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ]
    · have h' : r + 1 = L := le_antisymm (by omega) h
      rw [h', Nat.mod_self, Finset.range_zero, Finset.sum_empty, ← Finset.sum_range_succ, h', hsum]
  have hcoc : ∀ x y : ℤ, c (x + y) = c x + A.ρ (σ ^ x) (c y) := by
    intro x y
    induction y using Int.induction_on with
    | zero => simp [hc0]
    | succ y ih =>
      rw [← add_assoc, hrec, ih, hrec, map_add, hρ, add_assoc]
    | pred y ih =>
      have e1 := hrec (x + (-(y : ℤ) - 1))
      have e2 := hrec (-(y : ℤ) - 1)
      rw [show x + (-(y : ℤ) - 1) + 1 = x + -(y : ℤ) by ring, ih] at e1
      rw [show -(y : ℤ) - 1 + 1 = -(y : ℤ) by ring] at e2
      rw [e2, map_add, hρ] at e1
      have e3 := e1.symm
      rw [← add_assoc] at e3
      exact add_right_cancel e3
  obtain ⟨F, hF⟩ : ∃ F : G → A, ∀ g, F g =
      ∑ i ∈ Finset.range (Multiplicative.toAdd (φ g)).val, A.ρ (σ ^ i) a := ⟨_, fun _ => rfl⟩
  have hFpow : ∀ n : ℤ, F (σ ^ n) = c n := by
    intro n
    rw [hF, hc, map_zpow, hφσ, toAdd_zpow, toAdd_ofAdd, zsmul_one]
  have hFlc : IsLocallyConstant F := by
    have h1 : IsLocallyConstant φ := φ.isLocallyConstant_of_isOpen_ker hφo
    have : F = (fun z : Multiplicative (ZMod L) =>
        ∑ i ∈ Finset.range (Multiplicative.toAdd z).val, A.ρ (σ ^ i) a) ∘ φ := funext hF
    rw [this]
    exact h1.comp _
  have hflc : IsLocallyConstant fun x : Fin 1 → G => F (x 0) :=
    hFlc.comp_continuous (continuous_apply 0)
  refine ⟨fun x => F (x 0), hflc, ?_, ?_⟩
  · refine hσ.eq_of_forall_zpow_pi (isLocallyConstant_d A hflc)
      (IsLocallyConstant.const 0) fun n => ?_
    show (inhomogeneousCochains.d A 1).hom (fun x => F (x 0)) (fun i => σ ^ n i) = 0
    rw [inhomogeneousD_one_apply]
    dsimp only
    rw [← zpow_add, hFpow, hFpow, hFpow, hcoc]
    abel
  · show F σ = a
    have h1 := hFpow 1
    rw [zpow_one] at h1
    rw [h1, ← zero_add (1 : ℤ), hrec, hc0, zpow_zero, map_one, Module.End.one_apply, zero_add]

end Cocycle

section Primary

theorem mul_pow_dvd_of_dvd_of_pow_add_dvd {ℓ N L e : ℕ} (hℓ : ℓ.Prime) (hN : 0 < N) (h1 : N ∣ L)
    (h2 : ℓ ^ (e + N) ∣ L) : N * ℓ ^ e ∣ L := by
  obtain ⟨v, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.ne_one
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hN
  have hcop : Nat.Coprime (ℓ ^ (e + v)) r :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hr)
  have hv : v ≤ ℓ ^ v * r := by
    have h3 : v < ℓ ^ v := v.lt_pow_self hℓ.one_lt
    have h4 : ℓ ^ v ≤ ℓ ^ v * r := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hr0)
    omega
  have h3 : ℓ ^ (e + v) ∣ L := (Nat.pow_dvd_pow ℓ (by omega)).trans h2
  have h4 : r ∣ L := (Dvd.intro_left _ rfl).trans h1
  have := hcop.mul_dvd_of_dvd_of_dvd h3 h4
  calc ℓ ^ v * r * ℓ ^ e = ℓ ^ (e + v) * r := by ring
    _ ∣ L := this

end Primary

section CocyclePrimary

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {ℓ : ℕ} {σ : G}

theorem IsPrimePowGenerator.exists_cocycle (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    {A : Rep.{u} k G} [IsDiscreteRep A] (a : A) {e : ℕ} (ha : ℓ ^ e • a = 0) :
    ∃ f : (Fin 1 → G) → A, IsLocallyConstant f ∧ (inhomogeneousCochains.d A 1).hom f = 0 ∧
      f (fun _ => σ) = a := by
  obtain ⟨U₀, hU₀⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_stabilizer A a) (stabilizer A.ρ a).one_mem
  have : Finite (G ⧸ (U₀ : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U₀.isOpen'
  set N := orderOf (QuotientGroup.mk σ : G ⧸ (U₀ : Subgroup G)) with hNdef
  have hN : 0 < N := orderOf_pos _
  have hσN : σ ^ N ∈ stabilizer A.ρ a := hU₀ ((QuotientGroup.eq_one_iff _).1 (by
    rw [QuotientGroup.mk_pow, hNdef, pow_orderOf_eq_one]))
  obtain ⟨χ, hχo, hχσ⟩ := hσ.exists_hom (e + N)
  let U : Subgroup G := (U₀ : Subgroup G) ⊓ χ.ker
  have hUo : IsOpen (U : Set G) := U₀.isOpen'.inter hχo
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  set L := orderOf (QuotientGroup.mk σ : G ⧸ U) with hLdef
  obtain ⟨φ, hφU, hφσ⟩ := hσ.dense.exists_hom_zmod_orderOf U hUo
  have hLU : σ ^ L ∈ U := (QuotientGroup.eq_one_iff _).1 (by
    rw [QuotientGroup.mk_pow, hLdef, pow_orderOf_eq_one])
  have hL : 0 < L := orderOf_pos _
  have h1 : N ∣ L := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hLU.1)
  have h2 : ℓ ^ (e + N) ∣ L := by
    have hk : χ (σ ^ L) = 1 := hLU.2
    rw [map_pow, hχσ, ← ofAdd_nsmul, nsmul_one, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hk
    exact (ZMod.natCast_eq_zero_iff _ _).1 hk
  obtain ⟨c, hc⟩ := mul_pow_dvd_of_dvd_of_pow_add_dvd hℓ hN h1 h2
  have hsum : ∑ i ∈ Finset.range L, A.ρ (σ ^ i) a = 0 := by
    rw [hc, mul_assoc]
    exact sum_range_mul_eq_zero ((mem_stabilizer _ _ _).1 hσN) (by rw [mul_comm, mul_smul, ha, smul_zero])
  have : NeZero L := ⟨hL.ne'⟩
  exact hσ.dense.exists_cocycle_of_hom L φ (Subgroup.isOpen_mono hφU hUo) hφσ a (hU₀ hLU.1) hsum

theorem IsPrimePowGenerator.H1Eval_surjective (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) :
    Function.Surjective (H1Eval A σ).hom := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨e, he⟩ := hA a
  obtain ⟨f, hlc, hd, hfσ⟩ := hσ.exists_cocycle hℓ a he
  let x : locallyConstantCochains A 1 := ⟨f, hlc⟩
  have hx : ((cochainsComplex A).d 1 2).hom x = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, cochainsComplex_d]
    exact Subtype.ext hd
  refine ⟨(cohomologyπ A 1).hom ((cochainsComplex A).cyclesMk x 2 (by simp) hx), ?_⟩
  rw [H1Eval_cohomology_class_apply]
  have h : cocycleFun A ((cochainsComplex A).cyclesMk x 2 (by simp) hx) = f :=
    congrArg Subtype.val ((cochainsComplex A).i_cyclesMk x 2 (by simp) hx)
  rw [h, hfσ]

omit [TotallyDisconnectedSpace G] in

theorem primary_discreteCoind_of_primary (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (f : discreteCoind k G A) : ∃ e : ℕ, ℓ ^ e • f = 0 := by
  let f' : LocallyConstant G A := f
  have : Finite (Set.range f') := f'.range_finite.to_subtype
  choose kk hkk using fun v : Set.range f' => hA v
  obtain ⟨K, hK⟩ := (Set.finite_range kk).bddAbove
  refine ⟨K, LocallyConstant.ext fun x => ?_⟩
  show ℓ ^ K • f' x = 0
  exact pow_nsmul_eq_zero_of_le (hK ⟨⟨f' x, x, rfl⟩, rfl⟩) (hkk ⟨f' x, x, rfl⟩)

omit [TotallyDisconnectedSpace G] in

theorem primary_coindCokernel_of_primary (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (x : coindCokernel A) : ∃ e : ℕ, ℓ ^ e • x = 0 := by
  have hepi : Epi (coindCokernelπ A) := (coindShortComplex_shortExact A).epi_g
  obtain ⟨f, rfl⟩ := (Rep.epi_iff_surjective (coindCokernelπ A)).1 hepi x
  obtain ⟨e, he⟩ := primary_discreteCoind_of_primary A hA f
  exact ⟨e, by rw [← map_nsmul, he, map_zero]⟩

theorem IsPrimePowGenerator.mem_range_sub_one_discreteCoind (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (c : LocallyConstant G A) :
    c ∈ LinearMap.range ((discreteCoind k G A).ρ σ - 1) := by
  have hz := isZero_cohomology_discreteCoind k G A 0
  have hs : Subsingleton (cohomology (discreteCoind k G A) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  obtain ⟨x, hx⟩ := hσ.H1Eval_surjective hℓ (discreteCoind k G A)
    (primary_discreteCoind_of_primary A hA) (Submodule.Quotient.mk c)
  rw [Subsingleton.elim x 0, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at hx
  exact hx

theorem IsPrimePowGenerator.isZero_cohomology_two (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) :
    IsZero (cohomology A 2) := by
  refine IsZero.of_iso ?_ (cohomologyCoindCokernelIso A 0).symm
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  apply H1Eval_injective (coindCokernel A) hσ.dense
  refine Subsingleton.elim (h := ⟨fun q q' => ?_⟩) _ _
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨q', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (q - q')
  rw [← hc]
  obtain ⟨d, hd⟩ := hσ.mem_range_sub_one_discreteCoind hℓ A hA c
  refine ⟨(coindCokernelπ A).hom d, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, ← Rep.hom_comm_apply, ← map_sub]
  rw [← hd]
  rfl

theorem IsPrimePowGenerator.isZero_cohomology_of_primary (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (cohomology A n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m generalizing A with
  | zero => exact hσ.isZero_cohomology_two hℓ A hA
  | succ m ih =>
    exact (ih (coindCokernel A) (primary_coindCokernel_of_primary A hA)).of_iso
      (cohomologyCoindCokernelIso A (m + 1)).symm

theorem IsPrimePowGenerator.eq_zero_of_pow_nsmul (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : IsAddTorsion A) {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology A p) {n : ℕ} (hx : ℓ ^ n • x = 0) : x = 0 := by
  set W := primarySubmodule A ℓ
  have hW := primarySubmodule_le_comap A ℓ
  have hS := subQuotShortComplex_shortExact A W hW

  have hbij : Function.Bijective (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom := by
    have : ⇑(ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom =
        fun y : A ⧸ W => ℓ • y := funext fun y => nsmul_id_hom_apply _ ℓ y
    rw [this]
    exact bijective_nsmul_quotient_primarySubmodule A hA hℓ
  have hiso : IsIso (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) := by
    have he : (Rep.mkIso ((ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom.ofBijective hbij)).hom =
        ℓ • 𝟙 (subQuotShortComplex A W hW).X₃ := Rep.hom_ext rfl
    rw [← he]
    infer_instance
  have hinj : Function.Injective (cohomologyMap (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) p).hom := by
    have hH : IsIso (cohomologyMap (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) p) :=
      ⟨cohomologyMap (inv (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃)) p, by
        rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id], by
        rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]⟩
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  let x' : cohomology (subQuotShortComplex A W hW).X₂ p := x
  have hx' : ℓ ^ n • x' = 0 := hx
  have hg : (cohomologyMap (subQuotShortComplex A W hW).g p).hom x' = 0 := by
    have hpow : ∀ j : ℕ, ∀ y : cohomology (subQuotShortComplex A W hW).X₃ p, ℓ ^ j • y = 0 → y = 0 := by
      intro j
      induction j with
      | zero => intro y hy; simpa using hy
      | succ j ih =>
        intro y hy
        apply ih
        apply hinj
        rw [map_zero, cohomologyMap_nsmul_id_apply, ← mul_smul, ← pow_succ']
        exact hy
    exact hpow n _ (by rw [← map_nsmul, hx', map_zero])
  obtain ⟨y, hy'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS p) x' hg
  have hy : IsZero (cohomology (subQuotShortComplex A W hW).X₁ p) :=
    hσ.isZero_cohomology_of_primary hℓ _ (fun (b : (subQuotShortComplex A W hW).X₁) => by
      obtain ⟨j, hj⟩ := b.2
      exact ⟨j, Subtype.ext hj⟩) hp
  have h0 : x' = 0 := by
    rw [← hy', (ModuleCat.subsingleton_of_isZero hy).elim y 0, map_zero]
  exact h0

end CocyclePrimary

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.LocalField
  GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)
  (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})

section Hom

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ w : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ w.asIdeal → w ∈ S)

theorem val_intCast_nsmul_eq_zsmul {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n] {c : A} (hc : n • c = 0)
    (k : ℤ) : ((k : ZMod n).val) • c = k • c := by
  have h1 : (((k : ZMod n).val : ℕ) : ℤ) = k % n := ZMod.val_intCast k
  rw [← natCast_zsmul, h1]
  conv_rhs => rw [← Int.emod_add_mul_ediv k n]
  rw [add_smul, mul_comm, mul_smul, natCast_zsmul, hc, smul_zero, add_zero]

theorem dvd_of_nsmul_mk_one_div_eq_zero {N m : ℕ} (hN : N ≠ 0) (h : m • QZ.mk (1 / (N : ℚ)) = 0) : N ∣ m := by
  have h2 : QZ.mk ((m : ℚ) * (1 / (N : ℚ))) = 0 := by
    have e := map_nsmul QZ.mkHom m (1 / (N : ℚ))
    rw [nsmul_eq_mul] at e
    exact e.trans h
  obtain ⟨n, hn⟩ := (QZ.mk_eq_zero_iff _).1 h2
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have e1 : (n : ℚ) * (N : ℚ) = m := by rw [hn]; field_simp
  have e2 : n * (N : ℤ) = m := by exact_mod_cast e1
  exact Int.natCast_dvd_natCast.1 ⟨n, by rw [← e2, mul_comm]⟩

theorem exists_localGaloisCohomology_order {ℓ : ℕ} (hℓ : ℓ.Prime) (w : HeightOneSpectrum (𝓞 K.1)) (b : ℕ) :
    ∃ t : localGaloisCohomology K 2 (.inr w), ℓ ^ b • t = 0 ∧ ∀ m : ℕ, m • t = 0 → ℓ ^ b ∣ m := by
  have hN : ℓ ^ b ≠ 0 := pow_ne_zero b hℓ.ne_zero
  obtain ⟨t, ht⟩ := (placeInv_bijective_inr (K := K) w).2 (QZ.mk (1 / ((ℓ ^ b : ℕ) : ℚ)))
  refine ⟨t, ?_, fun m hm => ?_⟩
  · apply (placeInv_bijective_inr (K := K) w).1
    rw [AddMonoidHom.map_nsmul, ht, AddMonoidHom.map_zero]
    exact QZ.nsmul_mk_one_div (ℓ ^ b)
  · refine dvd_of_nsmul_mk_one_div_eq_zero hN ?_
    rw [← ht, ← AddMonoidHom.map_nsmul, hm, AddMonoidHom.map_zero]

set_option maxHeartbeats 8000000 in
include hℓ hS in

theorem exists_char_order_gsDecomp (b : ℕ) :
    ∃ χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ,
      ℓ ^ b • χ = 0 ∧ (∀ m : ℕ, m • χ = 0 → ℓ ^ b ∣ m) ∧
        ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0 := by
  obtain ⟨t, htk, htm⟩ := exists_localGaloisCohomology_order K hℓ v.1 b
  obtain ⟨x, hxk, hxt, -⟩ := exists_gsLocalRes_eq_single K S ℓ hℓ hS ιs v.1 v.2 t b htk
  obtain ⟨x', hx'⟩ : ∃ x', cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 x' = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  have hloc : gsLoc K S ιs v.1 x' = t := by
    change (gsLocalRes S (ιs.fin v.1) 2).hom
      ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) x') = t
    rw [hx']
    exact hxt
  refine ⟨gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) (gsVal K S ιs v.1 v.2 x'), ?_, fun m hm => ?_, fun h hh =>
    gvChar_decompHomS_eq_zero S (ιs.fin v.1) x' (ordEmbMor S (ιs.fin v.1) v.2) h hh⟩
  · have hx'k : ℓ ^ b • x' = 0 := by
      refine (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).injective ?_
      refine ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).toAddMonoidHom.map_nsmul
        _ _).trans ?_
      refine (congrArg (ℓ ^ b • ·) hx').trans ?_
      exact hxk.trans (AddEquiv.map_zero _).symm
    refine ((gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).toAddMonoidHom.map_nsmul _ _).symm.trans ?_
    refine (congrArg (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) ((AddMonoidHom.map_nsmul _ _ _).symm.trans
      ((congrArg (gsVal K S ιs v.1 v.2) hx'k).trans (AddMonoidHom.map_zero _)))).trans ?_
    exact AddEquiv.map_zero _
  · apply htm m
    have h1 : gsVal K S ιs v.1 v.2 (m • x') = 0 := by
      refine (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).injective ?_
      refine (congrArg (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) (AddMonoidHom.map_nsmul _ _ _)).trans ?_
      refine ((gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).toAddMonoidHom.map_nsmul _ _).trans ?_
      exact hm.trans (AddEquiv.map_zero _).symm
    have h2 := (gsLoc_eq_zero_iff K S ιs v.1 v.2 (m • x')).2 h1
    exact ((congrArg (m • ·) hloc).symm.trans (AddMonoidHom.map_nsmul (gsLoc K S ιs v.1) m x').symm).trans h2

set_option maxHeartbeats 4000000 in

theorem char_eq_proj_nsmul_of_gsDecomp {ℓ : ℕ} (hℓ : ℓ.Prime) (b : ℕ)
    (χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ)
    (hχk : ℓ ^ b • χ = 0) (hB : ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0)
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) :
    χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val •
          χ (Additive.ofMul σ) := by
  have hN : ℓ ^ b ≠ 0 := pow_ne_zero b hℓ.ne_zero
  have : NeZero (ℓ ^ b) := ⟨hN⟩
  obtain ⟨c, hcdef⟩ : ∃ c, χ (Additive.ofMul σ) = c := ⟨_, rfl⟩
  have hc : ℓ ^ b • c = 0 := by
    rw [← hcdef, ← ContinuousAddMonoidHom.nsmul_apply, hχk]
    rfl
  rw [hcdef]
  have hE := eq_univ_of_unramifiedDegree v.1 σ hσ
    {g | χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val • c}
    (isClosed_eq (χ.continuous.comp continuous_ofMul)
      ((continuous_of_discreteTopology (f := fun z : ZMod (ℓ ^ b) => z.val • c)).comp
        ((ProfiniteInteger.continuous_proj _).comp (continuous_toAdd.comp continuous_unramifiedDegree))))
    (fun k => by
      show χ (Additive.ofMul (σ ^ k)) = _
      rw [ofMul_zpow, map_zsmul, hcdef, map_zpow, hσ, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_one, map_intCast]
      exact (val_intCast_nsmul_eq_zsmul (n := ℓ ^ b) hc k).symm)
    (fun g hg h hh => by
      show χ (Additive.ofMul (g * h)) = _
      rw [ofMul_mul, map_add, hB h (gsDecomp_eq_one_of_unramifiedDegree_eq_one K S ιs v h hh), add_zero,
        map_mul, hh, mul_one]
      exact hg)
  have hg : g ∈ {g | χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val • c} := by
    rw [hE]
    exact Set.mem_univ _
  exact hg

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one (b : ℕ)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hg : gsDecomp K S ιs v g = 1) :
    ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (unramifiedDegree
      (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_unramifiedDegree_eq_one (K := K) (v := v.1)
  obtain ⟨χ, hχk, hA, hB⟩ := exists_char_order_gsDecomp K S ιs v hℓ hS b
  have hC := char_eq_proj_nsmul_of_gsDecomp K S ιs v hℓ b χ hχk hB σ hσ
  obtain ⟨z, hz⟩ : ∃ z : ZMod (ℓ ^ b), ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) = z := ⟨_, rfl⟩
  have hzc : z.val • χ (Additive.ofMul σ) = 0 := by
    have e := hC g
    rw [hz] at e
    exact e.symm.trans (hB g hg)
  have hzχ : z.val • χ = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [ContinuousAddMonoidHom.nsmul_apply, ← ofMul_toMul y, hC, smul_comm, hzc, smul_zero]
    rfl
  have hdvd := hA z.val hzχ
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero b hℓ.ne_zero⟩
  have hlt : z.val < ℓ ^ b := ZMod.val_lt z
  have h0 : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  rw [hz]
  exact (ZMod.val_eq_zero z).1 h0

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem exists_hom_zmod_pow_rangeRestrict_gsDecomp
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1) (b : ℕ) :
    ∃ φ : (gsDecomp K S ιs v).range →* Multiplicative (ZMod (ℓ ^ b)),
      IsOpen (φ.ker : Set (gsDecomp K S ιs v).range) ∧
        φ ((gsDecomp K S ιs v).rangeRestrict σ) = Multiplicative.ofAdd 1 := by
  set deg := unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1))
  let ψ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →* Multiplicative (ZMod (ℓ ^ b)) :=
    (AddMonoidHom.toMultiplicative (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩).toAddMonoidHom).comp deg
  have hψ : ∀ g, ψ g = Multiplicative.ofAdd
      (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (deg g)) : ZMod (ℓ ^ b)) :=
    fun _ => rfl
  have hker : (gsDecomp K S ιs v).ker ≤ ψ.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [hψ, proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one K S ιs v hℓ hS b g hg, ofAdd_zero]
    rfl
  let φ : (gsDecomp K S ιs v).range →* Multiplicative (ZMod (ℓ ^ b)) :=
    (QuotientGroup.lift _ ψ hker).comp
      (QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm.toMonoidHom
  have hφ : ∀ g, φ ((gsDecomp K S ιs v).rangeRestrict g) = ψ g := fun g => by
    have e : (QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm
        ((gsDecomp K S ιs v).rangeRestrict g) = (g : _ ⧸ (gsDecomp K S ιs v).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift _ ψ hker ((QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm
      ((gsDecomp K S ιs v).rangeRestrict g)) = ψ g
    rw [e, QuotientGroup.lift_mk]
  refine ⟨φ, ?_, ?_⟩
  · rw [← (isQuotientMap_rangeRestrict_gsDecomp K S ιs v).isOpen_preimage]
    have e : (gsDecomp K S ιs v).rangeRestrict ⁻¹' (φ.ker : Set (gsDecomp K S ιs v).range) =
        (fun g => (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (deg g)) : ZMod (ℓ ^ b))) ⁻¹' {0} := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hφ, hψ, Set.mem_singleton_iff]
      exact Iff.rfl
    rw [e]
    exact (isOpen_discrete _).preimage
      ((ProfiniteInteger.continuous_proj _).comp (continuous_toAdd.comp continuous_unramifiedDegree))
  · rw [hφ, hψ, hσ, toAdd_ofAdd, map_one]
    rfl

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem exists_isPrimePowGenerator_gsDecomp :
    ∃ σ : (gsDecomp K S ιs v).range, IsPrimePowGenerator ℓ σ := by
  obtain ⟨σ, hσ⟩ := exists_unramifiedDegree_eq_one (K := K) (v := v.1)
  exact ⟨(gsDecomp K S ιs v).rangeRestrict σ,
    ⟨isTopologicalGenerator_rangeRestrict_gsDecomp K S ιs v σ hσ,
      fun b => exists_hom_zmod_pow_rangeRestrict_gsDecomp K S ιs v hℓ hS σ hσ b⟩⟩

instance isDiscreteRep_res_range_gsDecomp :
    IsDiscreteRep (Rep.res (gsDecomp K S ιs v).range.subtype (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) :=
  isDiscreteRep_res_subtype _ _

instance totallyDisconnectedSpace_range_gsDecomp : TotallyDisconnectedSpace (gsDecomp K S ιs v).range :=
  have := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  inferInstance

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem eq_zero_of_pow_nsmul_cohomology_range_gsDecomp {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (Rep.res (gsDecomp K S ιs v).range.subtype
      (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  obtain ⟨σ, hσ⟩ := exists_isPrimePowGenerator_gsDecomp K S ιs v hℓ hS
  exact hσ.eq_zero_of_pow_nsmul hℓ _ isAddTorsion_QZ hp x hx

end Hom

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section TwoTorsion

variable {K : FiniteSubfield}

theorem two_nsmul_cohomology_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    2 • y = 0 := by
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  apply (bijective_realLocalization ι hr).1
  rw [map_nsmul, map_zero]
  funext v
  rw [Pi.smul_apply]
  rcases Nat.even_or_odd r with he | ho
  · have hc := natCard_localGaloisCohomology_of_isReal_of_even v.1 v.2 (by omega) he
    rw [← hc]
    exact card_nsmul_eq_zero'
  · have := subsingleton_localGaloisCohomology_of_isReal_of_odd v.1 v.2 ho
    exact Subsingleton.elim _ _

theorem eq_zero_of_pow_nsmul_cohomology_unitsLimitRep_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) {r : ℕ}
    (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) {k : ℕ} (hk : ℓ ^ k • y = 0) : y = 0 :=
  eq_zero_of_coprime_nsmul_eq_zero ((Nat.coprime_primes Nat.prime_two hℓ).2 h2.symm)
    (two_nsmul_cohomology_unitsLimitRep hr y) hk

end TwoTorsion

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ (ιs : LocalEmbeddings K) {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (gsDiv K S ιs QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_pow_nsmul_cohomology_divFunRep (gsDecomp K S ιs) (continuous_gsDecomp K S ιs) hℓ (by omega)
    (fun v y hy => hy.elim fun j hj => eq_zero_of_pow_nsmul_cohomology_range_gsDecomp K S ιs v hℓ hS hp y j hj)
    x k hx

include hℓ hS in

theorem isIsoModCoprime_sUnitsToUnits_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom :=
  isIsoModCoprime_sUnitsToUnits K S (nonempty_localEmbeddings K).some hℓ hS
    (fun _ hp x k hx => eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ K S hℓ hS _ hp x k hx) hr

include hℓ hS in

theorem isIsoModCoprime_sUnitsInfl {r : ℕ} (hr : 4 ≤ r) : IsIsoModCoprime ℓ (sUnitsInfl K S r) :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS (by omega)).comp (isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr)

noncomputable def sUnitsToUnitsPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr).bijective_primaryComponentMap hℓ
      (isTorsion_cohomology _ (by omega)))


noncomputable def sUnitsInflPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsInfl K S hℓ hS hr).bijective_primaryComponentMap hℓ (isTorsion_cohomology _ (by omega)))


section Odd

include hℓ hS in

theorem eq_zero_of_pow_nsmul_cohomology_gsUnits_of_odd (h2 : ℓ ≠ 2) {r : ℕ} (hr : 4 ≤ r)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) {k : ℕ} (hk : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_gsUnitsInfl_eq_zero K S hℓ hS (by omega) x
    (eq_zero_of_pow_nsmul_cohomology_unitsLimitRep_of_odd hℓ h2 hr _ (k := k)
      ((map_nsmul _ _ _).symm.trans ((congrArg _ hk).trans (map_zero _)))) hk

include hℓ hS in

theorem eq_zero_of_pow_nsmul_cohomology_sUnits_of_odd (h2 : ℓ ≠ 2) {r : ℕ} (hr : 4 ≤ r)
    (x : cohomology (galSUnitsMax K.1 ℚ̄ S) r) {k : ℕ} (hk : ℓ ^ k • x = 0) : x = 0 :=
  (isIsoModCoprime_sUnitsInfl K S hℓ hS hr).eq_zero_of_pow_nsmul
    (eq_zero_of_pow_nsmul_cohomology_unitsLimitRep_of_odd hℓ h2 hr _ (k := k)
      ((map_nsmul _ _ _).symm.trans ((congrArg _ hk).trans (map_zero _)))) hk

end Odd

section Real

variable (ι : LocalEmbeddings K)

theorem mem_primaryComponent_two_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    y ∈ AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) 2 :=
  ⟨1, by rw [pow_one]; exact two_nsmul_cohomology_unitsLimitRep hr y⟩

theorem bijective_realLocalization_comp_primaryComponent {X : Type*} [AddCommGroup X] {r : ℕ} (hr : 4 ≤ r)
    (f : X →+ cohomology (unitsLimitRep K) r) (hf : IsIsoModCoprime 2 f) (hX : IsAddTorsion X) :
    Function.Bijective ((realLocalization ι (r := r) (by omega)).comp
      (f.comp (AddCommGroup.primaryComponent X 2).subtype)) := by
  have hb := hf.bijective_primaryComponentMap Nat.prime_two hX
  have hR := bijective_realLocalization ι hr
  refine ⟨fun a b hab => hb.1 (Subtype.ext (hR.1 hab)), fun t => ?_⟩
  obtain ⟨y, rfl⟩ := hR.2 t
  obtain ⟨a, ha⟩ := hb.2 ⟨y, mem_primaryComponent_two_unitsLimitRep (K := K) hr y⟩
  exact ⟨a, congrArg (realLocalization ι (r := r) (by omega)) (congrArg Subtype.val ha)⟩

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

noncomputable def gsUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (gsUnitsInfl K S r)
    (isIsoModCoprime_gsUnitsInfl K S Nat.prime_two h2S (by omega)) (isTorsion_cohomology _ (by omega)))


noncomputable def sUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (sUnitsInfl K S r)
    (isIsoModCoprime_sUnitsInfl K S Nat.prime_two h2S hr) (isTorsion_cohomology _ (by omega)))

theorem sUnitsRealPrimaryEquiv_apply {r : ℕ} (hr : 4 ≤ r)
    (x : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2) :
    sUnitsRealPrimaryEquiv K S ι h2S hr x = realLocalization ι (r := r) (by omega) (sUnitsInfl K S r x) :=
  rfl

end Real

end

end GroundTheory.ProfCoh
end
