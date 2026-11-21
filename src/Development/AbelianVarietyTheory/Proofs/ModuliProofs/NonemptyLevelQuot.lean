import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.GaloisQuotient

open TopologicalSpace

private theorem exists_homogeneous_mem_not_mem_finset_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : Ideal A) (P : Finset (Ideal A))
    (hP : ∀ p ∈ P, p.IsPrime ∧ p.IsHomogeneous 𝒜 ∧ ∃ d, 0 < d ∧ ∃ g ∈ 𝒜 d, g ∈ J ∧ g ∉ p) :
    ∃ d, 0 < d ∧ ∃ f ∈ 𝒜 d, f ∈ J ∧ ∀ p ∈ P, f ∉ p := by
  classical
  induction P using Finset.strongInduction with
  | H P ih =>
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, 0, zero_mem _, zero_mem _, by simp⟩
  obtain ⟨q, hqP, hqmin⟩ := P.exists_minimal hne
  obtain ⟨d, hd, f, hf, hfJ, hfP⟩ := ih (P.erase q) (Finset.erase_ssubset hqP)
    (fun p hp => hP p (Finset.mem_of_mem_erase hp))
  by_cases hfq : f ∉ q
  · refine ⟨d, hd, f, hf, hfJ, fun p hp => ?_⟩
    by_cases hpq : p = q
    · rw [hpq]; exact hfq
    · exact hfP p (Finset.mem_erase.2 ⟨hpq, hp⟩)
  push Not at hfq
  obtain ⟨hqprime, -, e, he, g, hg, hgJ, hgq⟩ := hP q hqP
  have hx : ∀ p ∈ P.erase q, ∃ c, ∃ x ∈ 𝒜 c, x ∈ p ∧ x ∉ q := by
    intro p hp
    obtain ⟨hpne, hpP⟩ := Finset.mem_erase.1 hp
    obtain ⟨-, hphom, -⟩ := hP p hpP
    have hnle : ¬ p ≤ q := fun hle => hpne (le_antisymm hle (hqmin hpP hle))
    obtain ⟨y, hyp, hyq⟩ := Set.not_subset.1 hnle
    by_contra hcon
    push Not at hcon
    apply hyq
    rw [← DirectSum.sum_support_decompose 𝒜 y]
    exact Ideal.sum_mem _ fun c _ => hcon c _ (SetLike.coe_mem _) (hphom c hyp)
  choose! c x hx𝒜 hxp hxq using hx
  set C := ∑ p ∈ P.erase q, c p
  set h := ∏ p ∈ P.erase q, x p
  have hh : h ∈ 𝒜 C := SetLike.prod_mem_graded 𝒜 c x hx𝒜
  have hhq : h ∉ q := by
    intro hm
    obtain ⟨p, hp, hpq⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hqprime)).1 hm
    exact hxq p hp hpq
  have hhp : ∀ p ∈ P.erase q, h ∈ p := fun p hp => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem x hp
    have hk' : h = x p * k := hk
    rw [hk']
    exact p.mul_mem_right _ (hxp p hp)
  have hpos : 0 < e + C := Nat.add_pos_left he _
  refine ⟨d * (e + C), Nat.mul_pos hd hpos, f ^ (e + C) + (g * h) ^ d, ?_, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · have h1 := SetLike.pow_mem_graded (e + C) hf
      rwa [smul_eq_mul, mul_comm] at h1
    · have h1 := SetLike.pow_mem_graded d (SetLike.mul_mem_graded hg hh)
      rwa [smul_eq_mul] at h1
  · exact J.add_mem (J.pow_mem_of_mem hfJ _ hpos) (J.pow_mem_of_mem (J.mul_mem_right _ hgJ) _ hd)
  · intro p hp hF
    by_cases hpq : p = q
    · rw [hpq] at hF
      have h1 : f ^ (e + C) ∈ q := q.pow_mem_of_mem hfq _ hpos
      have h2 : (g * h) ^ d ∈ q := (q.add_mem_iff_right h1).1 hF
      rcases hqprime.mem_or_mem (hqprime.mem_of_pow_mem _ h2) with h3 | h3
      · exact hgq h3
      · exact hhq h3
    · have hp' : p ∈ P.erase q := Finset.mem_erase.2 ⟨hpq, hp⟩
      have hpprime := (hP p hp).1
      have h2 : (g * h) ^ d ∈ p := p.pow_mem_of_mem (p.mul_mem_left _ (hhp p hp')) _ hd
      have h1 : f ^ (e + C) ∈ p := (p.add_mem_iff_left h2).1 hF
      exact hfP p hp' (hpprime.mem_of_pow_mem _ h1)

theorem exists_sec_nonzeroLocus_le {R : Type} [CommRing R] {N : ℕ} {s : Set (PSpace R N)} (hs : s.Finite)
    (U : (PSpace R N).Opens) (hU : s ⊆ U) :
    ∃ n, 1 ≤ n ∧ ∃ t : (lbPow (ProjSpace.O1 R N) n).Sec,
      s ⊆ Out.nonzeroLocus t ∧ Out.nonzeroLocus t ≤ U ∧ IsAffineOpen (Out.nonzeroLocus t) := by
  classical
  let J : Ideal (MvPolynomial (Fin (N + 1)) R) :=
    (ProjectiveSpectrum.vanishingIdeal (𝒜 := ProjSpace.grading R N)
      {x | ¬ (x : PSpace R N) ∈ U}).toIdeal
  have hJ1 : ∀ f ∈ J, Proj.basicOpen (ProjSpace.grading R N) f ≤ U := fun f hf x hx => by
    by_contra hxU
    exact hx ((ProjectiveSpectrum.mem_vanishingIdeal _ f).1 hf x hxU)
  have hJ2 : ∀ g, Proj.basicOpen (ProjSpace.grading R N) g ≤ U → g ∈ J := fun g hg =>
    (ProjectiveSpectrum.mem_vanishingIdeal _ g).2 fun x hxU => by
      by_contra hgx
      exact hxU (hg hgx)
  have hgen : ∀ x : PSpace R N, x ∈ U → ∃ d, 0 < d ∧ ∃ g ∈ ProjSpace.grading R N d, g ∈ J ∧
      g ∉ (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := ProjSpace.grading R N) x).toIdeal := by
    intro x hxU
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (ProjSpace.grading R N)) hxU
    rw [Proj.basicOpen_eq_iSup_proj] at hxr
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxr
    have hkU : Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r) ≤ U := by
      refine le_trans ?_ hrU
      rw [Proj.basicOpen_eq_iSup_proj (ProjSpace.grading R N) r]
      exact le_iSup (fun k => Proj.basicOpen (ProjSpace.grading R N) (GradedRing.proj (ProjSpace.grading R N) k r)) k
    obtain ⟨j, hj⟩ := ProjSpace.exists_mem_chart R N x
    refine ⟨k + 1, Nat.succ_pos k, GradedRing.proj (ProjSpace.grading R N) k r * MvPolynomial.X j, ?_, ?_, ?_⟩
    · refine SetLike.mul_mem_graded ?_ (ProjSpace.X_mem R N j)
      rw [GradedRing.proj_apply]
      exact SetLike.coe_mem _
    · apply hJ2
      rw [Proj.basicOpen_mul]
      exact inf_le_left.trans hkU
    · show x ∈ Proj.basicOpen (ProjSpace.grading R N) _
      rw [Proj.basicOpen_mul]
      exact ⟨hk, hj⟩
  obtain ⟨d, hd, f, hf, hfJ, hfP⟩ := exists_homogeneous_mem_not_mem_finset_primes (ProjSpace.grading R N) J
    (hs.toFinset.image fun x : PSpace R N =>
      (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := ProjSpace.grading R N) x).toIdeal)
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨ProjectiveSpectrum.isPrime _, HomogeneousIdeal.isHomogeneous _,
        hgen x (hU (hs.mem_toFinset.1 hx))⟩)
  have hfh : f.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d f).1 hf
  refine ⟨d, hd, ProjSpace.formSec d f hfh, ?_, ?_, ?_⟩
  · intro x hx
    rw [ProjSpace.nonzeroLocus_formSec]
    exact hfP _ (Finset.mem_image_of_mem _ (hs.mem_toFinset.2 hx))
  · rw [ProjSpace.nonzeroLocus_formSec]
    exact hJ1 f hfJ
  · rw [ProjSpace.nonzeroLocus_formSec]
    exact Proj.isAffineOpen_basicOpen _ f hf hd

theorem exists_sections_orbit_subset {Γ : Type} [Group Γ] [Finite Γ] {R : Type} [CommRing R] {X : Scheme.{0}}
    {s : X ⟶ Sp R} (ρ : Γ →* Aut X) (h : IsQProjOver s) :
    ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧
      ∀ x : X, ∃ i, ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i) := by
  classical
  obtain ⟨N, i, hi, hqc, he⟩ := h
  have : IsImmersion i := hi
  have : QuasiCompact i := hqc
  have hPc : CompactSpace (PSpace R N) := by
    have hc : IsCompact (⋃ k, (ProjSpace.chart R N k : Set (PSpace R N))) :=
      isCompact_iUnion fun k => (ProjSpace.isAffineOpen_chart R N k).isCompact
    rw [← TopologicalSpace.Opens.coe_iSup, ProjSpace.iSup_chart] at hc
    exact ⟨by simpa using hc⟩
  have hXc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace i
  have hmem : ∀ x, i x ∈ i.coborderRange := fun x => by
    exact subset_coborder (Set.mem_range_self x)
  have haffpre : ∀ D : (PSpace R N).Opens, D ≤ i.coborderRange → IsAffineOpen D →
      IsAffineOpen (i ⁻¹ᵁ D) := by
    intro D hD hA
    have h1 : IsAffineOpen (i.coborderRange.ι ⁻¹ᵁ D) :=
      hA.preimage_of_isOpenImmersion _ (by rwa [Scheme.Opens.opensRange_ι])
    have h2 := h1.preimage i.liftCoborder
    rwa [← Scheme.Hom.comp_preimage, i.liftCoborder_ι] at h2
  have key : ∀ x : X, ∃ n, 1 ≤ n ∧ ∃ t : (lbPow (ProjSpace.O1 R N) n).Sec,
      Set.range (fun g => i ((ρ g).hom x)) ⊆ Out.nonzeroLocus t ∧
        Out.nonzeroLocus t ≤ i.coborderRange ∧ IsAffineOpen (Out.nonzeroLocus t) :=
    fun x => exists_sec_nonzeroLocus_le (Set.finite_range _) _ (by rintro _ ⟨g, rfl⟩; exact hmem _)
  choose n hn t hts htU hta using key
  let W : X → Set X := fun x => {y | ∀ g, i ((ρ g).hom y) ∈ Out.nonzeroLocus (t x)}
  have hWo : ∀ x, IsOpen (W x) := fun x => by
    have hW : W x = ⋂ g, ((ρ g).hom ≫ i) ⁻¹' (Out.nonzeroLocus (t x) : Set (PSpace R N)) := by
      ext y
      simp [W]
    rw [hW]
    exact isOpen_iInter_of_finite fun g =>
      (Out.nonzeroLocus (t x)).isOpen.preimage ((ρ g).hom ≫ i).continuous
  have hWx : ∀ x, x ∈ W x := fun x g => hts x ⟨g, rfl⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hWx y⟩)
  let M := ∏ x ∈ F, n x
  have hdvd : ∀ x ∈ F, n x ∣ M := fun x hx => Finset.dvd_prod_of_mem n hx
  have hMpos : 0 < M := Finset.prod_pos fun x _ => hn x
  let e := F.equivFin
  let sec : F → (lbPow (ProjSpace.O1 R N) M).Sec := fun x =>
    GlobalTheory.secCast (Nat.mul_div_cancel' (hdvd x x.2)) (GlobalTheory.secPow (t x) (M / n x))
  have hloc : ∀ x : F, Out.nonzeroLocus (GlobalTheory.secPull (sec x) i) = i ⁻¹ᵁ Out.nonzeroLocus (t x) :=
    fun x => by
      rw [GlobalTheory.nonzeroLocus_secPull, GlobalTheory.nonzeroLocus_secCast, GlobalTheory.nonzeroLocus_secPow]
      exact Nat.div_pos (Nat.le_of_dvd hMpos (hdvd x x.2)) (hn x)
  refine ⟨(lbPow (ProjSpace.O1 R N) M).pull i, F.card, fun k => GlobalTheory.secPull (sec (e.symm k)) i,
    pull_isLB (GlobalTheory.isLB_lbPow (GlobalTheory.ProjSpace.O1_isLB R N) M) i, fun k => ?_, fun y => ?_⟩
  · rw [hloc]
    exact haffpre _ (htU _) (hta _)
  · obtain ⟨x, hxF, hy⟩ : ∃ x ∈ F, y ∈ W x := by simpa using hF (Set.mem_univ y)
    refine ⟨e ⟨x, hxF⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [hloc]
    exact hy g

theorem exists_isAmpleLB_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {R : Type} [CommRing R]
    {X Y : Scheme.{0}} {s : X ⟶ Sp R} {ρ : Γ →* Aut X} {π : X ⟶ Y} (hq : IsAffineQuotient ρ π)
    (h : IsQProjOver s) : ∃ L : LB Y, IsAmpleLB L := by
  obtain ⟨L, n, σ, hL, haff, hcov⟩ := exists_sections_orbit_subset ρ h
  have hsep : X.IsSeparated := by
    obtain ⟨N, i, hi, hqc, he⟩ := h
    have : IsImmersion i := hi
    have hs : IsSeparated s := by
      rw [← he]
      infer_instance
    exact ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  obtain ⟨L', m, σ', hL', haff', hcov'⟩ := GlobalTheory.QuotientNorm.exists_affine_cover_of_quotient Γ X Y ρ π
    ⟨hq.isAffineHom, hq.comp_eq, fun V => ⟨hq.app_injective V, fun f hf => hq.mem_range_app V f
      (fun g => ⟨hq.preimage_le V g, hf g _⟩)⟩⟩ hsep L n σ hL haff hcov
  refine ⟨L', ⟨hL', ?_, ?_⟩⟩
  · have hc : IsCompact (⋃ i, (Out.nonzeroLocus (σ' i) : Set Y)) :=
      isCompact_iUnion fun i => (haff' i).isCompact
    rw [← TopologicalSpace.Opens.coe_iSup, hcov'] at hc
    exact ⟨by simpa using hc⟩
  · intro y
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (σ' i) := by rw [hcov']; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨1, le_rfl, GlobalTheory.secToPow (σ' i) 1, ?_, ?_⟩
    · rw [GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]; exact hi
    · rw [GlobalTheory.nonzeroLocus_secToPow (σ' i) le_rfl]; exact haff' i

theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ X Y π sY Ga _ ρ hG hs hl hq
  have : Finite Ga := hG.finite
  let ρ' : Ga →* Aut X :=
    { toFun := fun a => ⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩
      map_one' := by
        ext1
        show ρ 1⁻¹ = _
        rw [inv_one, hG.one]
        rfl
      map_mul' := fun a c => by
        ext1
        show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
        rw [mul_inv_rev, hG.mul] }
  have hρ' : ∀ a, (ρ' a).hom = ρ a⁻¹ := fun a => rfl
  have : OrbitsInAffineOpens ρ' := OrbitsInAffineOpens.of_isQProjOver hq ρ'
  obtain ⟨Y', q, hQ⟩ := (exists_isAffineQuotient_iff ρ').mpr inferInstance
  obtain ⟨L', hL'⟩ := exists_isAmpleLB_of_isAffineQuotient hQ hq
  have hqi : ∀ a, ρ a ≫ q = q := fun a => by
    have := hQ.comp_eq a⁻¹
    rwa [hρ', inv_inv] at this
  obtain ⟨f, hf, -⟩ := GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG q hqi
  have hπi : ∀ a, (ρ' a).hom ≫ π = π := fun a => by rw [hρ']; exact hG.inv _
  have hfg : f ≫ hQ.desc π hπi = 𝟙 Y := by
    obtain ⟨u, -, hu⟩ := GlobalTheory.ZM.IsGaloisCover.existsUnique_desc hG π hG.inv
    have h1 := hu (f ≫ hQ.desc π hπi) (by
      show π ≫ f ≫ hQ.desc π hπi = π
      rw [← Category.assoc, hf, hQ.comp_desc])
    have h2 := hu (𝟙 Y) (by
      show π ≫ 𝟙 Y = π
      exact Category.comp_id π)
    rw [h1, h2]
  have hgf : hQ.desc π hπi ≫ f = 𝟙 Y' :=
    hQ.hom_ext (by rw [← Category.assoc, hQ.comp_desc, hf, Category.comp_id])
  have : IsIso f := ⟨⟨hQ.desc π hπi, hfg, hgf⟩⟩
  have hA : IsAmpleLB (L'.pull f) := GlobalTheory.IsAmpleLB.pull_of_isFinite hL' f
  have := hl
  exact GlobalTheory.IsAmpleLB.isQProjOver hA sY

end GlobalTheory.GaloisQuotient
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_target_of_isGaloisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  first | exact @GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover | (intros; apply GlobalTheory.LinDescent.exists_descent_of_isGaloisCover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_rigidified_faithfullyFlat_descent : Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | exact GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | (intros; apply GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_separated_galoisCover_of_free_action : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  first | exact @GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | exact GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | (intros; apply GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.galoisCover_descent_and_cartesian_squares : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  first | exact @GlobalTheory.ZM.galoisCover_descent | exact GlobalTheory.ZM.galoisCover_descent | (intros; apply GlobalTheory.ZM.galoisCover_descent <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace GaloisDescent

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := by
  unfold act
  exact pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := by
  unfold act
  exact pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) := by
  have hpb : IsPullback (pullback.snd T.hom π) (pullback.fst T.hom π) π T.hom :=
    (IsPullback.of_hasPullback T.hom π).flip
  exact ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 (pullback T.hom π) T.left (pullback.fst T.hom π) (act hc T)
    (pullback.snd T.hom π) T.hom (fun a => act_snd hc T a) pullback.condition.symm).2 hpb
    (fun a => act_fst hc T a)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g := by
  obtain ⟨f', -, huniq⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ f)
    (fun a => by rw [← Category.assoc, hc.inv])
  exact (huniq f rfl).trans (huniq g h.symm).symm

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  have h1 := up_left H x
  have h2 := up_left H y
  rw [e] at h1
  apply Over.OverMorphism.ext
  exact cover_ext (isGaloisCover_act hc T) (h1.symm.trans h2)

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  refine forall_congr' fun a => ?_
  change preHom _ w = pushHom _ _ w ↔ _
  rw [Over.OverMorphism.ext_iff]
  unfold preHom pushHom
  simp only [MonoidHom.mk'_apply, Over.comp_left, Over.homMk_left]
  unfold pushPt
  simp

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hinv : ∀ a, act hc T a ≫ (w.left ≫ φ) = w.left ≫ φ := fun a => by
    rw [← Category.assoc, (mem_equivariant hc hν).1 hw a, Category.assoc, hφ]
  obtain ⟨f', hf', -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ (isGaloisCover_act hc T)).1 G'.left (w.left ≫ φ) hinv
  have hw' : w.left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w w
  have hbase : f' ≫ G'.hom = T.hom := by
    apply cover_ext (isGaloisCover_act hc T)
    rw [← Category.assoc, hf', Category.assoc, H.w, ← Category.assoc, hw', pullback.condition]
  refine ⟨Over.homMk f' hbase, GlobalTheory.QuotientDescent.hom_ext H ?_⟩
  rw [up_left]
  simp [hf']

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := by
  rw [mem_equivariant]
  intro a
  have hu : (up H z).left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w (up H z)
  apply H.hom_ext
  · rw [Category.assoc, Category.assoc, hφ, up_left, ← Category.assoc, act_fst]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, ← Category.assoc (up H z).left, hu]
    exact act_snd hc T a

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have hsurj : ∀ (T : Over Y) (w : equivariant hc hν T), ∃ z : T ⟶ G', up H z = w.1 :=
    fun T w => exists_up hc H hν hφ w.2
  let e : ∀ T : Over Y, (T ⟶ G') ≃ equivariant hc hν T := fun T =>
    Equiv.ofBijective (fun z => ⟨up H z, up_mem hc H hν hφ z⟩)
      ⟨fun x y h => up_injective hc H (congrArg Subtype.val h),
       fun w => (hsurj T w).imp fun z hz => Subtype.ext hz⟩
  have hmap : ∀ {T T' : Over Y} (u : T' ⟶ T) (w : equivariant hc hν T),
      (Over.pullback π).map u ≫ w.1 ∈ equivariant hc hν T' := by
    intro T T' u w
    obtain ⟨z, hz⟩ := hsurj T w
    rw [← hz, ← up_comp]
    exact up_mem hc H hν hφ (u ≫ z)
  let F : (Over Y)ᵒᵖ ⥤ CommGrpCat :=
    { obj := fun T => CommGrpCat.of (equivariant hc hν T.unop)
      map := fun {T T'} u => CommGrpCat.ofHom
        { toFun := fun w => ⟨(Over.pullback π).map u.unop ≫ w.1, hmap u.unop w⟩
          map_one' := Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_one)
          map_mul' := fun w w' => Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_mul w.1 w'.1) }
      map_id := fun T => by
        ext w
        simp
      map_comp := fun u u' => by
        ext w
        simp }
  let α : (F ⋙ forget CommGrpCat).RepresentableBy G' :=
    { homEquiv := fun {T} => e T
      homEquiv_comp := fun {T T'} u z => Subtype.ext (up_comp H u z) }
  let inst : CommGrpObj G' := CommGrpObj.ofRepresentableBy G' F α
  refine ⟨inferInstance, inferInstance, H, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hmul : up H (x₀ * y₀) = up H x₀ * up H y₀ :=
    congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy G' (F ⋙ forget₂ CommGrpCat GrpCat) α).hom.app
      (Opposite.op (Over.mk (T.hom ≫ π)))).hom.map_mul x₀ y₀)
  let s₀ : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)) :=
    Over.homMk (pullback.lift (𝟙 T.left) T.hom (by simp)) (pullback.lift_snd _ _ _)
  have hs₀ : ∀ (z : Over.mk (T.hom ≫ π) ⟶ G') (t : T ⟶ G), z.left = t.left ≫ φ → s₀ ≫ up H z = t := by
    intro z t hz
    apply GlobalTheory.QuotientDescent.hom_ext H
    rw [Over.comp_left, Category.assoc, up_left, hz]
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)
  have key : s₀ ≫ up H (x₀ * y₀) = x * y := by
    rw [hmul, ← hs₀ x₀ x hx, ← hs₀ y₀ y hy]
    exact (preHom s₀).map_mul (up H x₀) (up H y₀)
  have hk := congrArg (fun t : T ⟶ G => t.left ≫ φ) key
  rw [← hk, Over.comp_left, Category.assoc, up_left]
  exact ((pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)).symm

end GaloisDescent

open GaloisDescent

theorem abelianScheme_descends_galoisCover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ X Y π sY Ga _ ρ G _ ν hc hq hab hν hν1 hνmul
  obtain ⟨hcomm, hsm, hpr, hgc⟩ := hab
  have := hc.finite
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have hdown : ∀ a, ν a ≫ G.hom = G.hom ≫ ρ a := fun a => (hν a).1.w
  have hinvG : ∀ a, ν a ≫ G.hom ≫ π = G.hom ≫ π := fun a => by
    rw [← Category.assoc, hdown, Category.assoc, hc.inv]
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ G.left) (a : Ga), y ≫ ν a = y → a = 1 := by
    intro k _ _ y a hy
    have hya : (y ≫ G.hom) ≫ ρ a = y ≫ G.hom := by
      rw [Category.assoc, ← hdown, ← Category.assoc, hy]
    have hy1 : (y ≫ G.hom) ≫ ρ 1 = y ≫ G.hom := by rw [hc.one, Category.comp_id]
    exact (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique hya hy1
  obtain ⟨Y₀, π₀, sY₀, -, hc₀, -, -, -⟩ := GlobalTheory.T.exists_separated_galoisCover_of_free_action K G.left (G.hom ≫ π ≫ sY) Ga ν hq hν1 hνmul
    (fun a => by rw [← Category.assoc G.hom π sY, ← Category.assoc, hinvG]) hfree
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares G.left Y₀ π₀ Ga ν hc₀).1 Y (G.hom ≫ π) hinvG
  have hsq : IsPullback G.hom π₀ π v :=
    ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 G.left Y₀ π₀ ν G.hom v hdown hv.symm).1 hc₀
  have H : IsPullback π₀ G.hom (Over.mk v).hom π := hsq.flip
  obtain ⟨inst, hcomm', hgp⟩ := exists_grpObj (G' := Over.mk v) (φ := π₀) hc H hν (fun a => hc₀.inv a)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) π :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsm' : Smooth v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ hsm
  have huc : UniversallyClosed v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have hlft : LocallyOfFiniteType v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have : Surjective π₀ := hc₀.onto
  have : IsFinite π₀ := hc₀.fin
  have : IsSeparated (π₀ ≫ v) := by rw [hv]; infer_instance
  have hsep : IsSeparated v := GlobalTheory.SemiAbelianDescent.isSeparated_of_comp π₀ v
  have hgc' : GeometricallyConnected v := GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback H
  exact ⟨Over.mk v, inst, π₀, ⟨hcomm', hsm', { toIsSeparated := hsep, toUniversallyClosed := huc, toLocallyOfFiniteType := hlft }, hgc'⟩, hgp, hc₀⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_descent_of_galoisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  atlas_forward_decl GlobalTheory.abelianScheme_descends_galoisCover
end

section
noncomputable section

namespace GlobalTheory.PolDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem kTriv_of_pull {S S' : Scheme.{0}} {f : S' ⟶ S} [IsAffineHom f] [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem relAmple_of_pull {S S' : Scheme.{0}} [IsLocallyNoetherian S] {f : S' ⟶ S} [IsFinite f] [Flat f]
    [Surjective f] {A : Over S} {A' : Over S'} [IsProper A.hom] {φ : A'.left ⟶ A.left} {L : LB A.left}
    {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hA : RelAmple A' L') : RelAmple A L := by
  have : IsFinite φ := MorphismProperty.of_isPullback (P := @IsFinite) h.flip inferInstance
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A' hL' hA (f ⁻¹ᵁ U) (hU.preimage f)
  have pre : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← h.w, Scheme.Hom.comp_preimage]
  rw [pre] at h₁
  have h₂ : IsAmpleLB ((L.pull φ).pull (φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)).ι) :=
    h₁.of_lbIso (LB.isLB_pull (LB.isLB_pull hL _) _)
      (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm)
  have h₃ : IsAmpleLB ((L.pull (A.hom ⁻¹ᵁ U).ι).pull (φ ∣_ (A.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull (LB.isLB_pull hL _) _)
      (FiniteAmple.lbIso_pull_pull _ hL (morphismRestrict_ι φ _).symm)).1 h₂
  have : Surjective (φ ∣_ A.hom ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  exact FiniteAmple.isAmpleLB_of_pull _ (LB.isLB_pull hL _) h₃

end GlobalTheory.PolDescent

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem relAmple_kTriv_of_finite_etale_cover : ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] (π : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), IsFinite π → Etale π → Surjective π → IsAbelianScheme G → L.IsLB → L'.IsLB → IsGrpPullback G' G π φ → LBIso L' (L.pull φ) → (Out.RelAmple G' L' → Out.RelAmple G L) ∧ (Out.KTriv G' L' → Out.KTriv G L) := by
  intro S S' _ π G G' _ _ φ L L' _ _ _ hG hL hL' h hw
  have := hG.proper
  exact ⟨PolDescent.relAmple_of_pull h.1 hL hL' hw, PolDescent.kTriv_of_pull h hL hL' hw⟩

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleDescent

open GlobalTheory.CechPic

theorem exists_linearisation {Ga : Type} [Group Ga] {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X)
    (e : X ⟶ Y) (he : e ≫ p = 𝟙 X) (hs : Function.Surjective p.appTop.hom) (ρ : Ga → (X ⟶ X)) (τ : Ga → (Y ⟶ Y))
    (ρm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) (τm : ∀ a c, τ (a * c) = τ a ≫ τ c) (hτ : ∀ a, e ≫ τ a = ρ a ≫ e)
    (r : (L.pull e).Gen) (hr : r.IsGen) (hiso : ∀ a, LBIso L (L.pull (τ a))) :
    ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ a] ![1, -1]), (∀ a, (u a).IsGen) ∧
      ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (τ a))) := by
  choose u hu hn using fun g => RigidLinearisation.exists_normalised hL p e he (ρ g) (τ g) (hτ g) r hr (hiso g)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => ?_⟩
  exact RigidLinearisation.val_eq_of_rigid hL (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
      simp) e (eq_one_of_surjective_appTop_of_section p e he hs) (hu _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
      have a₁ := hn (g * h) X (𝟙 X) y J hJ
      have a₂ := hn g X (𝟙 X) y J hJ
      have a₃ := hn h X (ρ g) y J hJ
      simp only [Category.id_comp] at a₁ a₂
      rw [val_mul hJ, val_pull hJ, hτ g, a₁, a₂, a₃, ρm]
      simp) _ _ y J hJ

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

abbrev fibre (T : Over S) (j : S' ⟶ S) : Over S' := Over.mk (pullback.snd T.hom j)

abbrev fibreProj (T : Over S) (j : S' ⟶ S) : Over.mk ((fibre T j).hom ≫ j) ⟶ T :=
  Over.homMk (pullback.fst T.hom j) pullback.condition

theorem exists_liftPt (h : IsGrpPullback B A j φ) {T : Over S} (p : T ⟶ A) :
    ∃ x : fibre T j ⟶ B, pushPt h.1.w x = fibreProj T j ≫ p :=
  ⟨Over.homMk (h.1.lift _ _ (Over.w (fibreProj T j ≫ p))) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem pushPt_comp (h : IsGrpPullback B A j φ) {T : Over S'} (x : T ⟶ B) {a : A ⟶ A} {a' : B ⟶ B}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem one_comm (h : IsGrpPullback B A j φ) : eSec B ≫ φ = j ≫ eSec A := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ B) = η[B] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[A]).left = _
  simp [eSec]

theorem exists_oAct (hR : Out.RigiditySt) {O : Type} [CommRing O] (hA : IsAbelianScheme A) [Epi j] [Epi φ]
    (h : IsGrpPullback B A j φ) (i : OAct O B) (hi : ∀ x, ∃ f : A.left ⟶ A.left, (i.act x).left ≫ φ = φ ≫ f) :
    ∃ a : OAct O A, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose f₀ hf₀ using hi
  let f : O → (A ⟶ A) := fun x => Over.homMk (f₀ x) (by
    rw [← cancel_epi φ, ← Category.assoc, ← hf₀, Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have hf : ∀ x, (i.act x).left ≫ φ = φ ≫ (f x).left := hf₀
  have ext : ∀ {a b : A ⟶ A}, φ ≫ a.left = φ ≫ b.left → a = b := fun e =>
    Over.OverMorphism.ext ((cancel_epi φ).1 e)
  refine ⟨⟨f, fun x => hR _ _ _ hA hA _ (Over.OverMorphism.ext ?_), ext ?_, fun x y => ext ?_,
    fun x y => ext ?_⟩, hf⟩
  · have := i.hom x
    have e : eSec B ≫ (i.act x).left = eSec B := congrArg (fun q => q.left) (IsMonHom.one_hom (i.act x))
    show eSec A ≫ (f x).left = eSec A
    rw [← cancel_epi j]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [← one_comm h, Category.assoc, ← hf, ← Category.assoc, e]
  · rw [← hf, i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · rw [← hf, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · let φ₀ : Over.mk (B.hom ≫ j) ⟶ A := Over.homMk φ h.1.w
    have h := h.2 B (i.act x) (i.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, i.add, ← h]
    rfl

variable [IsCommMonObj A]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Pic A.left) : Pic T.left :=
  ∑ I : Finset (Fin n), ((-1 : ℤ) ^ (n - I.card)) • pull (psum A x I).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) {L : LB A.left} (hL : L.IsLB) : (cubeLB A x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) {L : LB A.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  (cls_linComb hL _ _ _).trans (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl)

theorem pull_cubeCls [IsCommMonObj B] (h : IsGrpPullback B A j φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ B)) (x : Fin n → (T ⟶ A)) (U : Over.mk (T'.hom ≫ j) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (c : Pic A.left) :
    pull U.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x U hx I]

theorem pull_cubeCls_pre {T' T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (U : T' ⟶ T) (c : Pic A.left) :
    pull U.left (cubeCls x c) = cubeCls (fun i => U ≫ x i) c := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun q : T' ⟶ A => _ • pull q.left c) (psum_hom (preHom U) x I)

theorem cubeCls_one {T : Over S} (c : Pic A.left) : cubeCls (fun _ : Fin 3 => (1 : T ⟶ A)) c = 0 := by
  have e : ∀ I : Finset (Fin 3), psum A (fun _ : Fin 3 => (1 : T ⟶ A)) I = 1 := fun I =>
    (psum_hom (1 : (T ⟶ A) →* (T ⟶ A)) (fun _ => 1) I).symm
  unfold cubeCls
  simp only [e]
  rw [← Finset.sum_smul, show ∑ I : Finset (Fin 3), (-1 : ℤ) ^ (3 - I.card) = 0 by decide, zero_smul]

end Points

theorem eq_zero_of_pull (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) [Flat π] [Surjective π]
    [QuasiCompact π] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (c : Pic A.left)
    (h₀ : pull (η[A]).left c = 0) (h₁ : pull (fibreProj A π).left c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (T.exists_gen_of_rigidified_faithfullyFlat_descent hG S S' π A N hA hN ‹_› ‹_› ‹_›
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (hG : Out.GlobalFnsSt) {X Y : Scheme.{0}}
  {π : X ⟶ Y} [Flat π] [Surjective π] [QuasiCompact π] (t : SAB H X) {A : Over Y} [GrpObj A] [IsCommMonObj A]
  (hA : IsAbelianScheme A) {φ : t.G.left ⟶ A.left} (gp : IsGrpPullback t.G A π φ) (c : Pic A.left)
  (hc : pull φ c = cls t.PP.L t.PP.isLB)

include hG hA gp hc

theorem theorem_of_cube_descends : cubeCls (x3 A) c = 0 := by
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine eq_zero_of_pull hG π hA₃ _ ?_ ?_
  · rw [pull_cubeCls_pre, ← cubeCls_one c]
    congr 1
    funext k
    fin_cases k <;> simp [x3, Hom.one_def]
  · choose x hx using fun k => exists_liftPt gp (x3 A k)
    have e : cubeCls (x3 t.G) (cls t.PP.L t.PP.isLB) = 0 :=
      (cls_cube _ _).symm.trans ((cls_eq_zero_iff _).2 ⟨t.cub.t, t.cub.isGen⟩)
    have e' := congrArg (pull (lift (x 0) (lift (x 1) (x 2))).left) e
    rw [pull_cubeCls_pre, map_zero] at e'
    rw [pull_cubeCls gp x _ _ hx, hc, ← e']
    congr 1
    funext k
    fin_cases k <;> simp [x3]

theorem cubeCls_adj (act : OAct (𝓞 E) A) (hact : ∀ x, (t.act.act x).left ≫ φ = φ ≫ (act.act x).left) (a : 𝓞 E) :
    cubeCls ![fst A A ≫ act.act a, snd A A] c = cubeCls ![fst A A, snd A A ≫ act.act (H.bar a)] c := by
  have hA₂ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have := act.hom a
  have := act.hom (H.bar a)
  refine sub_eq_zero.1 (eq_zero_of_pull hG π hA₂ _ ?_ ?_)
  · rw [map_sub, pull_cubeCls_pre, pull_cubeCls_pre, sub_eq_zero]
    have e₁ : η[A ⊗ A] ≫ fst A A = 1 := by simp [Hom.one_def]
    have e₂ : η[A ⊗ A] ≫ snd A A = 1 := by simp [Hom.one_def]
    congr 1
    funext k
    fin_cases k
    · show η[A ⊗ A] ≫ fst A A ≫ act.act a = η[A ⊗ A] ≫ fst A A
      rw [← Category.assoc, e₁, MonObj.one_comp]
    · show η[A ⊗ A] ≫ snd A A = η[A ⊗ A] ≫ snd A A ≫ act.act (H.bar a)
      rw [← Category.assoc, e₂, MonObj.one_comp]
  · obtain ⟨x, hx⟩ := exists_liftPt gp (fst A A)
    obtain ⟨y, hy⟩ := exists_liftPt gp (snd A A)
    have e : cubeCls _ (cls t.PP.L t.PP.isLB) = cubeCls _ (cls t.PP.L t.PP.isLB) :=
      (cls_cube _ _).symm.trans (((cls_eq_iff _ _).2 (t.adj a)).trans (cls_cube _ _))
    have e' := congrArg (pull (lift x y).left) e
    rw [pull_cubeCls_pre, pull_cubeCls_pre] at e'
    rw [map_sub, sub_eq_zero, pull_cubeCls gp ![x ≫ t.act.act a, y] _ _ (fun k => ?_),
      pull_cubeCls gp ![x, y ≫ t.act.act (H.bar a)] _ _ (fun k => ?_), hc]
    · refine Eq.trans ?_ (e'.trans ?_)
      · congr 1
        funext k
        fin_cases k <;> simp
      · congr 1
        funext k
        fin_cases k <;> simp
    · fin_cases k
      · exact hx
      · exact (pushPt_comp gp y (hact _)).trans (by rw [hy, Category.assoc]; rfl)
    · fin_cases k
      · exact (pushPt_comp gp x (hact a)).trans (by rw [hx, Category.assoc]; rfl)
      · exact hy

omit hG hA [Flat π] [Surjective π] [QuasiCompact π] in

theorem pull_cubeCls_prim (act : OAct (𝓞 E) A) (hact : ∀ x, (t.act.act x).left ≫ φ = φ ≫ (act.act x).left) :
    pull φ (cubeCls ![𝟙 A, act.act H.w0] c) = cls t.PP.L t.PP.isLB := by
  let U : Over.mk (t.G.hom ≫ π) ⟶ A := Over.homMk φ gp.1.w
  have e := pull_cubeCls gp ![𝟙 t.G, t.act.act H.w0] ![𝟙 A, act.act H.w0] U (fun k => by
    fin_cases k
    · exact Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    · exact Over.OverMorphism.ext (hact _)) c
  rw [hc] at e
  exact e.trans ((cls_cube _ _).symm.trans ((cls_eq_iff _ _).2 t.prim).symm)

end Triple

theorem exists_sab_descent_of_galoisCover : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (t : SAB H X) (g : ℕ) (ν : ∀ a, SABMap t t (ρ a)), IsGaloisCover Ga ρ π → IsQProjOver sY → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (ν 1).φ = 𝟙 _ → (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) → ∃ (t' : SAB H Y) (m : SABMap t t' π), (∀ a, (ν a).φ ≫ m.φ = m.φ) ∧ IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro hL _ _ E _ _ _ H K _ X Y π sY Ga _ ρ t g ν hπ hq hp _ ha hk ν₁ νm
  have hG := hL.globalFns
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have : IsLocallyNoetherian Y := by
    obtain ⟨N, i, hi, -, rfl⟩ := hq
    have := isProper_str K N
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str K N)
  have hB : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  obtain ⟨A, _, φ, hA, gp, hφ⟩ := T.exists_abelianScheme_descent_of_galoisCover K X Y π sY Ga ρ t.G (fun a => (ν a).φ) hπ
    (RelAmpleQProj.isQProjOver_of_relAmple K X (π ≫ sY) t.G t.PP.L
      (isQProjOver_comp_of_isFinite_noetherian K X Y π sY hπ.fin hq) t.PP.isLB ha) hB (fun a => (ν a).cart) ν₁ νm
  have := hA.comm
  have := hφ.fin
  have := hφ.etale
  have := hφ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective _
  have : Epi φ := Flat.epi_of_flat_of_surjective _
  obtain ⟨act, hact⟩ := exists_oAct hL.rigidity hA gp t.act fun x => by
    obtain ⟨f, hf, -⟩ := (galoisCover_descent _ _ φ Ga _ hφ).1 _ ((t.act.act x).left ≫ φ) fun a => by
      have e : (t.act.act x).left ≫ (ν a).φ = (ν a).φ ≫ (t.act.act x).left := (ν a).act x
      rw [← Category.assoc, ← e, Category.assoc, hφ.inv a]
    exact ⟨f, hf.symm⟩
  obtain ⟨u, hu₁, hu₂⟩ := exists_linearisation t.PP.isLB t.G.hom (eSec t.G) (Over.w η[t.G]) (hG _ _ hB).2 ρ
    (fun a => (ν a).φ) hπ.mul νm (fun a => one_comm (ν a).cart) t.PP.rig t.PP.rigGen fun a => by
      obtain ⟨w, hw, -⟩ := (ν a).lin
      exact ⟨w, hw⟩
  obtain ⟨M, hM, iM⟩ := T.exists_descent_linearised_lineBundle_galoisCover _ _ φ Ga _ t.PP.L hφ t.PP.isLB u hu₁ hu₂
  have hc : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := ((cls_eq_iff _ (pull_isLB hM φ)).2 iM).symm
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hG E H Y A act M hA hM
    ((cls_eq_zero_iff (isLB_cube _ hM)).1 ((cls_cube _ hM).trans (theorem_of_cube_descends hG t hA gp _ hc)))
    fun a => (cls_eq_iff (isLB_cube _ hM) (isLB_cube _ hM)).1
      ((cls_cube _ hM).trans ((cubeCls_adj hG t hA gp _ hc act hact a).trans (cls_cube _ hM).symm))
  have iP : LBIso t.PP.L (PP.L.pull φ) := (cls_eq_iff t.PP.isLB (pull_isLB PP.isLB φ)).1
    ((pull_cubeCls_prim t gp _ hc act hact).symm.trans (congrArg (pull φ)
      ((cls_cube _ hM).symm.trans ((cls_eq_iff PP.isLB (isLB_cube _ hM)).2 iso).symm)))
  let t' : SAB H Y := ⟨A, isSemiAbelian_of_isAbelianScheme A hA, act, PP, cub, sym, adj, prim⟩
  obtain ⟨m, hm⟩ := exists_sabMap_of_isProper_of_lbIso hG E H Y X t' t π φ hA.proper gp iP hact
  obtain ⟨h₁, h₂⟩ := relAmple_kTriv_of_finite_etale_cover Y X π A t.G φ PP.L t.PP.L hπ.fin hπ.etale hπ.onto hA
    PP.isLB t.PP.isLB gp iP
  exact ⟨t', m, fun a => by rw [hm]; exact hφ.inv a, hA.proper, h₁ ha, h₂ hk⟩

end GlobalTheory.TripleDescent
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_descent_galoisCover : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (t : SAB H X) (g : ℕ) (ν : ∀ a, SABMap t t (ρ a)), IsGaloisCover Ga ρ π → IsQProjOver sY → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (ν 1).φ = 𝟙 _ → (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) → ∃ (t' : SAB H Y) (m : SABMap t t' π), (∀ a, (ν a).φ ≫ m.φ = m.φ) ∧ IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | exact GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | (intros; apply GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelGroup

open GlobalTheory.LevelFibre GlobalTheory.Moduli.LevelAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Field

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem mem_of_gens {l : Level H} (T : Subfield (KA l)) (h₁ : (baseKA l).ρ ∈ T) (h₂ : (baseKA l).ζ ∈ T) (x : KA l) :
    x ∈ T := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  | algebraMap q =>
    have : (⟨algebraMap ℚ ℂ q, (IntermediateField.adjoin ℚ {H.rt0, zeta l.A}).algebraMap_mem q⟩ : KA l) = (q : KA l) :=
      Subtype.ext (by simp)
    rw [this]
    exact SubfieldClass.ratCast_mem T q
  | add x y hx hy a b => exact T.add_mem a b
  | inv x hx a => exact T.inv_mem a
  | mul x y hx hy a b => exact T.mul_mem a b

theorem ringHom_ext {l : Level H} {K : Type} [Field K] {β β' : KA l →+* K} (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ)
    (h₂ : β (baseKA l).ζ = β' (baseKA l).ζ) : β = β' :=
  RingHom.ext fun x => mem_of_gens (β.eqLocusField β') h₁ h₂ x

theorem exists_factor {l : Level H} {K : Type} [Field K] (β β' : KA l →+* K) (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ)
    {n : ℤ} (h₂ : β (baseKA l).ζ ^ n = β' (baseKA l).ζ) : ∃ σ : KA l →+* KA l, β.comp σ = β' := by
  have h : ∀ x, ∃ y, β y = β' x := fun x =>
    mem_of_gens (β.fieldRange.comap β') ⟨_, h₁⟩ ⟨(baseKA l).ζ ^ n, (map_zpow₀ _ _ _).trans h₂⟩ x
  choose σ hσ using h
  refine ⟨{ toFun := σ
            map_one' := β.injective (by rw [hσ, map_one, map_one])
            map_mul' := fun a b => β.injective (by rw [hσ, map_mul, map_mul, hσ, hσ])
            map_zero' := β.injective (by rw [hσ, map_zero, map_zero])
            map_add' := fun a b => β.injective (by rw [hσ, map_add, map_add, hσ, hσ]) }, RingHom.ext hσ⟩

theorem zeta_zpow_congr (l : Level H) {i j : ℤ} (h : (l.A : ℤ) ∣ i - j) : (baseKA l).ζ ^ i = (baseKA l).ζ ^ j := by
  have h0 : (baseKA l).ζ ≠ 0 := (baseKA l).ζ_prim.ne_zero l.A_pos.ne'
  rw [← sub_add_cancel i j, zpow_add₀ h0, ((baseKA l).ζ_prim.zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]

end Field

theorem exists_finite_mod (D : Datum H) {n : ℕ} (hn : 0 < n) : ∃ (Q : Type) (_ : Finite Q)
    (π : (D.La →ₗ[𝓞 E] D.La) → Q), ∀ f f', π f = π f' → ∀ a, D.ModN n (f a - f' a) := by
  let N : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  haveI := D.fin
  haveI : Module.Finite ℤ (D.La ⧸ N) := Module.Finite.trans (𝓞 E) _
  haveI : Finite (D.La ⧸ N) := Module.finite_of_fg_torsion (M := D.La ⧸ N) fun x => by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • N.mkQ x = 0
    rw [natCast_zsmul, ← map_nsmul]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := D.fin.fg_top
  refine ⟨s → D.La ⧸ N, inferInstance, fun f x => N.mkQ (f x), fun f f' h a => ?_⟩
  have : N.mkQ ∘ₗ f = N.mkQ ∘ₗ f' := LinearMap.ext_on hs fun x hx => congrFun h ⟨x, hx⟩
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq N).1 (LinearMap.congr_fun this a)
  exact ⟨c, hc.symm⟩

section Obj

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_eq_of_point (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {a c : D.La}
    (h : x ≫ (o.eta a).left = x ≫ (o.eta c).left) : o.eta a = o.eta c := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x β hβ
  let P : D.La → (Over.mk x ⟶ o.t.G) := fun a => toUnit _ ≫ o.eta a
  have hP : ∀ a b, P (a + b) = P a * P b := fun a b => by
    simp only [P]; rw [o.eta_add, MonObj.comp_mul]
  refine eta_congr o (mem_of_eq_one l I P hP (fun b hb => ?_) hI (sub_eq_one P hP ?_))
  · simp only [P]; rw [o.eta_ker b hb, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    simp only [P]
    rw [unit_left, unit_left, h]

theorem etaA_eq_of_point (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {a c : D.La}
    (h : x ≫ (o.etaA a).left = x ≫ (o.etaA c).left) : o.etaA a = o.etaA c := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -, hI, -⟩ := o.geom k x β hβ
  refine etaA_congr o (modN_of_ev_eq I l.A_pos ?_)
  rw [← hI, ← hI]
  apply Over.OverMorphism.ext
  rw [unit_left, unit_left, h]

def twistObj {s' : S ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s') (g : Sim D) (hpq : 1 ≤ D.p + D.q) (b' : Base l (KA l))
    (hρ : b'.ρ = (baseKA l).ρ) (hζ : b'.ζ = (baseKA l).ζ ^ g.ν l.A) : Obj D l b' s' where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g.f l.M a)
  eta_add a c := by rw [map_add, o.eta_add]
  eta_ker a ha := o.eta_ker _ (LevelTwist.map_mem_smul_top _ _ ha)
  etaA a := o.etaA (g.f l.A a)
  etaA_add a c := by rw [map_add, o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ', hA', hM⟩ := o.geom k x β hx
    refine ⟨hρ ▸ hd, LevelTwist.twist I g ((SimAlg.sim_group E H D hpq).1 g), ?_, fun a => hA' _,
      fun a ha => hM _ (LevelTwist.map_mem_smul_top _ _ ha)⟩
    rw [LevelTwist.twist_ζ, hζ, map_zpow₀, ← hζ', Units.val_zpow_eq_zpow_val]

theorem pow_left_comp {S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {σ : 𝟙_ (Over S') ⟶ t'.G} {τ : 𝟙_ (Over S) ⟶ t.G} (h : σ.left ≫ m.φ = f ≫ τ.left) (d : ℕ) :
    (σ ^ d).left ≫ m.φ = f ≫ (τ ^ d).left := by
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart (𝟙 S') f (Category.id_comp f)
  have h₁ : e (toUnit _ ≫ σ) = toUnit _ ≫ τ := by
    apply Over.OverMorphism.ext
    rw [he, unit_left, unit_left, Category.id_comp]; exact h
  have h₂ := congrArg (fun w => (w ^ d).left) h₁
  simp only [← map_pow, ← MonObj.comp_pow, he, unit_left, Category.id_comp] at h₂
  exact h₂

end Obj

section Action

variable {l l₂ : Level H} (Xo : Moduli D l₂) (jK : KA l →+* KA l₂)

structure Twist (g : Sim D) (σ : KA l₂ →+* KA l₂) (f : Xo.X ⟶ Xo.X) : Prop where
  fix : σ.comp jK = jK
  root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A
  lowM : ∀ a, Xo.univ.eta (g.f l₂.M a) ^ (l₂.M / l.M) = Xo.univ.eta a ^ (l₂.M / l.M)
  lowA : ∀ a, Xo.univ.etaA (g.f l₂.A a) ^ (l₂.A / l.A) = Xo.univ.etaA a ^ (l₂.A / l.A)
  comm : f ≫ Xo.s = Xo.s ≫ spMap σ
  map : ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
    (∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left

theorem reduced : IsReduced Xo.X := by
  haveI := Xo.smooth
  exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim _)).1

variable {Xo jK}

theorem jK_rho (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : jK (baseKA l).ρ = (baseKA l₂).ρ :=
  lowerBase_rho jK hj

theorem rho_of_fix (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) {K : Type} [Field K] {β β' : KA l₂ →+* K}
    (h : β.comp jK = β'.comp jK) : β (baseKA l₂).ρ = β' (baseKA l₂).ρ := by
  rw [← jK_rho hj]; exact RingHom.congr_fun h _

def baseVia (σ : KA l₂ →+* KA l₂) : Base l₂ (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := σ (baseKA l₂).ζ
  ζ_prim := (baseKA l₂).ζ_prim.map_of_injective σ.injective

theorem existsUnique_twist (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} (fix : σ.comp jK = jK) (root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A) :
    ∃! f : Xo.X ⟶ Xo.X, f ≫ Xo.s = Xo.s ≫ spMap σ ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
      (∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left := by
  obtain ⟨f, ⟨h₁, ⟨m⟩⟩, hu⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo _ (baseVia σ) σ _ Xo.s
    (twistObj Xo.univ g hpq (baseVia σ) rfl root) (reduced Xo) (rho_of_fix hj (β' := RingHom.id _) fix) rfl
  exact ⟨f, ⟨h₁, m.toSABMap, m.eta, m.etaA⟩, fun f' ⟨a, ν, b, c⟩ => hu f' ⟨a, ⟨⟨ν, b, c⟩⟩⟩⟩

theorem Twist.unique (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g g' : Sim D} {σ σ' : KA l₂ →+* KA l₂} {f f' : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f) (h' : Twist Xo jK g' σ' f')
    (hσ : σ = σ') (hM : ∀ a, Xo.univ.eta (g.f l₂.M a) = Xo.univ.eta (g'.f l₂.M a))
    (hA : ∀ a, Xo.univ.etaA (g.f l₂.A a) = Xo.univ.etaA (g'.f l₂.A a)) : f = f' := by
  subst hσ
  obtain ⟨ν, a, b⟩ := h'.map
  exact (existsUnique_twist hpq hj h.fix h.root).unique ⟨h.comm, h.map⟩
    ⟨h'.comm, ν, fun x => by rw [hM]; exact a x, fun x => by rw [hA]; exact b x⟩

theorem Twist.one : Twist Xo jK (SimAlg.one D) (RingHom.id _) (𝟙 _) where
  fix := rfl
  root := (zpow_one _).symm
  lowM _ := rfl
  lowA _ := rfl
  comm := by rw [spMap_id', Category.id_comp, Category.comp_id]
  map := ⟨ObjLower.sabId _, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

theorem Twist.mul {g g' : Sim D} {σ σ' : KA l₂ →+* KA l₂} {f f' : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    (h' : Twist Xo jK g' σ' f') : Twist Xo jK (SimAlg.mul g g') (σ.comp σ') (f ≫ f') where
  fix := by rw [RingHom.comp_assoc, h'.fix, h.fix]
  root := by rw [RingHom.comp_apply, h'.root, map_zpow₀, h.root, ← zpow_mul]; rfl
  lowM a := (h.lowM _).trans (h'.lowM a)
  lowA a := (h.lowA _).trans (h'.lowA a)
  comm := by rw [Category.assoc, h'.comm, ← Category.assoc, h.comm, Category.assoc, spMap_comp']
  map := by
    obtain ⟨ν, a, b⟩ := h.map
    obtain ⟨ν', a', b'⟩ := h'.map
    obtain ⟨n, hn⟩ := exists_comp_sabMap ν ν' rfl
    refine ⟨n, fun x => ?_, fun x => ?_⟩
    · rw [hn, Category.assoc, ← a', ← Category.assoc, ← Category.assoc, ← a]; rfl
    · rw [hn, Category.assoc, ← b', ← Category.assoc, ← Category.assoc, ← b]; rfl

theorem Twist.exists_inv (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f) :
    ∃ g' σ' f', Twist Xo jK g' σ' f' ∧ f ≫ f' = 𝟙 _ := by
  obtain ⟨g', hg'⟩ := (SimAlg.sim_group E H D hpq).2.2.2 g
  have hz : σ (baseKA l₂).ζ ^ g'.ν l₂.A = (baseKA l₂).ζ := by
    rw [h.root, ← zpow_mul, zeta_zpow_congr l₂ (hg' _ l₂.A_pos).2, zpow_one]
  obtain ⟨σ', hσ'⟩ := exists_factor σ (RingHom.id _) (rho_of_fix hj h.fix) hz
  have fix : σ'.comp jK = jK := RingHom.ext fun x => σ.injective
    ((RingHom.congr_fun hσ' (jK x)).trans (RingHom.congr_fun h.fix x).symm)
  have root : σ' (baseKA l₂).ζ = (baseKA l₂).ζ ^ g'.ν l₂.A := σ.injective
    ((RingHom.congr_fun hσ' _).trans (by rw [map_zpow₀, hz]; rfl))
  have eM : ∀ a, Xo.univ.eta (g.f l₂.M (g'.f l₂.M a)) = Xo.univ.eta a := fun a =>
    eta_congr _ (LevelFibre.mem_of_modN l₂ ((hg' _ (level_pos l₂)).1 a).2)
  have eA : ∀ a, Xo.univ.etaA (g.f l₂.A (g'.f l₂.A a)) = Xo.univ.etaA a := fun a =>
    etaA_congr _ ((hg' _ l₂.A_pos).1 a).2
  obtain ⟨f', ⟨a, b⟩, -⟩ := existsUnique_twist (Xo := Xo) hpq hj fix root
  have h' : Twist Xo jK g' σ' f' :=
    ⟨fix, root, fun x => by rw [← h.lowM, eM], fun x => by rw [← h.lowA, eA], a, b⟩
  exact ⟨g', σ', f', h', (h.mul h').unique hpq hj Twist.one hσ' eM eA⟩

theorem Twist.lowers {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    (ν : SABMap Xo.univ.t Xo.univ.t f)
    (a : ∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left)
    (b : ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left) :
    Lowers l Xo.univ (fun x => Xo.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo.univ.etaA x ^ (l₂.A / l.A)) f ν.φ :=
  ⟨fun x => by
    have := pow_left_comp ν (a x) (l₂.M / l.M)
    rw [h.lowM] at this
    exact this, fun x => by
    have := pow_left_comp ν (b x) (l₂.A / l.A)
    rw [h.lowA] at this
    exact this⟩

def lowUniv (Xo : Moduli D l₂) (hd : l.Dvd l₂) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    Obj D l (lowerBase jK) Xo.s :=
  ObjLower.lower Xo.univ hd rfl (lowerBase_zeta jK hd.2.2 hj)

theorem pull_univ {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) (y : S' ⟶ S) : ∃ o' : Obj D l b (y ≫ s), Nonempty (ObjMap o' o y) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s (y ≫ s) y rfl rfl (by rw [spMap_id', Category.comp_id]) o

theorem Twist.eq_id_of_fixed (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (hy : y ≫ f = y) : f = 𝟙 _ := by
  obtain ⟨ν, a, b⟩ := h.map
  obtain ⟨o, ⟨p⟩⟩ := pull_univ (lowUniv Xo hd hj) y
  obtain ⟨n, hn⟩ := exists_comp_sabMap (t' := Xo.univ.t) p.toSABMap ν hy
  have hrig : n.φ = p.toSABMap.φ := obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) o y
    (Or.inl inferInstance) n p.toSABMap fun x => ⟨_, by
      have h₁ : (o.eta x).left ≫ p.toSABMap.φ = y ≫ (Xo.univ.eta x ^ (l₂.M / l.M)).left := p.eta x
      have h₂ := (h.lowers ν a b).1 x
      refine Eq.trans ?_ h₁.symm
      rw [hn]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ν.φ) h₁).trans ?_)
      rw [Category.assoc, h₂, ← Category.assoc, hy], rfl⟩
  have hid : ∀ τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G, y ≫ τ.left ≫ ν.φ = y ≫ τ.left := fun τ => by
    have hq : p.toSABMap.cart.1.lift (y ≫ τ.left) (𝟙 _) ((Category.assoc _ _ _).trans
        ((congrArg (y ≫ ·) (sec_w τ)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫ p.toSABMap.φ = y ≫ τ.left :=
      p.toSABMap.cart.1.lift_fst _ _ _
    rw [← Category.assoc, ← hq]
    exact (Category.assoc _ _ _).trans (congrArg _ (hn.symm.trans hrig))
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ Xo.s)
  have hσ : β.comp σ = β := spMap_inj (by
    rw [← spMap_comp', ← hβ, Category.assoc, ← h.comm, ← Category.assoc, hy])
  refine h.unique hpq hj Twist.one (RingHom.ext fun x => β.injective (RingHom.congr_fun hσ x))
    (fun x => eta_eq_of_point _ y ?_) (fun x => etaA_eq_of_point _ y ?_)
  · rw [← hid, a, ← Category.assoc, hy]; rfl
  · rw [← hid, b, ← Category.assoc, hy]; rfl

theorem exists_twist_of_lowers (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo.X)
    (t : SAB H (Sp k)) (mu : SABMap t Xo.univ.t y) (mu' : SABMap t Xo.univ.t y')
    (eM eA : D.La → (𝟙_ (Over (Sp k)) ⟶ t.G)) (hs : y ≫ Xo.s ≫ spMap jK = y' ≫ Xo.s ≫ spMap jK)
    (hl : Lowers l Xo.univ eM eA y mu.φ) (hl' : Lowers l Xo.univ eM eA y' mu'.φ) :
    ∃ g σ f, Twist Xo jK g σ f ∧ y ≫ f = y' := by
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ Xo.s)
  obtain ⟨β', hβ'⟩ := exists_spMap (y' ≫ Xo.s)
  have hb : β.comp jK = β'.comp jK := spMap_inj (by
    rw [← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])
  obtain ⟨o, ⟨p⟩⟩ := pull_univ Xo.univ y'
  obtain ⟨p', hp'⟩ := sab_cast (Category.id_comp y').symm p.toSABMap
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel mu' p'
  obtain ⟨n, hn⟩ := exists_comp_sabMap n' mu (Category.id_comp y)
  have key : ∀ (τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (τ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (ε : 𝟙_ (Over (Sp k)) ⟶ t.G) (d : ℕ),
      τ.left ≫ p.toSABMap.φ = y' ≫ τ₀.left → ε.left ≫ mu'.φ = y' ≫ (τ₀ ^ d).left →
      (τ ^ d).left ≫ n.φ = ε.left ≫ mu.φ := fun τ τ₀ ε d h₁ h₂ => by
    have h₃ : (τ ^ d).left ≫ n'.φ = ε.left := by
      apply mu'.cart.1.hom_ext
      · rw [Category.assoc]
        exact ((congrArg _ (hn'.symm.trans hp')).trans (pow_left_comp p.toSABMap h₁ d)).trans h₂.symm
      · rw [Category.assoc, n'.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact Category.id_comp _
    rw [hn, ← Category.assoc, h₃]
  obtain ⟨-, J, hJζ, hJA, hJ⟩ := Xo.univ.geom k y β hβ
  obtain ⟨-, I, hIζ, hIA, hI⟩ := o.geom k (𝟙 _) β' ((Category.id_comp _).trans hβ')
  obtain ⟨e, he⟩ := exists_ptEquiv n.cart (𝟙 _) y (Category.id_comp y)
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push n (𝟙 _) y (Category.id_comp y) e he I
  obtain ⟨h₁, h₂, h₃, h₄⟩ := obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ (baseKA l₂) _ Xo.s Xo.univ
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let PA : Out.PolAV Xo.X :=
    { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
      rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
  obtain ⟨g, hg⟩ := tateIso_differ_by_similitude E H D k _ _ _ (fun n p q a b _ hp hq ha hb =>
    unitOn_injective (((hL.weil _ PA n (Over.mk y)).1 p q hp hq).unique ha hb)) J J'
  have hel : ∀ τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, (e (toUnit _ ≫ τ)).left = τ.left ≫ n.φ := fun τ => by
    rw [he, unit_left, Category.id_comp]
  have hA : ∀ a, e (toUnit _ ≫ o.etaA a) = toUnit _ ≫ Xo.univ.etaA (g.f l₂.A a) := fun a => by
    rw [hIA, hJA, ← hJ', (hg _ l₂.A_pos).1]
  have hM : ∀ a, e (toUnit _ ≫ o.eta a) = toUnit _ ≫ Xo.univ.eta (g.f l₂.M a) := fun a => by
    obtain ⟨u, hu, v, hv, huv⟩ := level_split l₂
    have hcs : a = u • a + v • a := by rw [← add_smul, huv, one_smul]
    rw [hcs, o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hu trivial), map_add, Xo.univ.eta_add, map_smul, map_smul,
      Xo.univ.eta_ker _ (Submodule.smul_mem_smul hu trivial), _root_.one_mul, _root_.one_mul,
      hI _ (Submodule.smul_mem_smul hv trivial), hJ _ (Submodule.smul_mem_smul hv trivial), ← hJ',
      (hg _ (level_pos l₂)).1, map_smul]
  have hA' : ∀ a, (o.etaA a).left ≫ n.φ = y ≫ (Xo.univ.etaA (g.f l₂.A a)).left := fun a => by
    rw [← hel, hA, unit_left]
  have hM' : ∀ a, (o.eta a).left ≫ n.φ = y ≫ (Xo.univ.eta (g.f l₂.M a)).left := fun a => by
    rw [← hel, hM, unit_left]
  have hz : β (baseKA l₂).ζ ^ g.ν l₂.A = β' (baseKA l₂).ζ := by
    rw [← hJζ, ← hIζ, ← hJζ', (hg _ l₂.A_pos).2, Units.val_zpow_eq_zpow_val]
  obtain ⟨σ, hσ⟩ := exists_factor β β' (rho_of_fix hj hb) hz
  have fix : σ.comp jK = jK := RingHom.ext fun x => β.injective
    ((RingHom.congr_fun hσ (jK x)).trans (RingHom.congr_fun hb x).symm)
  have root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A := β.injective
    ((RingHom.congr_fun hσ _).trans (by rw [map_zpow₀, hz]))
  obtain ⟨f, ⟨hf, ν, a, b⟩, -⟩ := existsUnique_twist (Xo := Xo) hpq hj fix root
  refine ⟨g, σ, f, ⟨fix, root, fun x => eta_eq_of_point (lowUniv Xo hd hj) y ?_,
    fun x => etaA_eq_of_point (lowUniv Xo hd hj) y ?_, hf, ν, a, b⟩, ?_⟩
  · exact (pow_left_comp n (hM' x) _).symm.trans ((key _ _ _ _ (p.eta x) (hl'.1 x)).trans (hl.1 x))
  · exact (pow_left_comp n (hA' x) _).symm.trans ((key _ _ _ _ (p.etaA x) (hl'.2 x)).trans (hl.2 x))
  · obtain ⟨m, hm⟩ := exists_comp_sabMap n ν rfl
    refine (Xo.rep (Sp k) (y' ≫ Xo.s) inferInstance o).unique ⟨?_, ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩⟩ ⟨rfl, ⟨p⟩⟩
    · rw [Category.assoc, hf, ← Category.assoc, hβ, hβ', spMap_comp', hσ]
    · show _ ≫ m.φ = _
      rw [hm, ← Category.assoc, hM', Category.assoc, a, Category.assoc]
    · show _ ≫ m.φ = _
      rw [hm, ← Category.assoc, hA', Category.assoc, b, Category.assoc]

variable (Xo jK) in

def Grp : Type := {f : Xo.X ⟶ Xo.X // ∃ g σ, Twist Xo jK g σ f}

instance : One (Grp Xo jK) := ⟨⟨𝟙 _, _, _, Twist.one⟩⟩

instance : Mul (Grp Xo jK) := ⟨fun a c => ⟨a.1 ≫ c.1, by
  obtain ⟨g, σ, h⟩ := a.2
  obtain ⟨g', σ', h'⟩ := c.2
  exact ⟨_, _, h.mul h'⟩⟩⟩

theorem Grp.exists_inv (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) (a : Grp Xo jK) :
    ∃ c : Grp Xo jK, a * c = 1 := by
  obtain ⟨g, σ, h⟩ := a.2
  obtain ⟨g', σ', f', h', e⟩ := h.exists_inv hpq hj
  exact ⟨⟨f', g', σ', h'⟩, Subtype.ext e⟩

@[reducible] def Grp.group (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    Group (Grp Xo jK) :=
  letI : Inv (Grp Xo jK) := ⟨fun a => (Grp.exists_inv hpq hj a).choose⟩
  Group.ofRightAxioms (fun _ _ _ => Subtype.ext (Category.assoc _ _ _)) (fun _ => Subtype.ext (Category.comp_id _))
    fun a => (Grp.exists_inv hpq hj a).choose_spec

theorem Grp.finite (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : Finite (Grp Xo jK) := by
  obtain ⟨Q, _, π, hπ⟩ := exists_finite_mod D (level_pos l₂)
  obtain ⟨Q', _, π', hπ'⟩ := exists_finite_mod D l₂.A_pos
  haveI : NeZero l₂.A := ⟨l₂.A_pos.ne'⟩
  choose g σ h using fun a : Grp Xo jK => a.2
  refine Finite.of_injective (fun a => ((π ((g a).f l₂.M), π' ((g a).f l₂.A), ((g a).ν l₂.A : ZMod l₂.A)) :
    Q × Q' × ZMod l₂.A)) fun a c hac => Subtype.ext ?_
  simp only [Prod.mk.injEq] at hac
  refine (h a).unique hpq hj (h c) (ringHom_ext (rho_of_fix hj ((h a).fix.trans (h c).fix.symm)) ?_)
    (fun x => eta_congr _ (LevelFibre.mem_of_modN l₂ (hπ _ _ hac.1 x))) fun x => etaA_congr _ (hπ' _ _ hac.2.1 x)
  rw [(h a).root, (h c).root]
  exact zeta_zpow_congr l₂ ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hac.2.2.symm)

end Action

theorem exists_group_action : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (jK : KA l →+* KA l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (Xo₂.X ⟶ Xo₂.X)) (ν : ∀ a, SABMap Xo₂.univ.t Xo₂.univ.t (ρ a)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ (ν 1).φ = 𝟙 _ ∧ (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) ∧ (∀ a, ρ a ≫ Xo₂.s ≫ spMap jK = Xo₂.s ≫ spMap jK) ∧ (∀ a, Lowers l Xo₂.univ (fun x => Xo₂.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo₂.univ.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a).φ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo₂.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ Xo₂.X) (t : SAB H (Sp K)) (mu : SABMap t Xo₂.univ.t y) (mu' : SABMap t Xo₂.univ.t y') (eM eA : D.La → (𝟙_ (Over (Sp K)) ⟶ t.G)), y ≫ Xo₂.s ≫ spMap jK = y' ≫ Xo₂.s ≫ spMap jK → Lowers l Xo₂.univ eM eA y mu.φ → Lowers l Xo₂.univ eM eA y' mu'.φ → ∃ a, y ≫ ρ a = y' := by
  intro hL _ E _ _ _ H D l l₂ Xo jK hpq hd hj
  have hν : ∀ a : Grp Xo jK, ∃ ν : SABMap Xo.univ.t Xo.univ.t a.1,
      Lowers l Xo.univ (fun x => Xo.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo.univ.etaA x ^ (l₂.A / l.A)) a.1 ν.φ :=
    fun a => by
      obtain ⟨g, σ, h⟩ := a.2
      obtain ⟨ν, b, c⟩ := h.map
      exact ⟨ν, h.lowers ν b c⟩
  choose ν hν using hν
  have rig : ∀ (f : Xo.X ⟶ Xo.X) (m m' : SABMap Xo.univ.t Xo.univ.t f),
      (∀ x, (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m.φ = (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m'.φ) → m.φ = m'.φ :=
    fun f m m' h => obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) (lowUniv Xo hd hj) f
      (Or.inl (reduced Xo)) m m' fun x => ⟨_, h x, rfl⟩
  refine ⟨Grp Xo jK, Grp.group hpq hj, Grp.finite hpq hj, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_,
    fun a => ?_, hν, fun k _ _ y a hy => ?_, fun K _ _ y y' t mu mu' eM eA hs hl hl' => ?_⟩
  · exact rig (𝟙 _) (ν 1) (ObjLower.sabId _) fun x =>
      ((hν 1).1 x).trans ((Category.id_comp _).trans (Category.comp_id _).symm)
  · obtain ⟨n, hn⟩ := exists_comp_sabMap (ν a) (ν c) rfl
    refine (rig (a.1 ≫ c.1) (ν (a * c)) n fun x => ((hν (a * c)).1 x).trans ?_).trans hn
    have h₁ := (hν a).1 x
    have h₂ := (hν c).1 x
    simp only at h₁ h₂
    rw [hn, ← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
    rfl
  · obtain ⟨g, σ, h⟩ := a.2
    rw [← Category.assoc, h.comm, Category.assoc, spMap_comp', h.fix]
  · obtain ⟨g, σ, h⟩ := a.2
    exact Subtype.ext (h.eq_id_of_fixed hL hpq hd hj y hy)
  · obtain ⟨g, σ, f, h, e⟩ := exists_twist_of_lowers hL hpq hd hj y y' t mu mu' eM eA hs hl hl'
    exact ⟨⟨f, g, σ, h⟩, e⟩

end GlobalTheory.LevelGroup
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | (intros; apply GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelTower

theorem zeta_eq_pow {n m : ℕ} (hm : 0 < m) (h : n ∣ m) : zeta n = zeta m ^ (m / n) := by
  obtain ⟨c, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c hn, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact (baseKA l₂).ρ.2
  · rw [zeta_eq_pow l₂.A_pos h]
    exact pow_mem (baseKA l₂).ζ.2 _

theorem base_rho (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem base_zeta (l : Level H) : (((baseKA l).ζ : KA l) : ℂ) = zeta l.A := rfl

theorem exists_inclusion' {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    ∃ j : F →+* F', ∀ x, ((j x : F') : ℂ) = ((x : F) : ℂ) :=
  ⟨(IntermediateField.inclusion h).toRingHom, fun x => IntermediateField.coe_inclusion h x⟩

theorem exists_inclusion {l l₂ : Level H} (h : l.A ∣ l₂.A) :
    ∃ j : KA l →+* KA l₂, (∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ j (baseKA l).ρ = (baseKA l₂).ρ ∧
      j (baseKA l).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  obtain ⟨j, hj⟩ := exists_inclusion' (KA_le h)
  refine ⟨j, hj, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hj, base_rho, base_rho]
  · rw [hj, IntermediateField.coe_pow, base_zeta, base_zeta]
    exact zeta_eq_pow l₂.A_pos h

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_natCast H.d).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem finite_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : j.Finite := by
  letI := j.toAlgebra
  exact Module.Finite.of_restrictScalars_finite ℚ K K'

theorem etale_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : Etale (spMap j) := by
  letI := j.toAlgebra
  haveI : Module.Finite K K' := finite_of_numberField j
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this

end GlobalTheory.LevelTower

namespace GlobalTheory

open LevelTower

theorem nonempty_levelQuot : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  intro hL hL2 hTh E _ _ _ H D l l₂ Xo₂ hpq hdvd
  have hA : l.A ∣ l₂.A := hdvd.2.2
  obtain ⟨jK, hj, hjρ, hjζ⟩ := exists_inclusion hA
  haveI := finiteDimensional_KA l₂
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ :=
    GlobalTheory.LevelGroup.exists_group_action hL hL2 E H D l l₂ Xo₂ jK hpq hdvd hj
  have hq : IsQProjOver (Xo₂.s ≫ spMap jK) :=
    (isQProjOver_baseChange_and_finite_restrict _ _ jK Xo₂.X (Xo₂.s ≫ spMap jK)).2 Xo₂.s
      (finite_of_numberField jK) Xo₂.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    exists_isGaloisCover_of_isQProjOver (KA l) Xo₂.X (Xo₂.s ≫ spMap jK) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_of_isGaloisCover (KA l) _ Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension D.dim (π ≫ sY) := by
    rw [hπ]
    haveI := Xo₂.smooth
    haveI : Etale (spMap jK) := etale_of_numberField jK
    haveI : SmoothOfRelativeDimension 0 (spMap jK) := inferInstance
    have := smoothOfRelativeDimension_comp D.dim 0 Xo₂.s (spMap jK)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension D.dim sY := GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover (KA l) _ Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨t', m, hνm, hp, ha, hk⟩ := GlobalTheory.T.exists_abelianTriple_descent_galoisCover hL hL2 hTh E H (KA l) _ Y π sY Ga ρ Xo₂.univ.t _ ν hG hqY
    Xo₂.univ.proper (obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ _ _ _ Xo₂.univ).2.1
    Xo₂.univ.ample Xo₂.univ.ktriv hν1 hνmul
  obtain ⟨ob, m', hη, hηA⟩ := obj_descend_lower_level hL hL2 E H D l l₂ _ _ (baseKA l) (baseKA l₂) jK _ Y π sY
    Xo₂.s Ga ρ Xo₂.univ (fun a => (ν a).φ) t' m hdvd hjρ hjζ
    hπ hG hνm hlow hp ha hk
  refine ⟨⟨Y, sY, hqY, hsY, ob, π, jK, hj, hπ, hG.fin, hG.etale, hG.onto, m', hη, hηA, ?_⟩⟩
  intro K _ _ y y' t mu mu' eM eA h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans K y y' t mu mu' eM eA h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_levelQuot_of_level_dvd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  atlas_forward_decl GlobalTheory.nonempty_levelQuot
end
