import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelTorsorOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNorm

section
namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem torsorsTrivial_of_ringEquiv {B B' : Type} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (q : ℕ) (h : TorsorsTrivial B' q) : TorsorsTrivial B q := by
  intro D _ _ hfin hproj hff act hbij
  letI : Algebra B' B := e.symm.toRingHom.toAlgebra
  letI : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b) := by
    intro b
    change algebraMap B D b = algebraMap B D (e.symm (e b))
    rw [RingEquiv.symm_apply_apply]
  have hsmul : ∀ (b : B) (d : D), b • d = (e b) • d := by
    intro b d
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
  let eL : B ≃ₗ[B'] B' :=
    { e.toAddEquiv with
      map_smul' := fun b' b => by
        change e (e.symm b' * b) = b' * e b
        rw [map_mul, RingEquiv.apply_symm_apply] }
  haveI : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL
  haveI : Module.Finite B' B := Module.Finite.equiv eL.symm
  haveI : Module.FaithfullyFlat B D := hff
  haveI : Module.Finite B D := hfin
  have hfin' : Module.Finite B' D := Module.Finite.trans B D
  have hff' : Module.FaithfullyFlat B' D := Module.FaithfullyFlat.trans B' B D
  haveI i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  haveI i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let sl : D ≃ₛₗ[e.toRingHom] D :=
    { AddEquiv.refl D with
      map_smul' := fun b d => hsmul b d }
  haveI := hproj
  have hproj' : Module.Projective B' D := Module.Projective.of_equiv sl
  let act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D) :=
    { toFun := fun g => (act g).restrictScalars B'
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  haveI : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by
    rw [hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩
  let s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D :=
    TensorProduct.equivOfCompatibleSMul B B' B' D D
  have hcomp : ∀ x : TensorProduct B' D D,
      Algebra.TensorProduct.productMap
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B' D))
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun g => (act' g).toAlgHom)) x =
      Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) (s x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  obtain ⟨σ⟩ := h D hfin' hproj' hff' act' (by
    convert hbij.comp s.bijective using 1
    exact funext hcomp)
  refine ⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩
  change e.symm (σ (algebraMap B D b)) = b
  rw [hmap, σ.commutes]
  exact e.symm_apply_apply b

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

theorem nonempty_genFib_equiv {T T' O : Type} [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
    [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O] (M : Submonoid T)
    (hM : M ≤ nonZeroDivisors T) [IsLocalization M T'] :
    Nonempty (GenFib T O ≃+* GenFib T' O) := by
  haveI : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
  set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)
  set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')
  have h1 : M1 ≤ M2 := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩
    have hs' : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))
  have h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1 := by
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨algebraMap T O s, a, ?_, ?_⟩
    · have hy' : IsLocalization.mk' T' a s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      rintro rfl
      exact hy' (IsLocalization.mk'_zero s)
    · change algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)
      rw [IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization M2 (GenFib T O) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2
  exact ⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

open CategoryTheory in

theorem keyAll_of_keyLocal : KeyLocal → KeyAll := by
  intro hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2

  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])

  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']

  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have hqu' : IsUnit (q : T') := by
    simpa using hqu.map (algebraMap T T')
  have key := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'
  obtain ⟨eG⟩ := nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle
  exact torsorsTrivial_of_ringEquiv eG q key

end GlobalTheory.LocAcyc
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre : GlobalTheory.LocAcyc.KeyLocal → GlobalTheory.LocAcyc.KeyAll := by
  first | (exact @GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (exact GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (intros; apply GlobalTheory.LocAcyc.keyAll_of_keyLocal  <;> assumption)
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  first | (exact @GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (exact GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (intros; apply GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZModTorsorFiniteProjective_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D] [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  first | (exact @GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (exact GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (intros; apply GlobalTheory.LocAcyc.isZModTorsor_baseChange  <;> assumption)
end

section
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem exists_section_strictHenselisation_at_closed : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  intro hKey T E _ _ _ _ _ _ _ _ hT y _ hyT hyne q hq hqu DE _ _ actE htor
  obtain ⟨S, _, _, _, _, _, _, _, _, hmax, hflat, hloc, φ, hφ, hsh⟩ := GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt T E y
  have hKey' := hKey
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith at hKey'
  have htriv : GlobalTheory.LocAcyc.TorsorsTrivial (GlobalTheory.LocAcyc.GenFib T S) q :=
    hKey' T S hT (y.comap (algebraMap (Polynomial T) E)) φ hφ hsh hyT hyne q hq hqu
  have hMN : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors T)).comap (algebraMap E S) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hx
    exact Submonoid.mem_map.mpr ⟨t, ht, IsScalarTower.algebraMap_apply T E S t⟩
  let f : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T S :=
    IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S) hMN
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) := f.toAlgebra
  obtain ⟨act', -, htor'⟩ :=
    GlobalTheory.T.isZModTorsorFiniteProjective_baseChange (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) DE q hq actE htor
  obtain ⟨σ⟩ := (GlobalTheory.LocAcyc.torsorsTrivial_iff _ q).mp htriv _ act' htor'
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hmax, hflat, hloc, σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        DE →ₐ[GlobalTheory.LocAcyc.GenFib T E] GlobalTheory.LocAcyc.GenFib T S ⊗[GlobalTheory.LocAcyc.GenFib T E] DE).toRingHom,
    fun e => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  have hσ := σ.commutes (algebraMap (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S)
    (algebraMap E (GlobalTheory.LocAcyc.GenFib T E) e))
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hσ
  rw [hσ, RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq hMN e

end GlobalTheory.LocAcyc
end

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  atlas_forward_decl GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed
end

section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

private theorem spread_torsor : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := GlobalTheory.T.spread_torsor_to_etale_algebra
private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre
private theorem section_at_closedPt : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point
private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := GlobalTheory.T.exists_specialisation_to_strictlyHenselian

theorem keyGeneric_of_keyClosedPts : KeyClosedPts → KeyGeneric := by
  intro hC T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP hPeq q hq hqu
  rw [torsorsTrivial_iff]
  intro D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ := spread_torsor T O P φ hφ hSH.2.2.2 q hq D act hD

  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.comap_maximalIdeal (R := Polynomial T) (I := P)
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q (hQP.trans hPeq)
  haveI : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, hSy, hSflat, hSpieces, s, hs⟩ :=
    section_at_closedPt hC T E hAIC y hyT hyne q hq hqu DE actE hDE
  letI : Algebra E O := ψ.toRingHom.toAlgebra
  haveI : HenselianLocalRing O := hSH.1
  haveI : IsSepClosed (ResidueField O) := hSH.2.1
  obtain ⟨σ⟩ := specialisation_map E S O Q y hQy hSy rfl hSflat hSpieces
  have hσT : ∀ t : T, σ (algebraMap T S t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T E S, σ.commutes, IsScalarTower.algebraMap_apply T (Polynomial T) E]
    change ψ (algebraMap (Polynomial T) E _) = _
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap σ.toRingHom := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hσT t).symm⟩
  let m : GenFib T S →+* GenFib T O := IsLocalization.map (GenFib T O) σ.toRingHom hM
  refine hred (m.comp s) fun e => ?_
  rw [RingHom.comp_apply, hs e]
  simp only [m, IsLocalization.map_eq]
  change algebraMap O (GenFib T O) (σ (algebraMap E S e)) = _
  rw [σ.commutes]
  rfl

end GlobalTheory.LocAcyc
end
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyGeneric_of_keyClosedPts' : GlobalTheory.LocAcyc.KeyClosedPts → GlobalTheory.LocAcyc.KeyGeneric := by
  first | (exact @GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (exact GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (intros; apply GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts  <;> assumption)
end

section
open IsLocalRing Polynomial

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange : ∀ (B₁ B₂ D₁ : Type) [CommRing B₁] [CommRing B₂] [CommRing D₁] [Algebra B₁ B₂] [Algebra B₁ D₁]
    (q : ℕ), 0 < q → ∀ (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[B₁] D₁)),
    GlobalTheory.KeyOriginCut.IsZTorsor B₁ D₁ q act₁ →
    ∃ act₂ : Multiplicative (ZMod q) →* (TensorProduct B₁ B₂ D₁ ≃ₐ[B₂] TensorProduct B₁ B₂ D₁),
      GlobalTheory.KeyOriginCut.IsZTorsor B₂ (TensorProduct B₁ B₂ D₁) q act₂ := by
  intro B₁ B₂ D₁ _ _ _ _ _ q hq act₁ h
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  let act₂ : Multiplicative (ZMod q) →* (B₂ ⊗[B₁] D₁ ≃ₐ[B₂] B₂ ⊗[B₁] D₁) :=
    { toFun := fun g => Algebra.TensorProduct.congr AlgEquiv.refl (act₁ g)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      map_mul' := by
        intro g h
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy] }
  refine ⟨act₂, inferInstance, inferInstance, inferInstance, ?_⟩
  let e₀ := LinearEquiv.ofBijective (Algebra.TensorProduct.productMap
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun _ => AlgHom.id B₁ D₁))
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun g => (act₁ g).toAlgHom))).toLinearMap hbij
  have key : ∀ z : B₂ ⊗[B₁] (D₁ ⊗[B₁] D₁),
      Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))
        (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁ z) =
      TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)
        (LinearEquiv.baseChange B₁ B₂ _ _ e₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add] at hx hy ⊢; rw [hx, hy]
      | tmul x y =>
        funext g
        simp [act₂, e₀, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.piRight_apply,
          Algebra.TensorProduct.congr_apply]
        congr 1
  have hfun : ⇑(Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))) =
      ⇑(TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)) ∘
        ⇑(LinearEquiv.baseChange B₁ B₂ _ _ e₀) ∘
        ⇑(TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [← key, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (TensorProduct.piRight B₁ B₂ B₂ _).bijective.comp
    ((LinearEquiv.baseChange B₁ B₂ _ _ e₀).bijective.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm.bijective)

theorem exists_stage_torsor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq q hq hqu D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ :=
    GlobalTheory.T.spread_torsor_to_etale_algebra T O P φ hφ hSH.2.2.2 q hq D act hD
  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.comap_maximalIdeal (R := Polynomial T) (I := P)

  have hunit : ∀ y : Q.primeCompl, IsUnit (ψ.toRingHom (y : E)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : E) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap E (Localization.AtPrime Q)) = ψ.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) E (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact ψ.comp_algebraMap
  have hjT : ∀ t : T, j (algebraMap T (Localization.AtPrime Q) t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply T (Polynomial T) O, ← RingHom.comp_apply, hjR]
  have hM : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap j := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hjT t).symm⟩
  let ψ' : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.map (GlobalTheory.LocAcyc.GenFib T O) j hM
  have hψ' : ψ'.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j := IsLocalization.map_comp hM

  have hM' : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)).comap
        (algebraMap E (Localization.AtPrime Q)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q) t).symm⟩
  let m : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) :=
    IsLocalization.map _ (algebraMap E (Localization.AtPrime Q)) hM'
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := m.toAlgebra
  obtain ⟨act₂, h₂⟩ := torsor_baseChange (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) DE q hq actE hDE
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, ψ', hψ', _, inferInstance, inferInstance, act₂, h₂, ?_⟩
  intro σ hσ
  refine hred (σ.comp (Algebra.TensorProduct.includeRight (R := GlobalTheory.LocAcyc.GenFib T E)
    (A := GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (B := DE)).toRingHom) fun e => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)), ← RingHom.comp_apply σ, hσ]
  change ψ' (m (algebraMap E _ e)) = _
  simp only [m, IsLocalization.map_eq]
  rw [← RingHom.comp_apply ψ', hψ', RingHom.comp_apply, ← RingHom.comp_apply j, hjE]
  rfl

end GlobalTheory.KeyOriginCut
end
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_henselisation_prime_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_torsor) | (exact GlobalTheory.KeyOriginCut.exists_stage_torsor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_torsor  <;> assumption)
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  first | (exact @GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (exact GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (intros; apply GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType  <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginCut

theorem keyOrigin : GlobalTheory.LocAcyc.KeyOrigin := by
  have h₁ := GlobalTheory.T.strict_henselisation_prime_eq
  have h₂ := GlobalTheory.T.exists_noetherian_model_torsor_origin
  have h₃ := GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith GlobalTheory.LocAcyc.TorsorsTrivial
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hS q hq hqu D _ _ hfin hproj hff act hbij
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, ψ, hψ, D₁, _, _, act₁, htors₁, hpull₁⟩ :=
    h₁ T O hT P φ hφ hsh hS q hq hqu D act ⟨hfin, hproj, hff, hbij⟩
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, hqA, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, ψA, hψA,
    DA, _, _, actA, htorsA, hpullA⟩ := h₂ T O hT q hq hqu E Q hQ j hj ψ hψ D₁ act₁ htors₁
  obtain ⟨σ, hσ⟩ :=
    h₃ T O hT P φ hφ hsh hS q hq hqu A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htorsA
  obtain ⟨σ₁, hσ₁⟩ := hpullA σ hσ
  exact hpull₁ σ₁ hσ₁

end GlobalTheory.KeyOriginCut
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_trivial_strict_henselisation_origin : GlobalTheory.LocAcyc.KeyOrigin := by
  first | (exact @GlobalTheory.KeyOriginCut.keyOrigin) | (exact GlobalTheory.KeyOriginCut.keyOrigin) | (intros; apply GlobalTheory.KeyOriginCut.keyOrigin  <;> assumption)
end

section
open scoped TensorProduct
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem keyLocal_of (h1 : KeyClosedPts) (h2 : KeyGeneric) : KeyLocal := by
  intro T O _ _ _ _ _ _ _ _ hA P _ φ hφ hsh hP _ q hq hu
  by_cases h : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h2 T O hA P φ hφ hsh hP h q hq hu
  · exact h1 T O hA P φ hφ hsh hP h q hq hu

theorem torsor_trivial : ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D],
    Module.Finite (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.Projective (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.FaithfullyFlat (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D))
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) := by
  intro T O _ _ _ _ _ _ _ hA P _ φ hφ hsh q hq hu D _ _ hfin hproj hff act hbij
  have hO : KeyOrigin := GlobalTheory.T.torsor_trivial_strict_henselisation_origin
  have hAll : KeyAll :=
    GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre (keyLocal_of (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO) (GlobalTheory.T.keyGeneric_of_keyClosedPts' (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO)))
  exact hAll T O hA P φ hφ hsh q hq hu D hfin hproj hff act hbij

end GlobalTheory.LocAcyc
end

section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
end
