import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  atlas_forward_decl GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_surjective_valuation_isIntegral_iff (K : UQ) (L : Type) [Field L] [Algebra K.E L]
    [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L] :
    ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧
      ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  haveI hdvr := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure K.O K.E L
  haveI hfr := integralClosure.isFractionRing_of_finite_extension (A := K.O) K.E L
  set R := integralClosure K.O L
  let P := IsDiscreteValuationRing.maximalIdeal R
  let u : Lˣ →* Multiplicative ℤ := WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (P.valuation L).toMonoidWithZeroHom.toMonoidHom)
  have hu : ∀ x : Lˣ, ((u x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = P.valuation L x := by
    intro x
    simp [u, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  have key : ∀ x : L, x ≠ 0 → (IsIntegral K.O x ↔ P.valuation L x ≤ 1) := by
    intro x hx
    rw [← mem_integralClosure_iff]
    constructor
    · intro h
      have : x = algebraMap R L ⟨x, h⟩ := rfl
      rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro h
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [← hr]; exact r.2
      · by_cases hrm : r ∈ IsLocalRing.maximalIdeal R
        · exfalso
          have h1 : P.valuation L (algebraMap R L r) < 1 :=
            (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P r).2 hrm
          rw [hr] at h1
          have h2 : P.valuation L x * P.valuation L x⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hx, map_one]
          have h3 : P.valuation L x * P.valuation L x⁻¹ < 1 :=
            lt_of_le_of_lt (mul_le_of_le_one_left' h) h1
          exact (ne_of_lt h3) h2
        · have hru : IsUnit r := by
            by_contra hh; exact hrm ((IsLocalRing.mem_maximalIdeal r).2 hh)
          obtain ⟨s, hs⟩ := hru
          have : x = algebraMap R L (s⁻¹ : Rˣ) := by
            have e1 : algebraMap R L (s : R) * algebraMap R L ((s⁻¹ : Rˣ) : R) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            rw [hs, hr] at e1
            exact (inv_mul_eq_one₀ hx).1 e1
          rw [this]; exact ((s⁻¹ : Rˣ) : R).2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R L π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R L) _ h)
  let πL : Lˣ := Units.mk0 _ hπ0
  have huπ : u πL = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hu]
    change P.valuation L (algebraMap R L π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton P hπ.ne_zero hπ.maximalIdeal_eq]
    rfl
  refine ⟨u⁻¹, ?_, ?_⟩
  · intro n
    refine ⟨πL ^ (Multiplicative.toAdd n), ?_⟩
    rw [map_zpow, MonoidHom.inv_apply, huπ, ← ofAdd_neg, neg_neg, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  · intro x
    rw [key _ x.ne_zero, ← hu, MonoidHom.inv_apply, toAdd_inv, neg_nonneg, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  atlas_forward_decl GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isIntegral_iff_forall_maximalSpectrum (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  constructor
  · intro h m
    have := h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this
  · intro h
    letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
    choose p hpm hp using fun m : MaximalSpectrum B.A => h m
    refine ⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩
    have hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal := by
      intro m
      rw [eval₂_finset_prod]
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      apply Ideal.mul_mem_right
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 := hp m
      have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)
      rw [Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1] at h2
      rw [← aeval_def]
      exact h2.symm
    set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)
    have hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A) := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)
    have hz : z ^ k = 0 := by
      have := Ideal.pow_mem_pow hj k
      rw [hk] at this
      simpa using this
    exact IsReduced.eq_zero z ⟨k, hz⟩

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ x : B.A, IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  atlas_forward_decl GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory

theorem UnitLemma.exists_unit_residue (K : UQ) (B : InvAlg K) (hB : IsReduced B.A) (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal) (hz : z ≠ 0) :
    ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  classical
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  let e := IsArtinianRing.equivPi B.A
  let v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal := fun I =>
    if h : I = m then h ▸ z else 1
  have hv : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro I
    letI := Ideal.Quotient.field I.asIdeal
    rw [isUnit_iff_ne_zero]
    by_cases h : I = m
    · subst h; simpa [v] using hz
    · simp [v, h]
  have hy : IsUnit (e.symm v) := hv.map e.symm
  refine ⟨hy.unit, ?_, ?_⟩
  · have := IsArtinianRing.equivPi_apply B.A (e.symm v) m
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v]
  · intro m' hm'
    have := IsArtinianRing.equivPi_apply B.A (e.symm v) m'
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v, hm']

theorem UnitLemma.unit_prescribed_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz

end GlobalTheory
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A) (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧ ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  atlas_forward_decl GlobalTheory.UnitLemma.unit_prescribed_residue
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.SwapInt

theorem isIntegral_map_semilinear {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]

noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add, map_add, map_add,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]

theorem conjO_spec (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

theorem sigma_algebraMap {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]

end GlobalTheory.UnitLemma.SwapInt

open GlobalTheory.UnitLemma.SwapInt in

theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_residue_comap_involution_iff : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  atlas_forward_decl GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NotIntegral

theorem inv_small_not_integral : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  intro K B a ha m hint
  obtain ⟨ha0, hmax, -⟩ := ha
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let f : K.E →ₐ[K.O] (B.A ⧸ m.asIdeal) := IsScalarTower.toAlgHom K.O K.E (B.A ⧸ m.asIdeal)
  have hf : Function.Injective f := (algebraMap K.E (B.A ⧸ m.asIdeal)).injective
  have hE : IsIntegral K.O (algebraMap K.O K.E a)⁻¹ := (isIntegral_algHom_iff f hf).1 hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hE
  have hne : algebraMap K.O K.E a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]; exact ha0
  have hab : a * b = 1 := by
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  exact (IsLocalRing.mem_maximalIdeal a).1 hmax ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

end GlobalTheory.NotIntegral
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isIntegral_residue_inv_small_integer : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  atlas_forward_decl GlobalTheory.NotIntegral.inv_small_not_integral
end

section
namespace GlobalTheory

theorem involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩

end GlobalTheory

alias _root_.GlobalTheory.T.exists_representatives_two_element_orbits_involution := _root_.GlobalTheory.involution_pair_representatives
end

section
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem valsAt_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective ((valsAt w e).comp T.subtype) := by
  intro G _ τ hττ T hT ι s w hsw hex r e he hs n
  choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)
  have hτ : ∀ i j, w (e i) (τ (y j)) = 1 := by
    intro i j
    have h1 : w (s (e i)) (y j) = 1 := hy2 j _ (hs i j)
    have a := (hsw (e i) (y j)).1 (by rw [h1]; simp)
    have b := (hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)
    rw [map_inv, map_inv, toAdd_inv] at b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    omega
  have hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T := by
    intro j
    rw [hT, map_mul, map_inv, hττ]
    group
  refine ⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  apply Multiplicative.toAdd.injective
  funext i
  rw [valsAt_apply, map_prod, toAdd_prod]
  have hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0 := by
    intro j
    rw [map_mul, map_inv, hτ, inv_one, mul_one]
    split_ifs with hij
    · subst hij; rw [hy1]; rfl
    · rw [hy2 j (e i) fun h => hij (he _ _ h)]; rfl
  simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective ((valsAt w e).comp T.subtype) := by
  atlas_forward_decl GlobalTheory.UnitLemma.valsAt_torus_surjective
end

section
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusKer

theorem valsAt_torus_eq_one_iff (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  have hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x) := by
    intro i x; rw [map_inv, toAdd_inv]
  have hτ : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT t).1 t.2)
  have hτ' : τ ((t : G)⁻¹) = (t : G) := by rw [map_inv, hτ, inv_inv]
  constructor
  · intro h
    have he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0 := by
      intro j
      have := congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h
      simpa [valsAt_apply] using this
    intro i
    rcases hcov i with hi | ⟨j, hj | hj⟩
    · have h1 := hs i (t : G)
      rw [hi, hτ, hinv] at h1
      omega
    · subst hj; exact he j
    · subst hj
      have h1 := hs (e j) (t : G)
      have h2 := hs (e j) ((t : G)⁻¹)
      rw [hτ, hinv, he j] at h1
      rw [hτ', he j, hinv] at h2
      omega
  · intro h
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [valsAt_apply, h]
    rfl

end GlobalTheory.TorusKer
end

open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ t : T, (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  atlas_forward_decl GlobalTheory.TorusKer.valsAt_torus_eq_one_iff
end

section
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusInteg

theorem torus_integral_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  intro G _ τ T hT ι s w hs r e hcov α hα hpos t k
  have hτt : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT _).1 t.2)
  have val1 : ∀ i, Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))
      = - Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    simp [map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow, nsmul_eq_mul]
  have val2 : ∀ i, Multiplicative.toAdd (w i (τ ((t : G)⁻¹ * α ^ k)))
      = Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    rw [map_mul, map_inv, map_pow, hτt, hα, inv_inv]
    simp [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
  have rhs : ∀ j, ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ)
      = k * Multiplicative.toAdd (w (e j) α) := by
    intro j
    push_cast
    rw [Int.toNat_of_nonneg (hpos _).le]
  have lhs : ∀ j, Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j
      = Multiplicative.toAdd (w (e j) t) := fun j => rfl
  constructor
  · intro h j
    rw [lhs, rhs, abs_le]
    have h1 := h (e j)
    have h2 := (hs (e j) _).1 (h (s (e j)))
    rw [val1] at h1
    rw [val2] at h2
    constructor <;> linarith
  · intro h i
    rcases hcov i with hi | ⟨j, rfl | rfl⟩
    · have hz : Multiplicative.toAdd (w i t) = 0 := by
        have := hs i (t : G)
        rw [hi, hτt, map_inv, toAdd_inv] at this
        rcases lt_trichotomy (Multiplicative.toAdd (w i t)) 0 with h' | h' | h'
        · exact absurd (this.2 (by linarith)) (not_le.2 h')
        · exact h'
        · exact absurd (this.1 h'.le) (not_le.2 (by linarith))
      rw [val1, hz]
      have := (hpos i).le
      positivity
    · have := h j
      rw [lhs, rhs, abs_le] at this
      rw [val1]; linarith [this.1]
    · have := h j
      rw [lhs, rhs, abs_le] at this
      apply (hs (e j) _).2
      rw [val2]; linarith [this.1]

end GlobalTheory.TorusInteg
end

open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  atlas_forward_decl GlobalTheory.TorusInteg.torus_integral_iff
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := GlobalTheory.T.isReduced_of_lieReg' K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs
  refine ⟨r, (valsAt w e).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  atlas_forward_decl GlobalTheory.UnitLemma.torus_mod_intUnits_structure
end
