import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedBaseChangeLatticeCountEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetInvAlgBaseChangeUnramifiedOdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCharpolyInvAlgBaseChangeUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValResultantEqDegreeMulUnramifiedExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch

section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
end

section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_residually_unipotent_via_cayley : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | exact GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | (intros; apply GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent <;> assumption)
end

section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_adjoin_unitary_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have key : (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) * (y₁ - y₂) = 0 := by
    rw [Commute.geom_sum₂_mul (Commute.all _ _), h₁, h₂, sub_self]
  have hr : residue S (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) =
      (n : ResidueField S) * residue S y₂ ^ (n - 1) := by
    rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [Finset.sum_congr rfl (g := fun _ => residue S y₂ ^ (n - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  have hu : IsUnit (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hr]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · simpa using (hn.map (residue S)).ne_zero
    · intro h0
      have := congrArg (residue S) h₂
      rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
  have := (hu.mul_right_eq_zero).1 key
  exact sub_eq_zero.1 this

theorem card_sub_one_isUnit (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp

theorem exists_unr_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K _ B hu _ hi hl d hcard K' φ hU hz
  obtain ⟨z, hzp, hzadj⟩ := hz
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR
  have hq0 : K.q ≠ 0 := by
    intro h0
    have : 0 < Nat.card (ResidueField K.O) := Nat.card_pos
    rw [K.card_res, h0] at this
    simp at this
  have hq' : K'.q = K.q ^ d := hU.1
  set N := K'.q ^ 2 - 1 with hNdef
  have hcardR : Nat.card (ResidueField R) = K'.q ^ 2 := by rw [hcard, hq', ← pow_mul, mul_comm]
  have hd : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq'
    rw [hq', one_pow] at hcardR
    have : Subsingleton (ResidueField R) := (Nat.card_eq_one_iff_unique.1 hcardR).1
    exact not_subsingleton (ResidueField R) this
  haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))

  haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R
  have h1q : 1 < K'.q ^ 2 := by rw [← K'.card_res]; exact Finite.one_lt_card
  have hN : N ≠ 0 := by omega
  have hNR : IsUnit (N : R) := by
    have := card_sub_one_isUnit R
    rwa [hcardR] at this
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2
    (φ.injective.comp (IsFractionRing.injective K.O K.E))
  have hzN : z ^ N = 1 := hzp.pow_eq_one
  have hzint : IsIntegral K.O z :=
    ⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hmdvd : minpoly K.O z ∣ X ^ N - C 1 := minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])
  obtain ⟨yR, hyR⟩ := GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one R ((minpoly K.O z).map (algebraMap K.O R))
    ((minpoly.monic hzint).map _)
    (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne')
    (by
      rw [hcardR]
      have := Polynomial.map_dvd (algebraMap K.O R) hmdvd
      simpa using this)
  have hyN : yR ^ N = 1 := by
    obtain ⟨h, hh⟩ := hmdvd
    have := congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh
    simp only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this
    simpa [sub_eq_zero] using this

  have hzE : IsIntegral K.E z := hzint.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzE hzadj
  have hgen : pb.gen = z := rfl
  have hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0 := by
    rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap,
      ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]
    rfl
  let ψ : K'.E →+* B.A := (pb.lift (yR : B.A) hy).toRingHom
  have hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e := fun e => (pb.lift (yR : B.A) hy).commutes e
  have hψz : ψ z = yR := pb.lift_gen _ hy
  haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)
  have hψi : Function.Injective ψ := ψ.injective

  let τR : R →+* R := (B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx
  have hτR : ∀ x : R, (τR x : B.A) = B.σ x := fun x => rfl
  have hτ2 : ∀ x, τR (τR x) = x := fun x => Subtype.ext (B.σ_σ x)
  obtain ⟨a, b, hab, hres⟩ := K.c_res
  have hτa : τR (algebraMap K.O R a) = algebraMap K.O R b := by
    apply Subtype.ext
    rw [hτR]
    change B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]
  have hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a) := by
    rw [hτa]
    intro h
    have h2 : residue R (algebraMap K.O R (a - b)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    have hu' : IsUnit (a - b) := by
      by_contra hc
      exact hres ((IsLocalRing.mem_maximalIdeal _).2 hc)
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)
  obtain ⟨hfr1, hfr2⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity R K'.q hcardR τR hτ2 ⟨_, hne⟩
  choose τ' hτ' using K'.c_int
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let cO : K'.O →+* K'.O :=
    { toFun := τ'
      map_one' := hinj' (by rw [← hτ']; simp)
      map_mul' := fun a b => hinj' (by simp [← hτ'])
      map_zero' := hinj' (by rw [← hτ']; simp)
      map_add' := fun a b => hinj' (by simp [← hτ']) }
  have hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x) := fun x => (hτ' x).symm
  have hc2 : ∀ x, cO (cO x) = x := fun x => hinj' (by rw [hcO, hcO, K'.c_c])
  obtain ⟨a', b', hab', hres'⟩ := K'.c_res
  have hne' : residue K'.O (cO a') ≠ residue K'.O a' := by
    have : cO a' = b' := hinj' (by rw [hcO, hab'])
    rw [this]
    intro h
    apply hres'
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨-, hfc⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩
  obtain ⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z :=
    IsIntegrallyClosed.isIntegral_iff.1
      ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hzON : zO ^ N = 1 := hinj' (by rw [map_pow, hzO, hzN, map_one])
  have hcz : K'.c z = z ^ K'.q := by
    rw [← hzO, ← hcO, hfc zO hzON, map_pow]
  have hσz : B.σ (ψ z) = ψ (K'.c z) := by
    rw [hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]
    rfl
  have hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e) := by
    intro e
    have he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} := hzadj ▸ Algebra.mem_top
    induction he using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hσz
    | algebraMap e =>
      change B.σ (ψ (φ e)) = ψ (K'.c (φ e))
      rw [← hU.2.1, hψ, hψ, B.σ_alg]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

  have hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R := by
    intro y
    have hadj := GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic K K' d φ hU hd z hzp hzadj _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hd y)
    generalize algebraMap K'.O K'.E y = x at hadj ⊢
    induction hadj using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]; exact yR.2
    | algebraMap a =>
      change ψ (φ (algebraMap K.O K.E a)) ∈ R
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨ψ, hψ, hσ, hO, ?_⟩
  haveI : NeZero N := ⟨hN⟩
  have hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n) := fun n => by rw [map_pow, hψz]; rfl
  have hwp : IsPrimitiveRoot (residue R yR) N := by
    refine ⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩
    have h1 : yR ^ l = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])
    apply hψi
    rw [← hcoe, h1, map_one]
    rfl
  set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR
  have hgu : gR * τR gR = 1 := Subtype.ext hu
  have hg0 : residue R gR ≠ 0 := (IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero
  have hgN : residue R gR ^ N = 1 := by
    haveI := Fintype.ofFinite (ResidueField R)
    have := FiniteField.pow_card_sub_one_eq_one _ hg0
    rwa [← Nat.card_eq_fintype_card, hcardR] at this
  obtain ⟨j, -, hj⟩ := hwp.eq_pow_of_pow_eq_one hgN
  let zOu : K'.Oˣ := Units.ofPowEqOne zO N hzON hN
  have hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j := by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]
  refine ⟨zOu ^ j, ?_, ?_⟩
  · set e := j + j * K'.q with he
    have hres : residue R (yR ^ e) = 1 := by
      rw [map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]
    have hye : yR ^ e = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])
    rw [hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]
    apply hψi
    rw [← hcoe, hye, map_one]
    rfl
  · have : (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j :=
      Subtype.ext (by
        change ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)
        rw [hs, hcoe])
    rw [this, map_pow, hj]

end GlobalTheory.UnitLemma.Unr
end
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_involution_field_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  atlas_forward_decl GlobalTheory.UnitLemma.Unr.exists_unr_embedding
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := GlobalTheory.T.card_residueField_adjoin_unitary_prod K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := GlobalTheory.T.exists_unramified_involution_field_embedding K hK (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.charpoly_overExt_integral_reduction_pow K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := GlobalTheory.T.unitLemma_residually_unipotent_via_cayley hL K' (hodd hK) C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.Unr
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  atlas_forward_decl GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem IsIso.stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem IsIso.kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem IsIso.identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [h₁.kapSum_eq h₂, h₁.stSum_eq, h₂.stSum_eq, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (cut B e he).A +
      Module.finrank K.E (cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (cut B e he).P * (cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  rcases subsingleton_or_nontrivial B.A with hs | hs
  · exact Or.inl ⟨0, zero_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hid : ∀ e : Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → e = 0 ∨ e = 1
  · have : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
      Module.Finite.iff_fg.2 hi.fg_adjoin_singleton
    exact Or.inr (isLocalRing_of_idem (R := K.O) _ hid)
  push Not at hid
  obtain ⟨⟨e, he⟩, hee, h0, h1⟩ := hid
  have hee : e * e = e := congrArg Subtype.val hee
  have h0 : e ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : e ≠ 1 := fun h => h1 (Subtype.ext h)
  have he' := adjoin_stable B hu hi he
  have hee' : B.σ e * B.σ e = B.σ e := by rw [← map_mul, hee]
  have hm : e * B.σ e = 0 := by
    refine (h _ (mul_mem he he') ?_ ?_).resolve_right fun h2 => h1 ?_
    · linear_combination B.σ e * B.σ e * hee + e * hee'
    · rw [map_mul, B.σ_σ, mul_comm]
    · linear_combination (1 - e) * h2 + B.σ e * hee
  refine Or.inl ⟨e, he, hee, (h _ (add_mem he he') ?_ ?_).resolve_left fun h2 => h0 ?_⟩
  · linear_combination hee + hee' + 2 * hm
  · rw [map_add, B.σ_σ, add_comm]
  · linear_combination e * h2 - hee - hm

theorem identity_integral (hL : UnitLemmaLie) (hK : K.Odd) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact GlobalTheory.T.involutive_algebra_product_identity K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra hL K hK B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (cut B₁ e₁ s₁).A + Module.finrank K.E (cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine (isIso_cut B₁ j₁ s₁).identity (isIso_cut B₂ j₂ s₂) ?_
  refine GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem unitLemmaGroup_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  intro hL K hK B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL hK _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.Orbit
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  atlas_forward_decl GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie
end

section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  first | exact @GlobalTheory.UnitLemma.lattice_sandwich | exact GlobalTheory.UnitLemma.lattice_sandwich | (intros; apply GlobalTheory.UnitLemma.lattice_sandwich <;> assumption)
end

section
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.TorusOrbitLat

section General

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl

theorem mem_intUnits_iff (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl

theorem mem_mulLat_unit (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_eq_iff (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]

theorem isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h

end General

section Main

variable {K : UQ} (B : InvAlg K)

theorem rho_cond_mk (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w

theorem orbit_count : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)

end Main

end GlobalTheory.TorusOrbitLat
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  atlas_forward_decl GlobalTheory.TorusOrbitLat.orbit_count
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

theorem torusOrb_mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hz
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

theorem torusOrb_mulLat_mem_X (x : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (L : Submodule K.O B.A) (hL : L ∈ B.X x) :
    mulLat K.O (t : B.A) L ∈ B.X x := by
  obtain ⟨⟨hfg, hsp⟩, hg, hsd⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro a _
    have hmem : ((t⁻¹ : B.Aˣ) : B.A) * a ∈ Submodule.span K.E (L : Set B.A) := by rw [hsp]; trivial
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.mulLeft K.E (t : B.A)) hmem
    rw [Submodule.map_span] at h2
    have h3 : (LinearMap.mulLeft K.E (t : B.A)) ((((t⁻¹ : B.Aˣ) : B.A) * a)) = a := by
      simp [LinearMap.mulLeft_apply, ← mul_assoc]
    rw [h3] at h2
    have e : ((mulLat K.O (t : B.A) L : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (t : B.A)) '' (L : Set B.A) := by
      show ((L.map (LinearMap.mulLeft K.O (t : B.A)) : Submodule K.O B.A) : Set B.A) = _
      rw [Submodule.map_coe]
      rfl
    rw [e]
    exact h2
  · intro y hy
    rw [torusOrb_mem_mulLat_unit] at hy ⊢
    rw [mul_left_comm]
    exact hg _ hy
  · intro y
    rw [torusOrb_mem_mulLat_unit, hsd]
    constructor
    · intro h z hz
      rw [torusOrb_mem_mulLat_unit] at hz
      have := h _ hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht] at this
      simpa [← mul_assoc] using this
    · intro h z hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]
      apply h
      rw [torusOrb_mem_mulLat_unit]
      simpa [← mul_assoc] using hz

def torusOrbRel (x : B.A) (L M : B.X x) : Prop :=
  ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)

theorem torusOrb_orbRel_equivalence (x : B.A) : Equivalence (B.torusOrbRel x) where
  refl L := ⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩
  symm := by
    rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
    rw [h, torusOrb_mulLat_inv]
  trans := by
    rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩
    rw [h2, h1, torusOrb_mulLat_mul]

theorem torusOrb_orb_mk_eq (x : B.A) {L M : B.X x}
    (h : (Quot.mk (B.torusOrbRel x) L : Orb K.O B.T (B.X x)) = Quot.mk (B.torusOrbRel x) M) : B.torusOrbRel x L M :=
  (Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)

def torusOrb_orbSplit (x w : B.A) : {L : B.X x // w ∈ (L : Submodule K.O B.A)} ≃
    Σ o : Orb K.O B.T (B.X x), {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} where
  toFun L := ⟨(Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x)), L.1.1,
    B.torusOrb_orb_mk_eq x (Quot.out_eq (Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x))), L.2⟩
  invFun p := ⟨⟨p.2.1, by
      obtain ⟨t, ht, h⟩ := p.2.2.1
      rw [h]
      exact B.torusOrb_mulLat_mem_X x t ht _ (Quot.out p.1).2⟩, p.2.2.2⟩
  left_inv L := rfl
  right_inv p := by
    obtain ⟨o, M, h⟩ := p
    refine Sigma.subtype_ext ?_ rfl
    dsimp only
    conv_rhs => rw [← Quot.out_eq o]
    symm
    apply Quot.sound
    exact h.1

theorem torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  unfold UU
  rw [Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]

end InvAlg

theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.UU_eq_sum_over_torus_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) → (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) → B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  atlas_forward_decl GlobalTheory.UnitLemma.UU_eq_sum_orbits
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  atlas_forward_decl GlobalTheory.UnitLemma.rho_pow_eq_card_box
end

section
section
open Filter

namespace GlobalTheory

theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finset_prod (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory
end

open Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_ratio_box_counts_prod_one : ∀ (r : ℕ) (c : Fin r → ℕ) (m : ℕ), Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) / ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  atlas_forward_decl GlobalTheory.ratio_box_counts_tendsto_one
end

section
section
open GlobalTheory.UnitLemma Polynomial Filter Topology

namespace GlobalTheory.UnitLemma

theorem unitaryLimit : UnitaryLimit := by
  have L0 := GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
  have S1 := GlobalTheory.T.fullLattice_sandwich_between_integral_elements
  have S2 := GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
  have S3 := GlobalTheory.T.UU_eq_sum_over_torus_orbits
  have S4 := GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
  have S5 := GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box
  have S6 := GlobalTheory.T.tendsto_ratio_box_counts_prod_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  atlas_forward_decl GlobalTheory.UnitLemma.unitaryLimit
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_lie_and_group (hM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) :
    UnitLemmaLie ∧ UnitLemmaGroup :=
  have hL : UnitLemmaLie := GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent (GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch hM) GlobalTheory.T.unitary_lattice_count_ratio_tendsto GlobalTheory.T.linearLatticeCountDescent_proof
  ⟨hL, GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie hL⟩

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  atlas_forward_decl GlobalTheory.UnitLemma.unitLemma_lie_and_group
end
