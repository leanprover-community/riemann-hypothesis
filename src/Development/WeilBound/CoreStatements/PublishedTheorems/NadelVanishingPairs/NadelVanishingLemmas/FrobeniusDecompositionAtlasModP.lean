import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldCoordinatesDlog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfMonomialQuotientIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateQuotientRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularQuotientPrimeElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssociatedOfHeightOneAgree
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChart
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormsDifferentialClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerContractionChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsEqChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModPSquaredStalkSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesStalkFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModPSquaredTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusLiftStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartEquationsDifferUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftUnitTimesCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftPpZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftOfUnitMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtUnit

theorem unit_mul_monomial_of_forall_height_one (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (x : K) (hx : x ≠ 0)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ x * algebraMap R K d = algebraMap R K c) :
    ∃ (u : Rˣ) (m : Fin n → ℤ), x = algebraMap R K u * ∏ j ∈ J, (algebraMap R K (π j)) ^ m j := by
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0' : b0 ≠ 0 := nonZeroDivisors.ne_zero hb0
  have hb0K : algebraMap R K b0 ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0'
  have ha0 : a0 ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨α, a, ha, hna⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J a0 ha0
  obtain ⟨β, b, hb, hnb⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J b0 hb0'
  have hπ0 : ∀ j ∈ J, π j ≠ 0 := fun j hj =>
    (hπ j hj).elim (fun hu => hu.ne_zero) (fun hp => hp.ne_zero)
  have han : a ≠ 0 := by rintro rfl; rw [zero_mul] at ha; exact ha0 ha
  have hbn : b ≠ 0 := by rintro rfl; rw [zero_mul] at hb; exact hb0' hb
  have hprodQ : ∀ (Q : Ideal R), Q.IsPrime → (∀ j ∈ J, π j ∉ Q) →
      ∀ e : Fin n → ℕ, ∏ j ∈ J, π j ^ e j ∉ Q := by
    intro Q hQ hQJ e hmem
    obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.associated_of_height_one_agree R π J a b han hbn hπ
    (fun j hj hp => ⟨hna j hj hp, hnb j hj hp⟩) (fun Q hQ h1 hQJ => by
      obtain ⟨c, d, hc, hd, hcd⟩ := h Q hQ h1 hQJ
      refine ⟨c * ∏ j ∈ J, π j ^ β j, d * ∏ j ∈ J, π j ^ α j,
        hQ.mul_notMem hc (hprodQ Q hQ hQJ β), hQ.mul_notMem hd (hprodQ Q hQ hQJ α), ?_⟩
      have e1 : algebraMap R K a0 * algebraMap R K d = algebraMap R K b0 * algebraMap R K c := by
        rw [← hcd]; field_simp
      have e2 : a0 * d = b0 * c := IsFractionRing.injective R K (by rw [map_mul, map_mul, e1])
      rw [ha, hb] at e2
      linear_combination e2)
  refine ⟨u, fun j => (α j : ℤ) - β j, ?_⟩
  have hK : ∀ j ∈ J, algebraMap R K (π j) ≠ 0 := fun j hj => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ0 j hj
  have hprodK : ∏ j ∈ J, algebraMap R K (π j) ^ ((α j : ℤ) - β j) =
      (∏ j ∈ J, algebraMap R K (π j) ^ α j) / ∏ j ∈ J, algebraMap R K (π j) ^ β j := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [zpow_sub₀ (hK j hj), zpow_natCast, zpow_natCast]
  have hβK : ∏ j ∈ J, algebraMap R K (π j) ^ β j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hK j hj)
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hbn
  rw [hprodK, ha, hb, hu]
  simp only [map_mul, map_prod, map_pow]
  field_simp

theorem unit_mul_monomial_iff : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  intro p _ A _ _ _ n t het P _ L _ _ _ J ht g
  constructor
  · intro hL
    letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A :=
      (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := het
    haveI : IsRegularRing A := GlobalTheory.isRegularRing_of_etale (MvPolynomial (Fin n) (ZMod p)) A
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      IsRegularRing.isRegularLocalRing_localization P
    obtain ⟨hRd, hRi⟩ :=
      GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime P)
    haveI : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      rintro h0
      exact y.2 (h0 ▸ P.zero_mem)
    letI : Algebra (Localization.AtPrime P) L := (IsLocalization.lift hunits).toAlgebra
    haveI : IsScalarTower A (Localization.AtPrime P) L :=
      IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunits a).symm)
    haveI : IsFractionRing (Localization.AtPrime P) L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ L
    have hprime : ∀ j ∈ J, IsUnit (algebraMap A (Localization.AtPrime P) (t j)) ∨
        Prime (algebraMap A (Localization.AtPrime P) (t j)) := by
      intro j hj
      by_cases hjP : t j ∈ P
      · right
        refine GlobalTheory.T.regular_quotient_prime_element A P (t j) (fun h0 => ht j (by rw [h0, map_zero])) hjP
          (GlobalTheory.T.etale_coordinate_quotient_regular p A t het j)
      · left
        exact IsLocalization.map_units (Localization.AtPrime P) (⟨t j, hjP⟩ : P.primeCompl)
    obtain ⟨u, m, hum⟩ := unit_mul_monomial_of_forall_height_one (Localization.AtPrime P) L
      (fun j => algebraMap A (Localization.AtPrime P) (t j)) J hprime (g : L) g.ne_zero (by
        intro Q hQ _ hQJ
        have hQ'P : Q.comap (algebraMap A (Localization.AtPrime P)) ≤ P := by
          intro x hx
          by_contra hxP
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl)))
        obtain ⟨a, b, ha, hb, hab⟩ := hL (Q.comap (algebraMap A (Localization.AtPrime P)))
          (Ideal.comap_isPrime _ Q) hQ'P (fun j hj hjQ => hQJ j hj hjQ)
        refine ⟨algebraMap A _ a, algebraMap A _ b, ha, hb, ?_⟩
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact hab)
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective P.primeCompl (u : Localization.AtPrime P)
    change IsLocalization.mk' (Localization.AtPrime P) a s = _ at has
    have haP : a ∈ P.primeCompl := by
      rw [← IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P a s, has]
      exact u.isUnit
    refine ⟨Units.map (algebraMap (Localization.AtPrime P) L : Localization.AtPrime P →* L) u, m,
      ⟨a, s, haP, s.2, ?_⟩, ?_⟩
    · rw [Units.coe_map, MonoidHom.coe_coe, ← has, IsScalarTower.algebraMap_apply A
        (Localization.AtPrime P) L s, IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L a,
        ← map_mul, IsLocalization.mk'_spec]
    · ext
      rw [hum, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨u, m, ⟨a, b, ha, hb, hab⟩, rfl⟩ Q hQ hQP hQJ
    have hK : ∀ j, algebraMap A L (t j) ≠ 0 := ht
    have hprodQ : ∀ e : Fin n → ℕ, ∏ j ∈ J, t j ^ e j ∉ Q := by
      intro e hmem
      obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
    refine ⟨a * ∏ j ∈ J, t j ^ (m j).toNat, b * ∏ j ∈ J, t j ^ (-m j).toNat,
      hQ.mul_notMem (fun h => ha (hQP h)) (hprodQ _),
      hQ.mul_notMem (fun h => hb (hQP h)) (hprodQ _), ?_⟩
    have key : ∀ j, algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat =
        algebraMap A L (t j) ^ (m j).toNat := by
      intro j
      have e : m j = ((m j).toNat : ℤ) - ((-m j).toNat : ℤ) := (Int.toNat_sub_toNat_neg _).symm
      calc algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat
          = algebraMap A L (t j) ^ (((m j).toNat : ℤ) - ((-m j).toNat : ℤ)) *
            algebraMap A L (t j) ^ (-m j).toNat := by rw [← e]
        _ = _ := by
          rw [zpow_sub₀ (hK j), zpow_natCast, zpow_natCast,
            div_mul_cancel₀ _ (pow_ne_zero _ (hK j))]
    rw [Units.val_mul, Units.coe_prod, map_mul, map_mul, map_prod, map_prod, ← hab]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow]
    rw [show (u : L) * (∏ j ∈ J, algebraMap A L (t j) ^ m j) *
        (algebraMap A L b * ∏ j ∈ J, algebraMap A L (t j) ^ (-m j).toNat) =
        (u : L) * algebraMap A L b * ∏ j ∈ J, (algebraMap A L (t j) ^ m j *
          algebraMap A L (t j) ^ (-m j).toNat) by rw [Finset.prod_mul_distrib]; ring]
    simp only [key]

end GlobalTheory.EtUnit
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.unit_of_height_one_primes : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  atlas_forward_decl _root_.GlobalTheory.EtUnit.unit_mul_monomial_iff
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtLog

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)

include hU in

theorem unitAt_fnOf_iff_not_mem {y : X} (hy : y ∈ U) (s : Γ(X, U)) :
    UnitAt y (fnOf U (gen_mem hy) s) ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [unitAt_fnOf_iff hy, GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy]

include hU in

theorem regAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    RegAt y g ↔ ∃ a b : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    exact GlobalTheory.FieldPair.regAt_exists_fraction hU hy hg
  · rintro ⟨a, b, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact (regAt_fnOf hy _ a).mul hu.inv.regAt

include hU in

theorem unitAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    UnitAt y g ↔ ∃ a b : Γ(X, U), a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧ g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 hg.regAt
    refine ⟨a, b, ?_, hb, e⟩
    rw [← unitAt_fnOf_iff_not_mem hU hy, ← e]
    exact hg.mul (GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb)
  · rintro ⟨a, b, ha, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have hua := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy ha
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact hua.mul hu.inv

include hU in

theorem primeIdealOf_le_of_specializes {y z : X} (hy : y ∈ U) (hz : z ∈ U) (hzy : z ⤳ y) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro s hs
  by_contra hs'
  rw [← GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy] at hs'
  exact (GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hz s).1 (hzy.mem_open (X.basicOpen s).isOpen hs') hs

include hU in

theorem exists_specializes_of_le {y : X} (hy : y ∈ U) (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime)
    (hQP : Q ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    ∃ (z : X) (hz : z ∈ U), z ⤳ y ∧ (hU.primeIdealOf ⟨z, hz⟩).asIdeal = Q := by
  refine ⟨(GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩ : X), (GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩).2, ?_, ?_⟩
  · have h1 := ((PrimeSpectrum.le_iff_specializes ⟨Q, hQ⟩ (hU.primeIdealOf ⟨y, hy⟩)).mp hQP).map
      hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h1
    exact h1
  · rw [GlobalTheory.QCoh.primeIdealOf_pointOfPrime]

theorem isLogChart_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U))
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U →
    IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) →
    (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  intro p _ X _ f U h n t x J Z hU hEt hx hZ
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  letI : Algebra (ZMod p) Γ(X, U) := (cstOn f U).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have hEt' : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale := hEt
  have hA : ∀ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = fnOf U h s := fun _ => rfl
  have ht : ∀ j, algebraMap Γ(X, U) X.functionField (t j) ≠ 0 := fun j => by
    rw [hA, ← hx j]; exact (x j).ne_zero
  have hxt : x = fun j => Units.mk0 _ (ht j) := funext fun j => Units.ext (hx j)
  have hB := GlobalTheory.T.fraction_field_coordinates_dlog p Γ(X, U) t hEt' X.functionField ht
  have hprod : ∀ S : Finset (Fin n),
      algebraMap Γ(X, U) X.functionField (∏ j ∈ S, t j) = ∏ j ∈ S, (x j : X.functionField) :=
    fun S => by rw [map_prod]; exact Finset.prod_congr rfl fun j _ => (hx j).symm
  refine ⟨fun y hy => ⟨fun i => ?_, ?_, ?_, ?_⟩, fun y hy g => ?_⟩
  · rw [hx i]; exact regAt_fnOf hy h (t i)
  · rw [hxt]; exact hB.1
  · intro g hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 (mem_locRing.1 hg)
    obtain ⟨ca, hca⟩ := hB.2 a
    obtain ⟨cb, hcb⟩ := hB.2 b
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    refine ⟨fun i => (fnOf U h b)⁻¹ * (fnOf U h (ca i) - g * fnOf U h (cb i)), fun i => ?_, ?_⟩
    · exact mul_mem (mem_locRing.2 hu.inv.regAt) (sub_mem (mem_locRing.2 (regAt_fnOf hy h _))
        (mul_mem hg (mem_locRing.2 (regAt_fnOf hy h _))))
    · have hB0 : fnOf U h b ≠ 0 := hu.ne_zero
      have key : dK g = (fnOf U h b)⁻¹ • (dK (fnOf U h a) - g • dK (fnOf U h b)) := by
        have e' : g * fnOf U h b = fnOf U h a := e
        rw [← e']
        simp only [dK, Derivation.leibniz]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hB0, one_smul]
      simp only [hA] at hca hcb
      rw [key]
      simp only [dK] at hca hcb ⊢
      rw [hca, hcb, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx i, smul_smul, ← sub_smul, smul_smul, mul_comm g]
  · intro S g m hm hg
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.T.root_of_monomial_quotient_integral p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal
      X.functionField S g m hm (by
        obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy _).1 (mem_locRing.1 hg)
        exact ⟨a, b, hb, by rw [hprod]; exact e⟩)
    exact mem_locRing.2 ((regAt_iff_frac hU hy _).2 ⟨a, b, hb, by rw [← hprod]; exact e⟩)
  · have hZc : ∀ z (hz : z ∈ U), z ∉ Z ↔ ∀ j ∈ J, t j ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro z hz
      rw [hZ z hz]
      simp only [not_exists, not_and, not_not]
      refine forall₂_congr fun j _ => ?_
      rw [hx j]
      exact unitAt_fnOf_iff_not_mem hU hz (t j)
    have hU' := GlobalTheory.T.unit_of_height_one_primes p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal X.functionField J ht g
    refine Iff.trans ?_ (hU'.trans ?_)
    · constructor
      · intro hL Q hQ hQP hJ
        obtain ⟨z, hz, hzy, rfl⟩ := exists_specializes_of_le hU hy Q hQ hQP
        exact (unitAt_iff_frac hU hz g).1 (hL z hzy ((hZc z hz).2 hJ))
      · intro hL z hzy hzZ
        have hz : z ∈ U := hzy.mem_open U.isOpen hy
        exact (unitAt_iff_frac hU hz g).2 (hL _ inferInstance
          (primeIdealOf_le_of_specializes hU hy hz hzy) ((hZc z hz).1 hzZ))
    · subst hxt
      exact exists_congr fun u => exists_congr fun m => and_congr_left' (unitAt_iff_frac hU hy u).symm

end GlobalTheory.EtLog
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.etale_coordinates_log_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U)) (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U → IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) → (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  atlas_forward_decl _root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord
end

section
set_option autoImplicit false

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem logCartier_rounding_family : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (x : Fin n → Kˣ) (J : Finset (Fin n)) (γ : abelian₂ K →+* abelian₂ K) (Y : Type) [Nonempty Y] (A : Y → Subring K)
    (t : Y → Kˣ) (r : Y → Fin n → ℕ), (∀ y, AlgChart (A y) x) → (∀ y j, r y j < p) → IsCartierMap p x γ →
    ∀ (a : ℕ) (η : abelian₂ K), (∀ y, η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) a) →
    extD K η = 0 → ∃ ζ ξ : abelian₂ K, (∀ y, ζ ∈ chartForms (A y) x J (t y) a) ∧
      (∀ y q, q + 1 = a → ξ ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (a = 0 → ξ = 0) ∧ η = γ ζ + extD K ξ := by
  intro K _ p _ _ n x J γ Y _ A t r hA hr hγ a η hη hd
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hc : IsCoord x := (hA y0).coord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, Q, π, hhom, hQw, hπ, -, -, hstab⟩ := GlobalTheory.T.cartier_projection_properties K p n x hc
  have hT : ∀ y, (∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) (q + 1),
        h η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) 0, h η = 0) ∧
      ∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q,
        Q η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q := by
    intro y
    exact hstab (fun q => chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q)
      (GlobalTheory.T.chart_forms_differential_closed K p (A y) n x J (t y) (r y) (hA y))
      (fun i θ hθ => GlobalTheory.T.euler_contraction_chart_forms K (A y) n x J _ i θ (hA y).mem hθ)
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hc
  obtain ⟨c, hcη⟩ : ∃ c : Finset (Fin n) → K, ∑ I, c I • logWedge x I = η :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hsp ▸ Submodule.mem_top)
  choose g hg using fun I => hπ (c I)
  have hQη : Q η = ∑ I, g I ^ p • logWedge x I := by
    rw [← hcη, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQw, hg]
  refine ⟨∑ I, g I • logWedge x I, h η, ?_, ?_, ?_, ?_⟩
  · intro y
    have hm := (hT y).2.2 a η (hη y)
    rw [GlobalTheory.T.mem_chart_forms_iff] at hm
    obtain ⟨c', hc'0, hc'A, hc'eq⟩ := hm
    have heq : ∀ I, c' I = g I ^ p := by
      have h0 : ∑ I, (c' I - g I ^ p) • logWedge x I = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc'eq, ← hQη, sub_self]
      intro I
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 I)
    rw [GlobalTheory.T.mem_chart_forms_iff]
    refine ⟨g, ?_, ?_, rfl⟩
    · intro I hI
      have h1 := hc'0 I hI
      rw [heq] at h1
      exact (pow_eq_zero_iff hp.ne').mp h1
    · intro I
      have h1 := hc'A I
      rw [heq] at h1
      exact GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem K p (A y) n x I J (t y) (r y) (g I) hp (hA y) (hr y) h1
  · intro y q hq
    subst hq
    exact (hT y).1 q η (hη y)
  · intro ha
    subst ha
    exact (hT y0).2.1 η (hη y0)
  · rw [map_sum]
    simp_rw [GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ]
    rw [← hQη]
    have h2 := hhom η
    rw [hd, map_zero, add_zero] at h2
    exact sub_eq_iff_eq_add'.mp h2

end GlobalTheory
end

section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_eq_extD_imp_eq_zero :
    ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ)
      (γ : abelian₂ K →+* abelian₂ K), IsCoord x → IsCartierMap p x γ → ∀ ζ ξ : abelian₂ K, γ ζ = extD K ξ → ζ = 0 := by
  intro K _ p _ _ n x γ hx hγ ζ ξ hζ
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hx
  have hmem : ζ ∈ Submodule.span K (Set.range (logWedge x)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  obtain ⟨-, Q, π, -, hQ, -, hπ, hQd, -⟩ := GlobalTheory.T.cartier_projection_properties K p n x hx
  have hγs : γ (∑ I, c I • logWedge x I) = ∑ I, (c I ^ p) • logWedge x I := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ (c I) I
  have hfix : Q (γ (∑ I, c I • logWedge x I)) = γ (∑ I, c I • logWedge x I) := by
    rw [hγs, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ, hπ]
  have h0 : ∑ I, (c I ^ p) • logWedge x I = 0 := by
    rw [← hγs, ← hfix, hζ, hQd]
  have hc : ∀ I, c I ^ p = 0 := fun I =>
    (Fintype.linearIndependent_iff.1 hli) (fun I => c I ^ p) h0 I
  have hc' : ∀ I, c I = 0 := fun I =>
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 (hc I)
  simp [hc']

end GlobalTheory
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory

theorem mem_logSec_iff {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {G : CartierDiv X} {a : ℕ}
    {U : X.Opens} {η : abelian₂ X.functionField} : η ∈ logSec Z G a U ↔ ∀ y ∈ U, η ∈ logAt Z G a y := by
  simp only [logSec, latSec, AddSubgroup.mem_iInf]

theorem mem_inter_of_forall {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι)
    (y : X) (h : ∀ i ∈ s, y ∈ U i) : y ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact ⟨h i (Finset.mem_insert_self i s), ih fun k hk => h k (Finset.mem_insert_of_mem hk)⟩

private theorem spanForms_le_of_mem_closure_smul {K : Type} [Field K] (M : Set K) (A : Subring K)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (H H' : Set Ω[K⁄ℤ])
    (hH : ∀ h ∈ H, h ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) :
    ∀ a, spanForms M H a ≤ spanForms M H' a := by
  have key : ∀ a (c : K), c ∈ M → ∀ v : Fin a → Ω[K⁄ℤ],
      (∀ i, v i ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) →
      c • ExteriorAlgebra.ιMulti K a v ∈ spanForms M H' a := by
    intro a
    induction a with
    | zero =>
      intro c hc v _
      exact AddSubgroup.subset_closure ⟨c, hc, v, fun i => i.elim0, rfl⟩
    | succ a ih =>
      intro c hc v hv
      have hpre : ∀ h' ∈ H', ∀ z ∈ spanForms M H' a,
          ExteriorAlgebra.ι K h' * z ∈ spanForms M H' (a + 1) := by
        intro h' hh' z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨c', hc', v', hv', rfl⟩ := hz
          apply AddSubgroup.subset_closure
          refine ⟨c', hc', Fin.cons h' v', ?_, ?_⟩
          · intro i
            refine Fin.cases hh' (fun k => ?_) i
            simpa using hv' k
          · rw [ExteriorAlgebra.ιMulti_succ_apply, mul_smul_comm]
            rfl
        | zero => simp
        | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
        | neg z _ h1 => rw [mul_neg]; exact neg_mem h1
      have claim : ∀ w ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}, ∀ c ∈ M,
          c • (ExteriorAlgebra.ι K w * ExteriorAlgebra.ιMulti K a (Matrix.vecTail v)) ∈
            spanForms M H' (a + 1) := by
        intro w hw
        induction hw using AddSubgroup.closure_induction with
        | mem w hw =>
          obtain ⟨b, hb, h', hh', rfl⟩ := hw
          intro c hc
          rw [map_smul, smul_mul_assoc, smul_smul, ← mul_smul_comm]
          exact hpre h' hh' _ (ih (c * b) (hM c hc b hb) _ (fun i => hv i.succ))
        | zero => intro c _; simp
        | add w1 w2 _ _ h1 h2 =>
          intro c hc
          rw [map_add, add_mul, smul_add]
          exact add_mem (h1 c hc) (h2 c hc)
        | neg w _ h1 =>
          intro c hc
          rw [map_neg, neg_mul, smul_neg]
          exact neg_mem (h1 c hc)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      exact claim _ (hv 0) c hc
  intro a
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, v, hv, rfl⟩
  exact key a c hc v (fun i => hH _ (hv i))

private theorem dlog_mul' {K : Type} [Field K] (u v : Kˣ) : dlog (u * v) = dlog u + dlog v := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1 <;> congr 1 <;> simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev] <;> field_simp

private theorem dlog_one' {K : Type} [Field K] : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

private theorem dlog_pow' {K : Type} [Field K] (u : Kˣ) (k : ℕ) : dlog (u ^ k) = k • dlog u := by
  induction k with
  | zero => simp [dlog_one']
  | succ k ih => rw [pow_succ, dlog_mul', ih, succ_nsmul]

private theorem dlog_inv' {K : Type} [Field K] (u : Kˣ) : dlog u⁻¹ = - dlog u := by
  have h := dlog_mul' u u⁻¹
  rw [mul_inv_cancel, dlog_one'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem dlog_zpow' {K : Type} [Field K] (u : Kˣ) (m : ℤ) : dlog (u ^ m) = m • dlog u := by
  cases m with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast, dlog_pow', natCast_zsmul]
  | negSucc k => rw [zpow_negSucc, dlog_inv', dlog_pow', negSucc_zsmul]

private theorem dlog_prod_zpow {K : Type} [Field K] {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Kˣ) (m : Fin n → ℤ) :
    dlog (∏ j ∈ s, x j ^ m j) = ∑ j ∈ s, m j • dlog (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul', dlog_zpow', ih]

private theorem dK_units_eq_smul_dlog {K : Type} [Field K] (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  simp [dlog, smul_smul]

private theorem logUnit_of_unitAt {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {y : X}
    {g : X.functionFieldˣ} (h : UnitAt y (g : X.functionField)) : LogUnit Z y g := by
  obtain ⟨V, hyV, hV⟩ := h.exists_nhds
  intro z hz _
  exact hV z (hz.mem_open V.isOpen hyV)

private theorem exists_unitAt_dK_eq_smul_dlog_of_regAt {X : Scheme.{0}} [IsIntegral X] {y : X} {a : X.functionField} (ha : RegAt y a) :
    ∃ u : X.functionFieldˣ, UnitAt y (u : X.functionField) ∧ ∃ b, RegAt y b ∧ dK a = b • dlog u := by
  obtain ⟨s, rfl⟩ := ha
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with hs | hs
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨s, hs, rfl⟩, _, ⟨s, rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    exact h
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨1 - s, hs, rfl⟩, _, ⟨-(1 - s), rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    rw [map_neg, neg_smul, ← h]
    simp [dK, map_sub]

private theorem logAt_le_chartForms_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    logAt Z D a y ≤ chartForms (locRing y) x J t a := by
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | D.RegularAt y c} _ a ≤ spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  have hch := hc.chart y hy
  have hfr : ∀ k, ∀ b ∈ locRing y, b • frame x J k ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} :=
    fun k b hb => AddSubgroup.subset_closure ⟨b, hb, _, ⟨k, rfl⟩, rfl⟩
  have hdK : ∀ k, ∀ b ∈ locRing y, b • dK (x k : X.functionField) ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} := by
    intro k b hb
    by_cases hk : k ∈ J
    · have h1 : dK (x k : X.functionField) = (x k : X.functionField) • frame x J k := by
        rw [frame, if_pos hk, dK_units_eq_smul_dlog]
      rw [h1, smul_smul]
      exact hfr k _ ((locRing y).mul_mem hb (hch.mem k))
    · have h1 : dK (x k : X.functionField) = frame x J k := by rw [frame, if_neg hk]
      rw [h1]
      exact hfr k b hb
  rw [dlog_mul', dlog_prod_zpow]
  refine add_mem ?_ (sum_mem fun k hk => zsmul_mem ?_ _)
  · obtain ⟨a1, _, ha1⟩ := hu.inv
    obtain ⟨a0, _, ha0⟩ := hu
    have huA : (u : X.functionField) ∈ locRing y := mem_locRing.2 ⟨a0, ha0⟩
    have huiA : ((u⁻¹ : X.functionFieldˣ) : X.functionField) ∈ locRing y := by
      rw [Units.val_inv_eq_inv_val]
      exact mem_locRing.2 ⟨a1, ha1⟩
    obtain ⟨cf, hcf, hdu⟩ := hch.deriv _ huA
    rw [dlog, hdu, Finset.smul_sum]
    exact sum_mem fun k _ => by
      rw [smul_smul]
      exact hdK k _ ((locRing y).mul_mem huiA (hcf k))
  · have h1 : dlog (x k) = (1 : X.functionField) • frame x J k := by rw [frame, if_pos hk, one_smul]
    rw [h1]
    exact hfr k 1 (locRing y).one_mem

private theorem chartForms_le_logAt_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    chartForms (locRing y) x J t a ≤ logAt Z D a y := by
  classical
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a ≤ spanForms {c | D.RegularAt y c} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨k, rfl⟩
  by_cases hk : k ∈ J
  · have hlu : LogUnit Z y (x k) := by
      refine (hc.logUnit y hy (x k)).2 ⟨1, fun i => if i = k then 1 else 0, ⟨1, isUnit_one, by simp⟩, ?_⟩
      rw [one_mul, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (fun h => absurd hk h)]
      simp
    rw [frame, if_pos hk, ← one_smul X.functionField (dlog (x k))]
    exact AddSubgroup.subset_closure ⟨1, (locRing y).one_mem, _, ⟨x k, hlu, rfl⟩, rfl⟩
  · rw [frame, if_neg hk]
    obtain ⟨u, hu, b, hb, hd⟩ := exists_unitAt_dK_eq_smul_dlog_of_regAt (mem_locRing.1 ((hc.chart y hy).mem k))
    rw [hd]
    exact AddSubgroup.subset_closure ⟨b, mem_locRing.2 hb, _, ⟨u, logUnit_of_unitAt Z hu, rfl⟩, rfl⟩

private theorem isEqn_smul_add_sum_smul {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (G : CartierDiv X) (r : C → ℕ) (p : ℕ) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n))
    (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j) (y : X) (t : X.functionFieldˣ)
    (ht : G.IsEqn y t) (hE : ∀ c, (E c).IsEqn y ((e c).elim 1 x)) :
    (p • G + ∑ c, r c • E c).IsEqn y
      (t ^ p * ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c)) := by
  classical
  have hs : ∀ s : Finset C, (∑ c ∈ s, r c • E c).IsEqn y (∏ c ∈ s, ((e c).elim 1 x) ^ r c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((hE a).nsmul (r a)).add ih
  have hprod : ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
      ∏ c, ((e c).elim 1 x) ^ r c := by
    have h1 : ∀ j, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
        ∏ c, (if e c = some j then x j ^ r c else 1) := by
      intro j
      rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rcases hc : e c with _ | j0
    · simp
    · have hj0 : j0 ∈ J := (hJ j0).2 ⟨c, hc⟩
      simp only [Option.some.injEq, Option.elim_some]
      rw [Finset.prod_ite_eq J j0 (fun j => x j ^ r c), if_pos hj0]
  rw [hprod]
  exact (ht.nsmul p).add (hs _)

theorem cartierAt_atlas_inter : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X]
    [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) →
    ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ →
    CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s))
      (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr s j hj γ hγ
  classical
  obtain ⟨e, he_inj, hJ, heqn⟩ := 𝒜.snc j
  have hW : ∀ w ∈ inter 𝒜.U s, w ∈ 𝒜.U j := fun w hw => (Finset.inf_le hj : inter 𝒜.U s ≤ 𝒜.U j) hw
  have hcoord : IsCoord (𝒜.x j) := ((𝒜.chart j).chart _ (𝒜.gen j)).coord
  have hR : ∀ j', (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c) < p := by
    intro j'
    by_cases hne : ∃ c, e c = some j'
    · obtain ⟨c0, hc0⟩ := hne
      have h1 : Finset.univ.filter (fun c => e c = some j') = {c0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => he_inj c c0 j' h hc0, fun h => h ▸ hc0⟩
      rw [h1, Finset.sum_singleton]
      exact hr c0
    · have h1 : Finset.univ.filter (fun c => e c = some j') = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hne ⟨c, h⟩
      rw [h1, Finset.sum_empty]
      exact (Fact.out : p.Prime).pos
  choose tG htG using fun w : X => G.exists_isEqn w
  have hLe : ∀ (D : CartierDiv X) (w : X), w ∈ 𝒜.U j → ∀ (t : X.functionFieldˣ), D.IsEqn w t → ∀ a,
      logAt (suppAll E) D a w = chartForms (locRing w) (𝒜.x j) (𝒜.J j) t a :=
    fun D w hw t ht a => le_antisymm (logAt_le_chartForms_of_isLogChart (𝒜.chart j) hw ht a) (chartForms_le_logAt_of_isLogChart (𝒜.chart j) hw ht a)
  have hG' : ∀ w ∈ 𝒜.U j, (p • G + ∑ c, r c • E c).IsEqn w
      (tG w ^ p * ∏ j' ∈ 𝒜.J j, 𝒜.x j j' ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)) :=
    fun w hw => isEqn_smul_add_sum_smul E G r p (𝒜.x j) (𝒜.J j) e hJ w (tG w) (htG w) (fun c => heqn c w hw)
  haveI hY : Nonempty {w : X // w ∈ inter 𝒜.U s} :=
    ⟨⟨genericPoint X, mem_inter_of_forall _ _ _ (fun i _ => 𝒜.gen i)⟩⟩
  have hfam := fun a η => logCartier_rounding_family X.functionField p n (𝒜.x j) (𝒜.J j) γ
    {w : X // w ∈ inter 𝒜.U s} (fun w => locRing w.1) (fun w => tG w.1)
    (fun _ j' => ∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)
    (fun w => (𝒜.chart j).chart w.1 (hW _ w.2)) (fun _ => hR) hγ a η
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ h0
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x 0 (by rw [h0, map_zero])
  · intro a x _ z _ h
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x z h
  · intro y hy hd
    obtain ⟨ζ, ξ, hζ, _, h0, hyeq⟩ := hfam 0 y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ?_⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hyeq, h0 rfl, map_zero, add_zero]
  · intro a y hy hd
    obtain ⟨ζ, ξ, hζ, hξ, _, hyeq⟩ := hfam (a + 1) y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ξ, mem_logSec_iff.2 fun w hw => ?_, hyeq⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hLe _ _ (hW _ hw) _ (hG' _ (hW _ hw))]
      exact hξ ⟨w, hw⟩ a rfl

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.cartier_operator_log_sections : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ → CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s)) (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  atlas_forward_decl _root_.GlobalTheory.cartierAt_atlas_inter
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem mem_inter_iff {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ inter U s ↔ ∀ i ∈ s, y ∈ U i := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [← ih]
    exact Iff.rfl

theorem decomp_of_isLifted (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p]
    {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι)
    (hn : n < p) (hL : IsLifted p (suppAll E) 𝒜.U 𝒜.x) : Decomp p 𝒜 := by
  intro G r hr a b hH
  exact GlobalTheory.T.cech_log_forms_frobenius_lift p (suppAll E) 𝒜.U 𝒜.x (inter 𝒜.U) G (p • G + ∑ c, r c • E c) hn 𝒜.gen
    (fun i => ((𝒜.chart i).chart _ (𝒜.gen i)).coord)
    (fun s _ y => mem_inter_iff 𝒜.U s y) hL
    (GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr).1
    (fun q s η hη => GlobalTheory.T.log_sections_differential_closed p 𝒜 G r hr q (inter 𝒜.U s) η hη)
    (fun s j hj γ hγ => GlobalTheory.T.cartier_operator_log_sections p 𝒜 G r hr s j hj γ hγ)
    a b hH

end GlobalTheory.LogDR
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.frobenius_decomposition_of_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι), n < p → IsLifted p (suppAll E) 𝒜.U 𝒜.x → Decomp p 𝒜 := by
  atlas_forward_decl _root_.GlobalTheory.LogDR.decomp_of_isLifted
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem isFlatLift_stalkMap_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  intro p _ Y X g f π hP U n t hU ht y hy
  obtain ⟨hs, hk⟩ := GlobalTheory.T.mod_p_squared_stalk_surjective p Y X g f π hP y
  have hfl := GlobalTheory.T.etale_coordinates_stalk_flat g U t hU ht (π y) hy
  refine ⟨hs, hk, fun w => ?_⟩
  rw [GlobalTheory.T.flat_mod_p_squared_torsion p _ hfl w, hk w]

end GlobalTheory.DI
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.etale_coordinates_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  atlas_forward_decl _root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem lifted_stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens)
    (h : W' ≤ f ⁻¹ᵁ W) (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply f W z (h hz) s
  have h2 := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z hz ((f.app W).hom s)
  exact h1.trans h2.symm

theorem isLifted_of_sncCharts : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ {ι : Type} [Nonempty ι] (C : ι → SncChart g n L σ) (Z : Set X) (U : ι → X.Opens) (hU : ∀ i, U i ≤ π ⁻¹ᵁ (C i).U) (hgen : ∀ i, genericPoint X ∈ U i) (x : ι → Fin n → X.functionFieldˣ) (J : ι → Finset (Fin n)), (∀ i l, (x i l : X.functionField) = fnOf (U i) (hgen i) ((π.appLE (C i).U (U i) (hU i)).hom ((C i).t l))) → (∀ i l, l ∈ J i → ∃ c, (C i).e c = some l) → (∀ i, IsLogChart Z (U i) (x i) (J i)) → IsLifted p Z U x := by
  intro p _ Y X _ q f π hpb n s L σ hL ι _ C Z U hU hgen x J hx hJ hchart
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hη : ∀ i, π (genericPoint X) ∈ (C i).U := fun i => hU i (hgen i)
  let πK : Y.presheaf.stalk (π (genericPoint X)) →+* X.functionField := (π.stalkMap (genericPoint X)).hom
  have hflat : IsFlatLift p πK :=
    GlobalTheory.T.etale_coordinates_flat_lift p Y X q f π hpb (C i₁).U (C i₁).t (C i₁).affine (C i₁).etale (genericPoint X) (hη i₁)
  have hpK : (p : X.functionField) = 0 := by
    have h0 := (hflat.ker (p : Y.presheaf.stalk (π (genericPoint X)))).2 ⟨1, by ring⟩
    simpa using h0
  haveI : CharP X.functionField p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpK
  have hpp := logLift_pp_zero p πK hflat
  choose F hF1 hF2 hF3 using fun i =>
    GlobalTheory.T.exists_frobenius_lift_stalk p q (C i).U (C i).t (C i).affine (C i).etale (π (genericPoint X)) (hη i)

  have hlift : ∀ i l, πK ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom ((C i).t l)) =
      (x i l : X.functionField) := by
    intro i l
    rw [hx i l]
    exact lifted_stalkMap_germ_appLE π (C i).U (U i) (hU i) (genericPoint X) (hgen i) ((C i).t l)
  refine ⟨Y.presheaf.stalk (π (genericPoint X)), inferInstance, πK, F, hflat, ?_, ?_, ?_⟩
  · intro i z
    obtain ⟨w, hw⟩ := hF1 i z
    rw [hw, map_add, map_pow, map_mul, map_natCast, hpK, zero_mul, add_zero]
  · intro i l
    exact ⟨_, hlift i l, hF2 i l⟩
  intro y t hyt a ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨z, hz⟩ := hflat.surj (a : X.functionField)
    exact ⟨z, hz, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hsp : π (genericPoint X) ⤳ π y :=
    ((genericPoint_spec X).specializes (Set.mem_univ y)).map π.continuous
  have hsurj := (GlobalTheory.T.mod_p_squared_stalk_surjective p Y X q f π hpb y).1
  have hloc := GlobalTheory.T.local_ring_image_stalk_map π y hsp hsurj
  set At := stalkIm hsp with hAt
  have hmap : (locRing y : Set X.functionField) = (At.map πK : Set X.functionField) := by
    ext c
    rw [SetLike.mem_coe, hloc, SetLike.mem_coe, Subring.mem_map]
  have hstab : ∀ i ∈ t, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w :=
    fun i hi z hz => hF3 i (π y) (hU i (hyt i hi)) hsp z hz
  obtain ⟨u, m, hu, rfl⟩ := ((hchart i₀).logUnit y (hyt i₀ hi₀) a).1 ha
  rw [hmap]

  have hu0 : (u : X.functionField) ≠ 0 := u.ne_zero
  have hU1 : LogLift p πK F t (At.map πK : Set X.functionField) (u : X.functionField) := by
    have h2 := (unitAt_iff hu0).1 hu
    refine logLift_of_unit_mem_map p πK F t At hflat hstab _ hu0 ?_ ?_
    · exact Subring.mem_map.2 ((hloc _).1 h2.1)
    · exact Subring.mem_map.2 ((hloc _).1 h2.2)

  have hcoord : ∀ j ∈ J i₀, LogLift p πK F t (At.map πK : Set X.functionField) (x i₀ j : X.functionField) := by
    intro j hj
    obtain ⟨c, hc⟩ := hJ i₀ j hj
    refine ⟨_, hlift i₀ j, fun i hi => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.T.snc_chart_equations_differ_unit q L σ hL (C i₀) (C i) (π y) (hU i₀ (hyt i₀ hi₀)) (hU i (hyt i hi)) c
    rw [hc] at hv
    change (Y.presheaf.germ (C i₀).U (π y) (hU i₀ (hyt i₀ hi₀))).hom ((C i₀).t j) = _ at hv
    have hv' := congrArg (Y.presheaf.stalkSpecializes hsp).hom hv
    have e1 : ∀ (V : Y.Opens) (hV : π y ∈ V) (r : Γ(Y, V)),
        (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V (π y) hV).hom r) =
          (Y.presheaf.germ V (π (genericPoint X)) (hsp.mem_open V.isOpen hV)).hom r :=
      fun V hV r => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hV hsp r
    rw [map_mul] at hv'
    have hv2 : (Y.presheaf.germ (C i₀).U (π (genericPoint X)) (hη i₀)).hom ((C i₀).t j) =
        (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) *
          (Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (((C i).e c).elim 1 (C i).t) := by
      refine (e1 _ _ _).symm.trans (hv'.trans ?_)
      congr 1
      exact e1 _ _ _
    set sv := (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) with hsv
    set sv' := (Y.presheaf.stalkSpecializes hsp).hom ((v⁻¹ : (Y.presheaf.stalk (π y))ˣ) :
      Y.presheaf.stalk (π y)) with hsv'
    have hsvA : sv ∈ At := ⟨_, rfl⟩
    have hsv'A : sv' ∈ At := ⟨_, rfl⟩
    have hvv : sv * sv' = 1 := by rw [hsv, hsv', ← map_mul, Units.mul_inv, map_one]
    have hkey : ∀ o : Option (Fin n),
        F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) =
          ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) ^ p := by
      rintro (_ | l)
      · show F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom 1) = _
        simp
      · exact hF2 i l
    obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.frobenius_lift_unit_times_coord p At (F i) sv sv' _ hpp hsv'A hvv (hstab i hi sv hsvA) (hkey ((C i).e c))
    refine ⟨w, Subring.mem_map.2 ⟨w, hwA, rfl⟩, ?_⟩
    rw [hv2]
    exact hw
  rw [Units.val_mul, Units.coe_prod]
  refine logLift_mul p πK F t _ hflat hU1 ?_
  refine Finset.prod_induction _ (LogLift p πK F t (At.map πK : Set X.functionField))
    (fun _ _ => logLift_mul p πK F t _ hflat) (logLift_one p πK F t _) (fun j hj => ?_)
  rw [Units.val_zpow_eq_zpow_val]
  exact logLift_zpow p πK F t _ hflat (x i₀ j).ne_zero (hcoord j hj) (m j)

end GlobalTheory.DI
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.LogAtlas

theorem fnOf_coord_ne_zero {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {U : X.Opens} (h : genericPoint X ∈ U) {n : ℕ} {t : Fin n → Γ(X, U)}
    (ht : IsEtCoord f U t) (j : Fin n) : fnOf U h (t j) ≠ 0 := by
  intro h0
  have h1 : t j = 0 := fnOf_injective U h (h0.trans (map_zero _).symm)
  letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U) := ht
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have h2 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U)) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact (MvPolynomial.eval₂Hom_X' _ _ j).trans h1
  exact one_ne_zero (h2 h3)

theorem exists_div_of_sec {X : Scheme.{0}} [IsIntegral X] {M : LB X} (hM : M.IsLB) (τ : M.Sec) (c₀ : M.ι)
    (h₀ : genericPoint X ∈ M.U c₀) (hτ : fnOf _ h₀ (τ.f c₀) ≠ 0) :
    ∃ E : CartierDiv X, toPic E = cls M hM ∧ ∀ (c : M.ι) (y : X) (hy : y ∈ M.U c)
      (g : X.functionFieldˣ), (g : X.functionField) = fnOf _ (gen_mem hy) (τ.f c) → E.IsEqn y g := by
  have P := presents_ofLB hM c₀ h₀
  have hr : P.rat τ ≠ 0 := fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])
  have Q := P.add_principal (Units.mk0 _ hr)
  refine ⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩
  have e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr := Units.ext (by
    rw [hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])
  exact e ▸ Q.isEqn c y hy

theorem exists_div_of_chart {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {d s : ℕ} {M : Fin s → LB X} (hM : ∀ i, (M i).IsLB) {τ : ∀ i, (M i).Sec}
    (C₀ : SncChart f d M τ) (h₀ : genericPoint X ∈ C₀.U) :
    ∃ E : Fin s → CartierDiv X, (∀ i, toPic (E i) = cls (M i) (hM i)) ∧
      ∀ (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (x : Fin d → X.functionFieldˣ),
        (∀ j, (x j : X.functionField) = fnOf C.U h (C.t j)) →
        ∀ i, ∀ y ∈ C.U, (E i).IsEqn y ((C.e i).elim 1 x) := by
  have key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) :
      fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t) := by
    rw [← fnOf_resG (C.le i) h, C.eq i, map_mul]
  have H (i : Fin s) := exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by
    rw [key C₀ h₀ i]
    refine mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_
    rcases C₀.e i with _ | a
    · simp
    · exact fnOf_coord_ne_zero h₀ C₀.etale a)
  choose E hE hE' using H
  refine ⟨E, hE, fun C h x hx i y hy => ?_⟩
  have hu := unitAt_fnOf hy h (C.u i)
  have e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) =
      fnOf C.U h ((C.e i).elim 1 C.t) := by
    rcases C.e i with _ | a
    · simp
    · exact hx a
  have h1 := hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by
    rw [Units.val_mul, Units.val_mk0, e]; exact (key C h i).symm)
  rw [h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _),
    one_div]
  exact hu.inv

noncomputable def pullChart {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {X X' : Scheme.{0}}
    {f : X ⟶ Sp R} {f' : X' ⟶ Sp R'} {π : X' ⟶ X} (hP : IsPullback π f' f (spMap φ)) {d s : ℕ}
    {L : Fin s → LB X} {σ : ∀ i, (L i).Sec} (C : SncChart f d L σ) :
    SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) where
  U := π ⁻¹ᵁ C.U
  affine := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).1
  t := fun a => (π.app C.U).hom (C.t a)
  etale := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).2
  c := fun i => fun _ => C.c i
  le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
  e := C.e
  inj := C.inj
  u := fun i => Units.map (π.app C.U).hom (C.u i)
  eq := fun i => by
    show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
    rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
    rcases h : C.e i with _ | a
    · simp
    · simp

theorem exists_atlas_decomp : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∃ (m : ℕ) (E : Fin s → CartierDiv X) (𝒜 : SncAtlas E d (Fin m)), Decomp p 𝒜 ∧ ∀ i, toPic (E i) = CechPic.pull π (cls (L i) (h.isLB i)) := by
  classical
  intro p _ Y X _ g f π d _ hP hf hd s L σ h
  choose D hD using fun x : X => h.chart (π x)
  have hpr := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X))
    (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)
  let ε := T.equivFin.symm
  let C : Fin T.card → SncChart g d L σ := fun k => D (ε k)
  have hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U := gen_mem (x := ε k) (hD _)
  have hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U := by
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    obtain ⟨k, hk⟩ := ε.surjective ⟨z, hz⟩
    obtain rfl : (ε k : X) = z := congrArg Subtype.val hk
    exact ⟨k, hy⟩
  obtain ⟨k₀, -⟩ := hcov (genericPoint X)
  have : Nonempty (Fin T.card) := ⟨k₀⟩
  obtain ⟨E, hE, hE'⟩ := exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)
  let x : Fin T.card → Fin d → X.functionFieldˣ := fun k j =>
    Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)
  let J : Fin T.card → Finset (Fin d) := fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j
  have hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j := by simp [J]
  have heq (k) := hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)
  have hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k) := by
    refine GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine
      (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_
    constructor
    · intro hy'
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy'
      have h1 := (heq k c y hy).mem_supp_iff.1 hc
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1
      rcases he : (C k).e c with _ | a
      · rw [he] at h1
        exact (h1 (unitAt_one y)).elim
      · rw [he] at h1
        exact ⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩
    · rintro ⟨j, hj, hu⟩
      obtain ⟨c, hc⟩ := (hJ k j).1 hj
      refine Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)
      rw [hc]
      exact hu
  let 𝒜 : SncAtlas E d (Fin T.card) :=
    { U := fun k => (pullChart hP (C k)).U
      x := x
      J := J
      affine := fun k => (pullChart hP (C k)).affine
      gen := hgen
      cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y)
      chart := hlog
      snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }
  have : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  refine ⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩
  refine DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J
    (fun k l => ?_) (fun k l => (hJ k l).1) hlog
  exact congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l)))
    (π.app_eq_appLE)

end GlobalTheory.LogAtlas
end
