import Mathlib
import GroundTheory.LocalFields.ConductorMatch
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import GroundTheory.PAdicHodge.SenTateCharUnits
import GroundTheory.LocalFields.PrincipalUnitsModule
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.NormalizedTraceClosure
import GroundTheory.PAdicHodge.NormalizedTrace
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.TateCpTwist

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance isAlgClosure_padicAlgCl : IsAlgClosure K (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

variable {K} (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)

def charTowerGal (k : ℕ) : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p k).comap η

theorem mem_charTowerGal {k : ℕ} {σ : Gal(PadicAlgCl p/K)} : σ ∈ charTowerGal η k ↔ η σ ∈ unitsOneAdd p k :=
  Iff.rfl

instance charTowerGal_normal (k : ℕ) : (charTowerGal η k).Normal :=
  Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative _) η

theorem charTowerGal_antitone : Antitone (charTowerGal η) := fun _ _ h =>
  Subgroup.comap_mono (unitsOneAdd_antitone h)

variable {η}

theorem isOpen_charTowerGal (hη : Continuous η) (k : ℕ) : IsOpen (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  (isOpen_unitsOneAdd k).preimage hη

theorem isClosed_charTowerGal (hη : Continuous η) (k : ℕ) :
    IsClosed (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_charTowerGal hη k)

variable (η)

def charTower (k : ℕ) : IntermediateField K (PadicAlgCl p) :=
  _root_.IntermediateField.fixedField (charTowerGal η k)

theorem charTower_mono : Monotone (charTower η) := fun _ _ h =>
  _root_.IntermediateField.fixedField_antitone (charTowerGal_antitone η h)

variable {η}

theorem fixingSubgroup_charTower (hη : Continuous η) (k : ℕ) :
    (charTower η k).fixingSubgroup = charTowerGal η k :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨charTowerGal η k, isClosed_charTowerGal hη k⟩

theorem finiteDimensional_charTower (hη : Continuous η) (k : ℕ) : FiniteDimensional K (charTower η k) := by
  have h := isOpen_charTowerGal hη k
  rw [← fixingSubgroup_charTower hη k] at h
  exact (InfiniteGalois.isOpen_iff_finite _).1 h

theorem isGalois_charTower (hη : Continuous η) (k : ℕ) : IsGalois K (charTower η k) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_charTower hη]
  infer_instance

theorem restrictNormalHom_charTower_eq_one_iff (hη : Continuous η) (k : ℕ)
    [Normal K (charTower η k)] (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ = 1 ↔ η σ ∈ unitsOneAdd p k := by
  rw [← MonoidHom.mem_ker, (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  rfl

theorem isAbelianGalois_charTower (hη : Continuous η) (k : ℕ) : IsAbelianGalois K (charTower η k) := by
  have := isGalois_charTower hη k
  refine { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩ }
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) a
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) b
  rw [← map_mul, ← map_mul, ← div_eq_one, ← map_div]
  rw [restrictNormalHom_charTower_eq_one_iff hη, map_div, map_mul, map_mul, mul_comm (η σ), div_self']
  exact one_mem _

theorem map_mem_charTower (hη : Continuous η) {k : ℕ} (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ charTower η k) : σ y ∈ charTower η k := by
  have := isGalois_charTower hη k
  have h : σ y = ((σ.restrictNormal (charTower η k) ⟨y, hy⟩ : charTower η k) : PadicAlgCl p) :=
    (AlgEquiv.restrictNormal_commutes σ (charTower η k) ⟨y, hy⟩).symm
  rw [h]
  exact SetLike.coe_mem _

section CFT

variable (K) [FiniteDimensional ℚ_[p] K]

def artinGal (n : ℕ) : Subgroup Gal(PadicAlgCl p/K) :=
  ((unitFiltrationUnits K n).map (localArtinMap K (PadicAlgCl p))).comap
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)))

variable (η) in

def artinImage (n : ℕ) : Subgroup ℤ_[p]ˣ := (artinGal K n).map η

variable {K}

theorem artinGal_antitone : Antitone (artinGal K) := fun _ _ h =>
  Subgroup.comap_mono (Subgroup.map_mono (unitFiltrationUnits_antitone h))

variable (η) in
theorem artinImage_antitone : Antitone (artinImage K η) := fun _ _ h =>
  Subgroup.map_mono (artinGal_antitone h)

omit [FiniteDimensional ℚ_[p] K] in

theorem restrictAb_restrictNormalHom (E : IntermediateField K (PadicAlgCl p)) [Normal K E]
    (h : E ≤ maximalAbelianExtension K (PadicAlgCl p)) (ρ : Gal(PadicAlgCl p/K)) :
    restrictAb E h (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)) ρ) =
      AlgEquiv.restrictNormalHom E ρ := by
  ext x
  rw [restrictAb_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

omit [FiniteDimensional ℚ_[p] K] in

theorem eq_one_of_mem_fixingSubgroup_maximalAbelianExtension (hη : Continuous η)
    {ρ : Gal(PadicAlgCl p/K)}
    (hρ : ρ ∈ (maximalAbelianExtension K (PadicAlgCl p)).fixingSubgroup) : η ρ = 1 := by
  rw [fixingSubgroup_maximalAbelianExtension] at hρ
  have hker : (commutator Gal(PadicAlgCl p/K)).topologicalClosure ≤ η.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker η) ?_
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hη
  exact hker hρ

theorem restrictNormalHom_mem_upperRamificationGroup_iff (hη : Continuous η) (k n : ℕ)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ artinImage K η n ⊔ unitsOneAdd p k := by
  set M := charTower η k
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  have hM := le_maximalAbelianExtension M
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap M n, Subgroup.mem_sup]
  constructor
  · rintro ⟨u, hu, huσ⟩
    obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) u)
    have hρA : ρ ∈ artinGal K n := ⟨u, hu, hρ.symm⟩
    refine ⟨η ρ, ⟨ρ, hρA, rfl⟩, η (ρ⁻¹ * σ), ?_, by rw [map_mul, map_inv, mul_inv_cancel_left]⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, ← huσ, MonoidHom.comp_apply, ← hρ, restrictAb_restrictNormalHom,
        inv_mul_cancel]
    exact (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
  · rintro ⟨a, ⟨ρ, hρA, rfl⟩, b, hb, hab⟩
    obtain ⟨u, hu, hu'⟩ := hρA
    refine ⟨u, hu, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      refine (restrictNormalHom_charTower_eq_one_iff hη k _).2 ?_
      rw [map_mul, map_inv, ← hab, inv_mul_cancel_left]
      exact hb
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [MonoidHom.comp_apply, hu', restrictAb_restrictNormalHom, h1]

theorem artinImage_add_eq_map_pow (hη : Continuous η) {n e : ℕ}
    (h : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinImage K η (n + e) = (artinImage K η n).map (powMonoidHom p) := by
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  ext a
  constructor
  · rintro ⟨ρ, ⟨u, hu, hu'⟩, rfl⟩
    rw [← h] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨ρw, hρw⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) w)
    refine ⟨η ρw, ⟨ρw, ⟨w, hw, hρw.symm⟩, rfl⟩, ?_⟩
    have hfix : ρ⁻¹ * ρw ^ p ∈ Lab.fixingSubgroup := by
      rw [← Lab.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_pow, hρw, ← hu',
        powMonoidHom_apply, map_pow, inv_mul_cancel]
    have h1 := eq_one_of_mem_fixingSubgroup_maximalAbelianExtension hη hfix
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h1
    rw [powMonoidHom_apply, h1]
  · rintro ⟨b, ⟨ρ, ⟨w, hw, hw'⟩, rfl⟩, rfl⟩
    refine ⟨ρ ^ p, ⟨w ^ p, ?_, ?_⟩, ?_⟩
    · rw [← h]; exact ⟨w, hw, rfl⟩
    · rw [map_pow, map_pow, hw']
    · rw [map_pow, powMonoidHom_apply]

theorem artinImage_le_of_conductor_le (hη : Continuous η) [FiniteDimensional K (charTower η 2)]
    [IsAbelianGalois K (charTower η 2)] {n : ℕ} (hn : conductor (charTower η 2) ≤ n) :
    artinImage K η n ≤ unitsOneAdd p 2 := by
  rintro _ ⟨ρ, hρ, rfl⟩
  have h1 := (restrictNormalHom_mem_upperRamificationGroup_iff hη 2 n ρ).2
    (Subgroup.mem_sup_left ⟨ρ, hρ, rfl⟩)
  rw [(upperRamificationGroup_natCast_eq_bot_iff (charTower η 2) n).2 hn, Subgroup.mem_bot] at h1
  exact (restrictNormalHom_charTower_eq_one_iff hη 2 ρ).1 h1

end CFT

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open GroundTheory.LocalField ValuativeRel IsLocalRing

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Powers

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem natCast_prime_mem_valBall : (p : K) ∈ valBall K (absRamificationIndex K) := by
  rw [mem_valBall, normalizedValuation_natCast_prime p]

theorem div_natCast_prime_mem_valBall {a : ℤ} {x : K}
    (hx : x ∈ valBall K (a + absRamificationIndex K)) : x / p ∈ valBall K a := by
  have h := div_natCast_mem_valBall p hx hp.out.ne_zero
  rw [padicValNat_self, Nat.cast_one, mul_one, add_sub_cancel_right] at h
  exact h

theorem map_pow_unitFiltrationUnits {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  set e := absRamificationIndex K
  have hn1 : 1 ≤ n := one_le_of_lt_sub_one_mul_nat p hn
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have hn' : (e : ℤ) < (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) := by
    have : (p - 1 : ℤ) * n ≤ (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)
    omega
  have hne : (n : ℤ) + e = ((n + e : ℕ) : ℤ) := by push_cast; ring

  have hlogpow : ∀ u : unitFiltrationUnits K n,
      logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) =
        p * logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := by
    intro u
    have h := map_nsmul (logValBallHom p n hn) p (Additive.ofMul u)
    have h' := congrArg Subtype.val h
    rw [← ofMul_pow] at h'
    rw [coe_logValBallHom] at h'
    simpa [coe_logValBallHom, nsmul_eq_mul] using h'
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    set U : unitFiltrationUnits K n := ⟨u, hu⟩
    have hU : ((U ^ p : unitFiltrationUnits K n) : Kˣ) = powMonoidHom p u := rfl

    have hlog : logSeries ((((U ^ p : unitFiltrationUnits K n) : Kˣ) : K) - 1) ∈
        valBall K ((n + e : ℕ) : ℤ) := by
      rw [hlogpow U, ← hne, add_comm]
      exact mul_mem_valBall (natCast_prime_mem_valBall p)
        (logSeries_mem_valBall p (sub_one_mem_valBall_of_mem hn1 U) hn)
    have hexp := expSeries_logSeries p hn (U ^ p)
    have hmem := expSeries_sub_one_mem p hlog hn'
    rw [hexp] at hmem
    rw [← hU]
    exact (mem_unitFiltrationUnits_iff_valBall (by omega)).2 hmem
  · intro w hw
    have hwn : w ∈ unitFiltrationUnits K n := unitFiltrationUnits_antitone (by omega) hw
    set W : unitFiltrationUnits K n := ⟨w, hwn⟩
    have hy : logSeries (((w : Kˣ) : K) - 1) ∈ valBall K (n + e) := by
      rw [hne]
      exact logSeries_mem_valBall p ((mem_unitFiltrationUnits_iff_valBall (by omega)).1 hw) hn'
    have hz : logSeries (((w : Kˣ) : K) - 1) / p ∈ valBall K n := div_natCast_prime_mem_valBall p hy
    set u := expUnit p n hn ⟨_, hz⟩
    refine ⟨(u : Kˣ), u.2, ?_⟩
    have hinj := logValBallHom_injective p n hn
    have key : logValBallHom p n hn (Additive.ofMul (u ^ p)) =
        logValBallHom p n hn (Additive.ofMul W) := by
      apply Subtype.ext
      rw [coe_logValBallHom, coe_logValBallHom]
      change logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) = _
      rw [hlogpow u]
      have hu := congrArg Subtype.val (logValBallHom_expUnit p n hn ⟨_, hz⟩)
      rw [coe_logValBallHom, toMul_ofMul] at hu
      have hu' : logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) =
          logSeries (((w : Kˣ) : K) - 1) / p := hu
      rw [hu', toMul_ofMul]
      have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
      field_simp
      rfl
    have := congrArg (fun v => ((Additive.toMul v : unitFiltrationUnits K n) : Kˣ)) (hinj key)
    exact this

theorem exists_map_pow_unitFiltrationUnits :
    ∃ n₀, ∀ n ≥ n₀, (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  refine ⟨absRamificationIndex K + 1, fun n hn => map_pow_unitFiltrationUnits p ?_⟩
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have : (n : ℤ) ≤ (p - 1 : ℤ) * n := le_mul_of_one_le_left (by omega) hp1
  omega

end Powers

section Residue

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

omit hp in

theorem not_dvd_card_residueField_sub_one : ¬ p ∣ Nat.card 𝓀[K] - 1 := by
  intro h
  apply natCast_card_residueField_sub_one_ne_zero K
  exact (CharP.cast_eq_zero_iff 𝓀[K] p _).2 h

theorem pow_card_sub_one_mem_unitFiltration (v : 𝒪[K]ˣ) :
    v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 := by
  have h := pow_mem (unitsMulInvTeichmuller_mem v) (Nat.card 𝓀[K] - 1)
  rwa [mul_pow, inv_pow, teichmuller_pow_card_sub_one, inv_one, mul_one] at h

theorem pow_prime_pow_mem_unitFiltrationUnits {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 1) (n : ℕ) :
    x ^ p ^ n ∈ unitFiltrationUnits K (n + 1) := by
  have h := nsmul_prime_pow_mem_principalFiltration p
    (u := Additive.ofMul (⟨x, hx⟩ : unitFiltrationUnits K 1))
    (by rw [principalFiltration_zero]; exact AddSubgroup.mem_top _) n
  rw [zero_add, mem_principalFiltration, toMul_nsmul, toMul_ofMul] at h
  rw [mem_unitFiltrationUnits_iff_valBall (by omega)]
  exact_mod_cast h

theorem exists_pow_mem_unitFiltrationUnits (n : ℕ) :
    ∃ c j : ℕ, ¬ p ∣ c ∧ ∀ u ∈ unitFiltrationUnits K 0, u ^ (c * p ^ j) ∈ unitFiltrationUnits K n := by
  refine ⟨Nat.card 𝓀[K] - 1, n, not_dvd_card_residueField_sub_one p, fun u hu => ?_⟩
  obtain ⟨v, -, rfl⟩ := hu
  have h1 : unitsIncl K (v ^ (Nat.card 𝓀[K] - 1)) ∈ unitFiltrationUnits K 1 :=
    ⟨_, pow_card_sub_one_mem_unitFiltration v, rfl⟩
  have h2 := pow_prime_pow_mem_unitFiltrationUnits p h1 n
  rw [map_pow, ← pow_mul] at h2
  exact unitFiltrationUnits_antitone (by omega) h2

end Residue

section Norm

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
  [Algebra.IsAlgebraic K Ω]

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem nrm_natCast_prime_eq :
    nrm K (p : Ω) = baseUnifNrm K Ω ^ absRamificationIndex K := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hv : normalizedValuation K (p : K) =
      normalizedValuation K (((baseUnif K : 𝒪[K]) : K) ^ absRamificationIndex K) := by
    rw [normalizedValuation_natCast_prime p, map_pow, baseUnif, normalizedValuation_uniformizer hirr,
      ← WithZero.exp_nsmul]
    simp
  have key : ∀ a b : K, normalizedValuation K a = normalizedValuation K b →
      nrm K (algebraMap K Ω a) = nrm K (algebraMap K Ω b) := by
    intro a b hab
    have h1 : a ≤ᵥ b := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.le)
    have h2 : b ≤ᵥ a := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.ge)
    exact le_antisymm ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h1))
      ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle _ _).2 h2))
  have h := key _ _ hv
  rw [map_natCast] at h
  rw [h, map_pow, nrm_pow]
  rfl

end Norm

section ResidueChar

variable (p : ℕ) [hp : Fact p.Prime]

theorem charP_residueField_of_valuativeExtension (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra ℚ_[p] F]
    [ValuativeExtension ℚ_[p] F] : CharP 𝓀[F] p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hq : ¬ ((1 : ℚ_[p]) ≤ᵥ (p : ℚ_[p])) := by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
      GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one, Padic.norm_p]
    exact not_le.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hF : ¬ ((1 : F) ≤ᵥ (p : F)) := by
    intro h
    apply hq
    rw [← ValuativeExtension.vle_iff_vle (A := ℚ_[p]) (B := F), map_one, map_natCast]
    exact h
  have e : (((p : 𝒪[F]) : F)) = (p : F) := by push_cast; rfl
  rw [e, ← map_one (valuation F)]
  exact lt_of_not_ge fun h => hF ((Valuation.vle_iff_le (valuation F)).2 h)

end ResidueChar

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K] {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

instance valuativeExtension_charTower (k : ℕ) : ValuativeExtension K (charTower η k) :=
  GroundTheory.LocalField.intermediateField_valuativeExtension_left _

variable (K η) in

def artinLevel (n : ℕ) : ℕ := sInf {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}

theorem artinLevel_spec {n : ℕ} (h : artinImage K η n ≠ ⊥) :
    artinImage K η n ≤ unitsOneAdd p (artinLevel K η n) ∧
      ∃ a ∈ artinImage K η n, a ∉ unitsOneAdd p (artinLevel K η n + 1) := by
  have hne : {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}.Nonempty := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    obtain ⟨s, -, hs'⟩ := exists_level (p := p) (a := (a : ℤ_[p]ˣ)) (fun h' => ha1 (Subtype.ext h'))
    exact ⟨s, fun hle => hs' (hle a.2)⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_eq_succ_pred (artinLevel K η n) with h0 | h0
    · rw [h0, unitsOneAdd_zero]; exact le_top
    · have hlt : Nat.pred (artinLevel K η n) < artinLevel K η n := by omega
      have := Nat.notMem_of_lt_sInf hlt
      simp only [Set.mem_ofPred_eq, not_not] at this
      rw [h0]
      exact this
  · have hmem' : ¬ artinImage K η n ≤ unitsOneAdd p (artinLevel K η n + 1) := hmem
    exact SetLike.not_le_iff_exists.1 hmem'

theorem artinLevel_mono (hA : ∀ n, artinImage K η n ≠ ⊥) : Monotone (artinLevel K η) := by
  intro n n' hnn'
  obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n')
  have h1 := (artinLevel_spec (hA n)).1 (artinImage_antitone η hnn' ha)
  by_contra hlt
  push Not at hlt
  exact ha' (unitsOneAdd_antitone (by omega) h1)

theorem artinLevel_add (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥) {n e : ℕ}
    (h2 : 2 ≤ artinLevel K η n)
    (hpow : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinLevel K η (n + e) = artinLevel K η n + 1 := by
  have heq := artinImage_add_eq_map_pow hη hpow
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n)
  obtain ⟨hle', b, hb, hb'⟩ := artinLevel_spec (hA (n + e))
  apply le_antisymm
  ·
    have hap : a ^ p ∈ artinImage K η (n + e) := by rw [heq]; exact ⟨a, ha, rfl⟩
    have hap' : a ^ p ∉ unitsOneAdd p (artinLevel K η n + 2) := fun h =>
      ha' (((pow_prime_mem_iff h2 (hle ha)).2).1 h)
    by_contra hlt
    push Not at hlt
    exact hap' (unitsOneAdd_antitone (by omega) (hle' hap))
  ·
    have hle2 : artinImage K η (n + e) ≤ unitsOneAdd p (artinLevel K η n + 1) := by
      rw [heq]
      rintro _ ⟨c, hc, rfl⟩
      exact (pow_prime_mem_iff h2 (hle hc)).1
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) (hle2 hb))

theorem artinImage_sup_unitsOneAdd {n : ℕ} (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    (k : ℕ) : artinImage K η n ⊔ unitsOneAdd p k = unitsOneAdd p (min (artinLevel K η n) k) := by
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec hA
  apply le_antisymm
  · exact sup_le (hle.trans (unitsOneAdd_antitone (min_le_left _ _)))
      (unitsOneAdd_antitone (min_le_right _ _))
  · intro b hb
    rcases le_total k (artinLevel K η n) with hk | hk
    · rw [min_eq_right hk] at hb
      exact Subgroup.mem_sup_right hb
    · rw [min_eq_left hk] at hb
      obtain ⟨j, hj⟩ := exists_mul_inv_pow_mem h2 (hle ha) ha' hb k
      have e : b = a ^ j * (b * (a ^ j)⁻¹) := by rw [mul_comm, inv_mul_cancel_right]
      rw [e]
      exact Subgroup.mul_mem_sup (pow_mem ha j) hj

theorem restrictNormalHom_mem_upperRamificationGroup_iff_level (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ unitsOneAdd p (min (artinLevel K η n) k) := by
  rw [restrictNormalHom_mem_upperRamificationGroup_iff hη, artinImage_sup_unitsOneAdd hA h2]

theorem upperRamificationGroup_charTower_eq_map (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    upperRamificationGroup K (charTower η k) n =
      (charTowerGal η (min (artinLevel K η n) k)).map
        (AlgEquiv.restrictNormalHom (charTower η k)) := by
  ext g
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) g
  rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη hA h2]
  constructor
  · intro h
    exact ⟨σ, h, rfl⟩
  · rintro ⟨σ', hσ', heq⟩
    have h1 : AlgEquiv.restrictNormalHom (charTower η k) (σ'⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have h2' := (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
    have e : η σ = η σ' * η (σ'⁻¹ * σ) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    rw [e]
    exact mul_mem hσ' (unitsOneAdd_antitone (min_le_right _ _) h2')

omit [FiniteDimensional ℚ_[p] K] in

theorem relIndex_charTowerGal {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t) {a : ℤ_[p]ˣ} (haR : a ∈ η.range)
    (ha : a ∈ unitsOneAdd p s) (ha' : a ∉ unitsOneAdd p (s + 1)) :
    (charTowerGal η t).relIndex (charTowerGal η s) = p ^ (t - s) := by
  rw [charTowerGal, charTowerGal, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    ← Subgroup.inf_relIndex_right, inf_comm η.range, ← inf_assoc,
    inf_eq_left.2 (unitsOneAdd_antitone hst)]
  have h := relIndex_unitsOneAdd_inf hs η.range haR ha ha' (t - s)
  rwa [Nat.add_sub_cancel' hst] at h

theorem relIndex_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' j : ℕ} (hn'j : n' ≤ j) (h2 : 2 ≤ artinLevel K η n')
    (hjk : artinLevel K η j ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    (upperRamificationGroup K (charTower η k) j).relIndex
        (upperRamificationGroup K (charTower η k) n') =
      p ^ (artinLevel K η j - artinLevel K η n') := by
  have hmono := artinLevel_mono hA hn'j
  have h2j : 2 ≤ artinLevel K η j := h2.trans hmono
  rw [upperRamificationGroup_charTower_eq_map hη (hA j) h2j,
    upperRamificationGroup_charTower_eq_map hη (hA n') h2, Subgroup.relIndex_map_map,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη, min_eq_left hjk,
    min_eq_left (hmono.trans hjk), sup_eq_left.2 (charTowerGal_antitone η hjk),
    sup_eq_left.2 (charTowerGal_antitone η (hmono.trans hjk))]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hmono (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem card_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' : ℕ} (h2 : 2 ≤ artinLevel K η n')
    (hk : artinLevel K η n' ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    Nat.card (upperRamificationGroup K (charTower η k) n') = p ^ (k - artinLevel K η n') := by
  rw [upperRamificationGroup_charTower_eq_map hη (hA n') h2, min_eq_left hk,
    ← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_comap, MonoidHom.comap_bot,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hk (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem integral_eq_sum_of_eq_ceil {f : ℝ → ℝ} (hf : ∀ w, f w = f (⌈w⌉ : ℝ))
    (hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) (N : ℕ) :
    ∫ w in (0 : ℝ)..N, f w = ∑ j ∈ Finset.Ioc 0 N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 N) (hint N ((N + 1 : ℕ) : ℝ))]
    congr 1
    have hc : ∫ w in (N : ℝ)..((N + 1 : ℕ) : ℝ), f w =
        ∫ _ in (N : ℝ)..((N + 1 : ℕ) : ℝ), f ((N + 1 : ℕ) : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun w hw => ?_)
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
      rw [Set.uIoc_of_le hle] at hw
      rw [hf w]
      congr 1
      have : ⌈w⌉ = ((N + 1 : ℕ) : ℤ) := by
        rw [Int.ceil_eq_iff]
        push_cast at hw ⊢
        constructor <;> linarith [hw.1, hw.2]
      rw [this]
      norm_cast
    rw [Nat.cast_succ] at hc ⊢
    rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    ring

theorem sum_zpow_block_le (μ : ℕ → ℕ) (hμ : Monotone μ) {e n₀ : ℕ}
    (hper : ∀ n, n₀ ≤ n → μ (n + e) = μ n + 1) {N k : ℕ} (hN : k + 1 ≤ μ (N + 1)) {b : ℝ}
    (hb : 1 ≤ b) : ∀ q : ℕ, n₀ + e * q ≤ N →
      (e : ℝ) * ∑ i ∈ Finset.range q, b ^ ((k : ℤ) - i) ≤
        ∑ j ∈ Finset.Ioc (N - e * q) N, b ^ (μ j : ℤ)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [show e * (q + 1) = e * q + e by ring] at hq ⊢
    have ih := sum_zpow_block_le μ hμ hper hN hb q (by omega)

    have hiter : ∀ i j, n₀ ≤ j → μ (j + e * i) = μ j + i := by
      intro i
      induction i with
      | zero => simp
      | succ i ihi =>
        intro j hj
        rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ihi j hj, add_assoc]
    have hsplit : Finset.Ioc (N - (e * q + e)) N =
        Finset.Ioc (N - (e * q + e)) (N - e * q) ∪ Finset.Ioc (N - e * q) N := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
    have hdisj : Disjoint (Finset.Ioc (N - (e * q + e)) (N - e * q)) (Finset.Ioc (N - e * q) N) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_range_succ, mul_add, add_comm]
    refine add_le_add ?_ ih

    have hcard : (Finset.Ioc (N - (e * q + e)) (N - e * q)).card = e := by
      rw [Nat.card_Ioc]; omega
    calc (e : ℝ) * b ^ ((k : ℤ) - q)
        = ∑ _j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q), b ^ ((k : ℤ) - q) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q), b ^ (μ j : ℤ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_Ioc] at hj
          refine zpow_le_zpow_right₀ hb ?_

          have h1 : μ (j + e * q) = μ j + q := hiter q j (by omega)
          have h2 : k + 1 ≤ μ (j + e * q + e) := hN.trans (hμ (by omega))
          rw [hper _ (by omega), h1] at h2
          omega

theorem artinLevel_add_mul {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) (i : ℕ) :
    artinLevel K η (n₀ + e * i) = artinLevel K η n₀ + i := by
  induction i with
  | zero => simp
  | succ i ih => rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ih, add_assoc]

theorem exists_last_artinLevel_le (hA : ∀ n, artinImage K η n ≠ ⊥) {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) {k : ℕ}
    (hk : artinLevel K η n₀ ≤ k) :
    ∃ N, artinLevel K η N ≤ k ∧ k + 1 ≤ artinLevel K η (N + 1) ∧
      n₀ + e * (k - artinLevel K η n₀) ≤ N := by
  have hmono := artinLevel_mono hA
  have hiter := artinLevel_add_mul hper
  have hex : ∃ n, k < artinLevel K η n :=
    ⟨n₀ + e * (k - artinLevel K η n₀ + 1), by rw [hiter]; omega⟩
  classical
  have hF : k < artinLevel K η (Nat.find hex) := Nat.find_spec hex
  have hF0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hF
    have := hmono (Nat.zero_le n₀)
    omega
  obtain ⟨N, hNF⟩ : ∃ N, N + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨N, ?_, by rw [hNF]; exact hF, ?_⟩
  · have := Nat.find_min hex (show N < Nat.find hex by omega)
    omega
  · by_contra hlt
    push Not at hlt
    have := hmono (show Nat.find hex ≤ n₀ + e * (k - artinLevel K η n₀) by omega)
    rw [hiter] at this
    omega

theorem le_herbrandPsi_div_ramificationIndex (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k N : ℕ} (hNk : artinLevel K η N ≤ k) (hN1 : k + 1 ≤ artinLevel K η (N + 1))
    (hNq : n₀ + e * (k - artinLevel K η n₀) ≤ N)
    [FiniteDimensional K (charTower η (k + 1))] [IsAbelianGalois K (charTower η (k + 1))] :
    (e : ℝ) / p * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) ≤
      herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1)) := by
  have hmono := artinLevel_mono hA
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have hsk : artinLevel K η n' ≤ k := (hmono hn'N).trans hNk

  have hn'0 : upperRamificationGroup K (charTower η (k + 1)) n' ≤
      lowerRamificationGroup K (charTower η (k + 1)) 0 := by
    rw [← upperRamificationGroup_zero]
    exact upperRamificationGroup_antitone K _ (Nat.cast_nonneg n')
  obtain ⟨c, hc⟩ : ∃ c, (upperRamificationGroup K (charTower η (k + 1)) n').relIndex
      (lowerRamificationGroup K (charTower η (k + 1)) 0) = c := ⟨_, rfl⟩
  have hE : ramificationIndex K (charTower η (k + 1)) = c * p ^ (k + 1 - artinLevel K η n') := by
    rw [← card_lowerRamificationGroup_zero, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_mul_relIndex _ _ _ bot_le hn'0, Subgroup.relIndex_bot_left,
      card_upperRamificationGroup_charTower hη hA h2 (by omega), hc, mul_comm]

  have hψsum : herbrandPsi K (charTower η (k + 1)) N =
      ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) := by
    rw [herbrandPsi_eq_integral (Nat.cast_nonneg N)]
    refine integral_eq_sum_of_eq_ceil (fun w => ?_) (fun a b => intervalIntegrable_upperIndex a b) N
    simp only [upperIndex]
    rw [upperRamificationGroup_eq_ceil (L := charTower η (k + 1)) w]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hterm : ∀ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
      (upperIndex K (charTower η (k + 1)) j : ℝ) =
        (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) * (p : ℝ) ^ (artinLevel K η j : ℤ) := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hn'j : n' ≤ j := by omega
    have hjk : artinLevel K η j ≤ k + 1 := by have := hmono hj.2; omega
    have hsj : artinLevel K η n' ≤ artinLevel K η j := hmono hn'j
    rw [upperIndex, ← Subgroup.relIndex_mul_relIndex _ _ _
      (upperRamificationGroup_antitone K _ (by exact_mod_cast hn'j)) hn'0,
      relIndex_upperRamificationGroup_charTower hη hA hn'j h2 hjk, hc]
    push_cast
    rw [← zpow_natCast, Nat.cast_sub hsj, zpow_sub₀ hp0.ne', zpow_neg]
    ring
  have hψlow : (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
      ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i)) ≤
        herbrandPsi K (charTower η (k + 1)) N := by
    rw [hψsum]
    calc (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
          ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i))
        ≤ (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
            ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N, (p : ℝ) ^ (artinLevel K η j : ℤ) :=
          mul_le_mul_of_nonneg_left
            (sum_zpow_block_le (artinLevel K η) hmono hper hN1 hp1 _ hNq) (by positivity)
      _ = ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
            (upperIndex K (charTower η (k + 1)) j : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j hj => (hterm j hj).symm
      _ ≤ ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
            (fun _ _ _ => Nat.cast_nonneg _)
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  rw [le_div_iff₀ hE0]
  refine le_trans (le_of_eq ?_) hψlow
  rw [hE]
  push_cast
  have hsum : ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i) =
      (p : ℝ) ^ (k : ℤ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zpow_add₀ hp0.ne']
    ring_nf
  rw [hsum, ← zpow_natCast (p : ℝ) (k + 1 - artinLevel K η n'), Nat.cast_sub (by omega),
    zpow_sub₀ hp0.ne', zpow_neg]
  push_cast
  rw [zpow_add₀ hp0.ne', zpow_one]
  field_simp

theorem nrm_sub_le_of_mem_unitsOneAdd (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k : ℕ} (hk : artinLevel K η n₀ ≤ k) {σ : Gal(PadicAlgCl p/K)} (hσ : η σ ∈ unitsOneAdd p k)
    {y : PadicAlgCl p} (hy : y ∈ charTower η (k + 1)) :
    nrm K (σ y - y) ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
      ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) * nrm K y := by
  have : FiniteDimensional K (charTower η (k + 1)) := finiteDimensional_charTower hη (k + 1)
  have : IsAbelianGalois K (charTower η (k + 1)) := isAbelianGalois_charTower hη (k + 1)
  have hmono := artinLevel_mono hA
  obtain ⟨N, hNk, hN1, hNq⟩ := exists_last_artinLevel_le hA hper hk
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have h2N : 2 ≤ artinLevel K η N := h2.trans (hmono hn'N)
  have hσN : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      upperRamificationGroup K (charTower η (k + 1)) N := by
    rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη (hA N) h2N,
      min_eq_left (by omega)]
    exact unitsOneAdd_antitone hNk hσ
  have hψ0 : 0 ≤ herbrandPsi K (charTower η (k + 1)) N := by
    rw [← herbrandPsi_zero (K := K) (L := charTower η (k + 1))]
    exact herbrandPsi_strictMono.monotone (Nat.cast_nonneg N)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = ⌈herbrandPsi K (charTower η (k + 1)) N⌉ :=
    ⟨_, Int.toNat_of_nonneg (Int.ceil_nonneg hψ0)⟩
  have hmem : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      lowerRamificationGroup K (charTower η (k + 1)) (i : ℤ) := by
    rw [hi]
    exact hσN
  have h1 := nrm_sub_le_of_mem_lowerRamificationGroup (charTower η (k + 1)) hmem ⟨y, hy⟩
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  have hX := le_herbrandPsi_div_ramificationIndex hη hA hn' h2 hper hNk hN1 hNq
  have hu0 : 0 < unifNrm (charTower η (k + 1)) := unifNrm_pos _
  have hu1 : unifNrm (charTower η (k + 1)) < 1 := unifNrm_lt_one _
  have huE : unifNrm (charTower η (k + 1)) ^ ramificationIndex K (charTower η (k + 1)) =
      baseUnifNrm K (PadicAlgCl p) := unifNrm_pow_ramificationIndex _
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  calc unifNrm (charTower η (k + 1)) ^ i = unifNrm (charTower η (k + 1)) ^ (i : ℝ) :=
        (Real.rpow_natCast _ i).symm
    _ ≤ unifNrm (charTower η (k + 1)) ^ herbrandPsi K (charTower η (k + 1)) N := by
        refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1.le ?_
        have : ((⌈herbrandPsi K (charTower η (k + 1)) N⌉ : ℤ) : ℝ) = (i : ℝ) := by
          rw [← hi]; norm_cast
        rw [← this]
        exact Int.le_ceil _
    _ = baseUnifNrm K (PadicAlgCl p) ^
          (herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1))) := by
        rw [← huE, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
        congr 1
        field_simp
    _ ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
          ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) :=
        Real.rpow_le_rpow_of_exponent_ge baseUnifNrm_pos
          (by rw [← huE]; exact pow_le_one₀ hu0.le hu1.le) hX

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel Polynomial Module

theorem sum_range_X_add_one_pow (n : ℕ) :
    ∑ j ∈ Finset.range n, ((X : ℤ[X]) + 1) ^ j =
      ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℤ[X]) * X ^ i := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℤ[X]) ≠ 0)
  have h1 : (X : ℤ[X]) * ∑ j ∈ Finset.range n, (X + 1) ^ j = (X + 1) ^ n - 1 := by
    have := geom_sum_mul ((X : ℤ[X]) + 1) n
    rw [add_sub_cancel_right] at this
    rw [mul_comm, this]
  have h2 : (X + 1 : ℤ[X]) ^ n - 1 =
      ∑ i ∈ Finset.range n, (X : ℤ[X]) ^ (i + 1) * (n.choose (i + 1) : ℤ[X]) := by
    rw [add_pow, Finset.sum_range_succ']
    simp
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K]

def galOver (M : IntermediateField K (PadicAlgCl p)) (σ : Gal(PadicAlgCl p/K))
    (hσ : σ ∈ M.fixingSubgroup) : PadicAlgCl p ≃ₐ[M] PadicAlgCl p :=
  { σ.toRingEquiv with
    commutes' := fun m => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ m m.2 }

omit [FiniteDimensional ℚ_[p] K] in
theorem galOver_apply (M : IntermediateField K (PadicAlgCl p)) (σ : Gal(PadicAlgCl p/K))
    (hσ : σ ∈ M.fixingSubgroup) (y : PadicAlgCl p) : galOver M σ hσ y = σ y := rfl

variable (M M' : IntermediateField K (PadicAlgCl p)) (hMM' : M ≤ M') [FiniteDimensional K M']
  {τ : Gal(PadicAlgCl p/K)} (hτM : τ ∈ M.fixingSubgroup)
  (hτp : τ ^ p ∈ M'.fixingSubgroup) (hτ1 : τ ∉ M'.fixingSubgroup)
  (hgen : ∀ σ ∈ M.fixingSubgroup, ∃ j : ℕ, ∀ y ∈ M', σ y = (τ ^ j) y)

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hτ1 in

theorem pow_mem_fixingSubgroup_iff (m : ℕ) : τ ^ m ∈ M'.fixingSubgroup ↔ p ∣ m := by
  constructor
  · intro hm
    by_contra hdvd
    have hcop : Nat.Coprime m p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hdvd))
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop.gcd_eq_one, Nat.cast_one] at hg
    have : τ = (τ ^ m) ^ (Nat.gcdA m p) * (τ ^ p) ^ (Nat.gcdB m p) := by
      rw [← zpow_natCast, ← zpow_natCast τ p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
    exact hτ1 (this ▸ mul_mem (zpow_mem hm _) (zpow_mem hτp _))
  · rintro ⟨c, rfl⟩
    rw [pow_mul]
    exact pow_mem hτp c

section Embeddings

variable {M M'} {hMM'}

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτM in
theorem pow_mem_fixingSubgroup_base (j : ℕ) : τ ^ j ∈ M.fixingSubgroup := pow_mem hτM j

variable (hMM') in

def stepEmb (hτM : τ ∈ M.fixingSubgroup) (j : ℕ) :
    IntermediateField.extendScalars hMM' →ₐ[M] PadicAlgCl p :=
  (galOver M (τ ^ j) (pow_mem hτM j)).toAlgHom.comp (IntermediateField.extendScalars hMM').val

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
theorem stepEmb_apply (j : ℕ) (y : IntermediateField.extendScalars hMM') :
    stepEmb hMM' hτM j y = (τ ^ j) (y : PadicAlgCl p) := rfl

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hτ1 in
theorem stepEmb_injective {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : stepEmb hMM' hτM i = stepEmb hMM' hτM j) : i = j := by
  have key : ∀ {a b : ℕ}, a ≤ b → b < p → stepEmb hMM' hτM a = stepEmb hMM' hτM b → a = b := by
    intro a b hab hb h
    have hfix : τ ^ (b - a) ∈ M'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 := congrArg (fun φ => φ (⟨y, hy⟩ : IntermediateField.extendScalars hMM')) h
      simp only [stepEmb_apply] at h1
      have e : τ ^ b = τ ^ a * τ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
      rw [e, AlgEquiv.mul_apply] at h1
      exact ((τ ^ a).injective h1).symm
    have hdvd := (pow_mem_fixingSubgroup_iff M' hτp hτ1 (b - a)).1 hfix
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  rcases le_total i j with hij | hji
  · exact key hij hj h
  · exact (key hji hi h.symm).symm

instance isAlgClosure_padicAlgCl_over (E : IntermediateField K (PadicAlgCl p)) :
    IsAlgClosure E (PadicAlgCl p) :=
  haveI : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) E⟩

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hgen in
theorem stepEmb_surjective (φ : IntermediateField.extendScalars hMM' →ₐ[M] PadicAlgCl p) :
    ∃ j < p, stepEmb hMM' hτM j = φ := by
  set φ' := φ.liftNormal (PadicAlgCl p)
  have hbij : Function.Bijective φ' := Algebra.IsAlgebraic.algHom_bijective φ'
  let σ : Gal(PadicAlgCl p/K) := (AlgEquiv.ofBijective φ' hbij).restrictScalars K
  have hσ : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro m hm
    change φ' (algebraMap M (PadicAlgCl p) ⟨m, hm⟩) = m
    rw [AlgHom.commutes]
    rfl
  obtain ⟨j, hj⟩ := hgen σ hσ
  have hp0 : 0 < p := hp.out.pos
  refine ⟨j % p, Nat.mod_lt _ hp0, ?_⟩
  ext y
  rw [stepEmb_apply]
  have h1 : φ y = φ' (y : PadicAlgCl p) := by
    have := AlgHom.liftNormal_commutes φ (PadicAlgCl p) y
    exact this.symm
  rw [h1]
  change (τ ^ (j % p)) (y : PadicAlgCl p) = σ y
  rw [hj y y.2]
  have e : τ ^ j = τ ^ (j % p) * (τ ^ p) ^ (j / p) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e, AlgEquiv.mul_apply]
  congr 1
  exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (pow_mem hτp _) y y.2).symm

end Embeddings

variable {M M'} {hMM'}

omit [FiniteDimensional ℚ_[p] K] in
theorem finiteDimensional_extendScalars_of_le :
    FiniteDimensional M (IntermediateField.extendScalars hMM') := by
  apply Module.finite_of_finrank_pos
  have h : 0 < Module.finrank K M' := Module.finrank_pos
  rw [finrank_eq_mul_finrank_extendScalars hMM'] at h
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h

include hMM' hτM hτp hτ1 hgen in
omit [FiniteDimensional ℚ_[p] K] in

theorem natCast_mul_normTrace_eq_sum {y : PadicAlgCl p} (hy : y ∈ M') :
    (p : PadicAlgCl p) * normTrace M y = ∑ j ∈ Finset.range p, (τ ^ j) y := by
  have := finiteDimensional_extendScalars_of_le (M := M) (M' := M') (hMM' := hMM')
  set E := IntermediateField.extendScalars hMM'
  let e : Fin p → (E →ₐ[M] PadicAlgCl p) := fun j => stepEmb hMM' hτM j.1
  have he : Function.Bijective e := by
    refine ⟨fun i j h => Fin.ext (stepEmb_injective hτM hτp hτ1 i.2 j.2 h), fun φ => ?_⟩
    obtain ⟨j, hj, hφ⟩ := stepEmb_surjective hτM hτp hgen φ
    exact ⟨⟨j, hj⟩, hφ⟩
  have hcard : Module.finrank M E = p := by
    rw [← AlgHom.card M E (PadicAlgCl p), ← Fintype.card_of_bijective he, Fintype.card_fin]
  set y' : E := ⟨y, hy⟩
  have hyy : y = algebraMap E (PadicAlgCl p) y' := rfl
  have htr := trace_eq_sum_embeddings (K := M) (L := E) (PadicAlgCl p) (x := y')
  have hsum : ∑ σ : E →ₐ[M] PadicAlgCl p, σ y' = ∑ j ∈ Finset.range p, (τ ^ j) y := by
    rw [← Fintype.sum_bijective e he (fun j => e j y') (fun σ => σ y') (fun _ => rfl),
      ← Fin.sum_univ_eq_sum_range (fun j => (τ ^ j) y)]
    rfl
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [normTrace, hyy, normTraceF_eq_trace_div M E y', hcard, map_div₀, htr, hsum, map_natCast,
    mul_div_cancel₀ _ hp0]
  rfl

omit [FiniteDimensional ℚ_[p] K] in

theorem sum_range_pow_apply_eq (τ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    ∑ j ∈ Finset.range n, (τ ^ j) y = ∑ i ∈ Finset.range n, (n.choose (i + 1) : PadicAlgCl p) *
      (((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y := by
  set T : Module.End K (PadicAlgCl p) := τ.toLinearMap
  set D := T - 1
  have hT : ∀ (j : ℕ) (z : PadicAlgCl p), (T ^ j) z = (τ ^ j) z := by
    intro j
    induction j with
    | zero => intro z; rfl
    | succ j ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, pow_succ, AlgEquiv.mul_apply, ih]
      rfl
  have key := congrArg (fun P => (Polynomial.aeval D P) y) (sum_range_X_add_one_pow n)
  simp only [map_sum, map_pow, map_add, aeval_X, map_one, map_mul, map_natCast] at key
  rw [LinearMap.sum_apply, LinearMap.sum_apply] at key
  simp only [Module.End.mul_apply, Module.End.natCast_apply, nsmul_eq_mul] at key
  rw [sub_add_cancel] at key
  rw [← key]
  exact Finset.sum_congr rfl fun j _ => (hT j y).symm

omit [FiniteDimensional K M'] in

theorem nrm_pow_sub_one_apply_le (τ : Gal(PadicAlgCl p/K)) (hτM' : ∀ z ∈ M', τ z ∈ M') {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ z ∈ M', nrm K (τ z - z) ≤ ρ * nrm K z) {y : PadicAlgCl p} (hy : y ∈ M') (i : ℕ) :
    (((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y ∈ M' ∧
      nrm K ((((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y) ≤ ρ ^ i * nrm K y := by
  induction i with
  | zero => simpa using hy
  | succ i ih =>
    set D : Module.End K (PadicAlgCl p) := τ.toLinearMap - 1
    have e : (D ^ (i + 1)) y = τ ((D ^ i) y) - (D ^ i) y := by
      rw [pow_succ', Module.End.mul_apply]
      rfl
    rw [e]
    refine ⟨sub_mem (hτM' _ ih.1) ih.1, ?_⟩
    calc nrm K (τ ((D ^ i) y) - (D ^ i) y) ≤ ρ * nrm K ((D ^ i) y) := hρ _ ih.1
      _ ≤ ρ * (ρ ^ i * nrm K y) := mul_le_mul_of_nonneg_left ih.2 hρ0
      _ = ρ ^ (i + 1) * nrm K y := by ring

include hMM' hτM hτp hτ1 hgen in

theorem nrm_normTrace_mul_le (hτM' : ∀ z ∈ M', τ z ∈ M') {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ z ∈ M', nrm K (τ z - z) ≤ ρ * nrm K z) {y : PadicAlgCl p} (hy : y ∈ M') :
    nrm K (normTrace M y) * nrm K (p : PadicAlgCl p) ≤
      max (nrm K (p : PadicAlgCl p)) (ρ ^ (p - 1)) * nrm K y := by
  have hsum := natCast_mul_normTrace_eq_sum (hMM' := hMM') hτM hτp hτ1 hgen hy
  rw [sum_range_pow_apply_eq] at hsum
  rw [mul_comm, ← nrm_mul, hsum]
  set C := max (nrm K (p : PadicAlgCl p)) (ρ ^ (p - 1)) * nrm K y
  have hC : 0 ≤ C := mul_nonneg (le_trans (nrm_nonneg _) (le_max_left _ _)) (nrm_nonneg _)
  refine nrm_sum_le hC fun i hi => ?_
  rw [Finset.mem_range] at hi
  obtain ⟨-, hDi⟩ := nrm_pow_sub_one_apply_le τ hτM' hρ0 hρ hy i
  rw [nrm_mul]
  have hρi : ρ ^ i ≤ 1 := pow_le_one₀ hρ0 hρ1
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (show i < p - 1 + 1 by omega)) with hlt | heq
  ·
    obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (by omega : i + 1 ≠ 0) (by omega : i + 1 < p)
    rw [hc, Nat.cast_mul, nrm_mul]
    have hc1 := nrm_natCast_le_one (K := K) (Ω := PadicAlgCl p) c
    have hp1 := nrm_natCast_le_one (K := K) (Ω := PadicAlgCl p) p
    calc nrm K (p : PadicAlgCl p) * nrm K (c : PadicAlgCl p) *
          nrm K ((((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y)
        ≤ nrm K (p : PadicAlgCl p) * 1 * (1 * nrm K y) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc1 (nrm_nonneg _))
            (hDi.trans (mul_le_mul_of_nonneg_right hρi (nrm_nonneg _))) (nrm_nonneg _)
            (by rw [mul_one]; exact nrm_nonneg _)
      _ ≤ C := by
          rw [one_mul, mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (nrm_nonneg _)
  ·
    have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, nrm_one, one_mul]
    rw [heq] at hDi
    rw [heq]
    exact hDi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (nrm_nonneg _))

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]

def inertiaGal (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    have hτy : ‖τ y‖ ≤ 1 := by rwa [norm_gal_apply]
    have e : (σ * τ) y - y = (σ (τ y) - τ y) + (τ y - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt ((PadicAlgCl.isNonarchimedean p) _ _) (max_lt (hσ _ hτy) (hτ y hy))
  inv_mem' := fun {σ} hσ y hy => by
    have e : σ (σ⁻¹ y - y) = -(σ y - y) := by
      rw [map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]; ring
    rw [← norm_gal_apply σ, e, norm_neg]
    exact hσ y hy

theorem mem_inertiaGal {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Gal(PadicAlgCl p/K)} :
    σ ∈ inertiaGal K ↔ ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1 := Iff.rfl

namespace SenTateChar

open SenTateChar

theorem exists_mem_inertiaGal_unitsOneAdd_two (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ) (hη : Continuous η)
    (hinf : (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Infinite) :
    ∃ τ ∈ inertiaGal K, η τ ∈ unitsOneAdd p 2 ∧ η τ ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hinf
  set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η
  have hU : IsOpen (U : Set Gal(PadicAlgCl p/K)) := (isOpen_unitsOneAdd 2).preimage hη
  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  classical

  let f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ := fun c =>
    if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩
  have h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ := ⟨τ, hτ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτ', hτ'U⟩ := h.choose_spec
  have hq : (h.choose)⁻¹ * τ ∈ U := QuotientGroup.eq.1 hτ'U
  have hI : (h.choose)⁻¹ * τ ∈ inertiaGal K := mul_mem (inv_mem hτ') hτ
  have h1 : η ((h.choose)⁻¹ * τ) = 1 := hne _ hI hq
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem eq_zero_of_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (M : ℕ → IntermediateField K (PadicAlgCl p)) (hM : Monotone M)
    [∀ k, FiniteDimensional K (M k)]
    (hstab : ∀ (σ : Gal(PadicAlgCl p/K)) (k : ℕ), ∀ y ∈ M k, σ y ∈ M k)
    (hker : ∀ σ : Gal(PadicAlgCl p/K), (∀ k, σ ∈ (M k).fixingSubgroup) → η σ = 1)
    (C : ℝ) (n₁ : ℕ)
    (hbound : ∀ n, n₁ ≤ n → ∀ m, ∀ y ∈ M m, ‖normTrace (M n) y‖ ≤ C * ‖y‖)
    (hgen : ∀ n, n₁ ≤ n → ∃ γ ∈ (M n).fixingSubgroup, η γ ≠ 1)
    {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  classical
  set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE
  have hdir : Directed (· ≤ ·) M := hM.directed_le
  have hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m := fun {y} hy => by
    have h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p)) :=
      (mem_restrictScalars _).1 hy
    rw [coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  have hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E := fun {m} {y} hy =>
    (mem_restrictScalars _).2 (le_iSup M m hy)

  have hxc : x ∈ closureInCp E := by
    have hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x := by
      intro σ hσ
      have h1 : η σ = 1 := hker σ fun k => by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
        exact fun y hy => hσ y (le_iSup M k hy)
      have := hx σ
      rwa [h1, Units.val_one, PadicInt.coe_one, map_one, one_mul] at this
    have h := fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed Ms)
    have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x} := hfixed
    rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
    exact hx'

  have hC1 : 1 ≤ C := by
    have h := hbound n₁ le_rfl n₁ 1 (one_mem _)
    rwa [normTrace_of_mem _ (one_mem _), norm_one, mul_one] at h
  have hC0 : 0 ≤ C := zero_le_one.trans hC1

  have hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z :=
    fun n y _ z _ => normTrace_add _ y z
  have hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖ := by
    intro n hn y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hbound n hn m y hm
  have hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E := by
    intro σ y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hME (hstab σ m y hm)
  have hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p),
      normTrace (M n) (σ y) = σ (normTrace (M n) y) := by
    intro σ n y
    refine normTrace_map_of_map_eq (M n) σ ?_ y
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hstab σ n z hz
    · intro z hz
      refine ⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩
      change σ (σ⁻¹ z) = z
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0 := by
    intro n hn
    set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]
    have : FiniteDimensional ℚ_[p] (M n) := Module.Finite.trans K (M n)
    have : FiniteDimensional ℚ_[p] k' := (inferInstance : FiniteDimensional ℚ_[p] (M n))
    have hkE : k' ≤ E := fun y hy => hME ((mem_restrictScalars _).1 hy)
    have hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k' := fun y _ =>
      (mem_restrictScalars _).2 (normTrace_mem _ y)
    have hfix : ∀ a ∈ k', normTrace (M n) a = a := fun a ha =>
      normTrace_of_mem _ ((mem_restrictScalars _).1 ha)
    have hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y :=
      fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y
    obtain ⟨γ, hγ, hγη⟩ := hgen n hn
    obtain ⟨b, hb, hbx⟩ := extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc

    set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])
    have hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) :=
      rfl
    have hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k' := k'.algebraMap_mem q
    have hγx : γ • x ∈ closureInCp E := smul_mem_closureInCp γ (hmapsE γ) hxc
    have key : extendToClosure E (normTrace (M n)) x =
        algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x := by
      conv_lhs => rw [← hx γ]
      rw [hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx,
        extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx,
        gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]
    have hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1 := by
      rw [Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]
      intro h
      apply hγη
      have h' : (η γ : ℤ_[p]) = 1 := Subtype.ext (by simpa [q] using h)
      exact Units.ext h'
    have h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)

  have hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := hmemE hy
    set m' := max m n₁
    have hym : y ∈ M m' := hM (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ closureInCp E := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ closureInCp E := sub_mem_closureInCp hyc hxc
    have hadd' := hadd m'
    have hbd' := hbd m' (le_max_right _ _)
    have h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) =
        extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) +
          extendToClosure E (normTrace (M m')) x := by
      rw [extendToClosure_sub hadd' hbd' hyc hxc]
      ring
    rw [extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _),
      add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ C * ε := by
      rw [h1]
      refine (norm_extendToClosure_le hadd' hbd' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hC0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + C * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + C) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound' (‖x‖ / (2 * (1 + C))) (by positivity)
  have h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime]

instance charP_residueField_intermediateField (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : CharP 𝓀[K] p :=
  charP_residueField_of_valuativeExtension p K

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
  {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

theorem nrm_le_nrm_iff_norm_le' (x y : PadicAlgCl p) : nrm K x ≤ nrm K y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [nrm_le_nrm_iff, vle_iff_norm_le]

theorem nrm_lt_nrm_iff_norm_lt' (x y : PadicAlgCl p) : nrm K x < nrm K y ↔ ‖x‖ < ‖y‖ := by
  rw [← not_le, ← not_le, nrm_le_nrm_iff_norm_le']

theorem restrictNormalHom_mem_lowerRamificationGroup_zero (M : IntermediateField K (PadicAlgCl p))
    [FiniteDimensional K M] [Normal K M] {τ : Gal(PadicAlgCl p/K)} (hτ : τ ∈ inertiaGal K) :
    AlgEquiv.restrictNormalHom M τ ∈ lowerRamificationGroup K M 0 := by
  rw [mem_lowerRamificationGroup_iff_valuation]
  intro x hx
  have hx1 : nrm K ((⟨x, hx⟩ : 𝒪[M]) : PadicAlgCl p) ≤ 1 := (mem_integer_iff_nrm_le_one M x).1 hx
  have hxn : ‖((x : M) : PadicAlgCl p)‖ ≤ 1 := by
    rw [← norm_one (α := PadicAlgCl p), ← nrm_le_nrm_iff_norm_le' (K := K), nrm_one]
    exact hx1
  have h1 := (mem_inertiaGal.1 hτ) _ hxn
  set z : M := AlgEquiv.restrictNormalHom M τ x - x
  have hz : ((z : M) : PadicAlgCl p) = τ (x : PadicAlgCl p) - (x : PadicAlgCl p) := by
    simp only [z, AddSubgroupClass.coe_sub, AlgEquiv.restrictNormalHom_apply]
  have hzlt : nrm K ((z : M) : PadicAlgCl p) < 1 := by
    rw [← nrm_one (K := K) (Ω := PadicAlgCl p), nrm_lt_nrm_iff_norm_lt', norm_one, hz]
    exact h1
  have key : nrm K ((z : M) : PadicAlgCl p) ≤ unifNrm M ^ (1 : ℤ) := by
    rcases eq_or_ne z 0 with h0 | h0
    · rw [h0, IntermediateField.coe_zero, nrm_zero]
      exact le_of_lt (zpow_pos (unifNrm_pos M) _)
    · rw [nrm_eq_unifNrm_zpow M h0] at hzlt ⊢
      have hord : 1 ≤ ord z := by
        by_contra hlt
        push Not at hlt
        have : (1 : ℝ) ≤ unifNrm M ^ ord z :=
          one_le_zpow_of_nonpos₀ (unifNrm_pos M) (unifNrm_lt_one M).le (by omega)
        linarith
      exact zpow_le_zpow_right_of_le_one₀ (unifNrm_pos M) (unifNrm_lt_one M).le hord
  have := (normalizedValuation_le_exp_iff M z 1).2 key
  simpa [z] using this

theorem artinImage_ne_bot (hη : Continuous η) {τ : Gal(PadicAlgCl p/K)} (hτ : τ ∈ inertiaGal K)
    (hτ2 : η τ ∈ unitsOneAdd p 2) (hτ1 : η τ ≠ 1) (n : ℕ) : artinImage K η n ≠ ⊥ := by
  obtain ⟨b, hb, hb'⟩ := exists_level hτ1
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) hτ2)

  have : FiniteDimensional K (charTower η (b + 1)) := finiteDimensional_charTower hη (b + 1)
  have : IsAbelianGalois K (charTower η (b + 1)) := isAbelianGalois_charTower hη (b + 1)
  have h0 := restrictNormalHom_mem_lowerRamificationGroup_zero (charTower η (b + 1)) hτ
  rw [← upperRamificationGroup_zero, show (0 : ℝ) = ((0 : ℕ) : ℝ) by simp,
    restrictNormalHom_mem_upperRamificationGroup_iff hη, Subgroup.mem_sup] at h0
  obtain ⟨a, ⟨ρ, ⟨u, hu, hu'⟩, rfl⟩, w, hw, haw⟩ := h0
  have ha : η ρ ∈ unitsOneAdd p b := by
    have e : η ρ = η τ * w⁻¹ := by rw [← haw, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hb (inv_mem (unitsOneAdd_antitone (Nat.le_succ b) hw))
  have ha' : η ρ ∉ unitsOneAdd p (b + 1) := fun h => hb' (haw ▸ mul_mem h hw)

  obtain ⟨c, j, hc, hcj⟩ := exists_pow_mem_unitFiltrationUnits (K := K) p n
  have hmem : ρ ^ (c * p ^ j) ∈ artinGal K n := by
    refine ⟨u ^ (c * p ^ j), hcj u hu, ?_⟩
    rw [map_pow, hu', map_pow]
  obtain ⟨h1, h2⟩ := pow_not_mem_of_not_dvd (by omega) ha ha' hc
  obtain ⟨-, h4⟩ := pow_prime_pow_mem_not_mem hb2 h1 h2 j
  intro hbot
  have : η (ρ ^ (c * p ^ j)) ∈ artinImage K η n := ⟨_, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot, map_pow, pow_mul] at this
  exact h4 (this ▸ one_mem _)

theorem baseUnifNrm_le_one : baseUnifNrm K (PadicAlgCl p) ≤ 1 := by
  rw [← unifNrm_pow_ramificationIndex (⊥ : IntermediateField K (PadicAlgCl p))]
  exact pow_le_one₀ (unifNrm_pos _).le (unifNrm_lt_one _).le

omit [FiniteDimensional ℚ_[p] K] in

theorem div_mul_geom_sum_mul_sub_one (e q : ℕ) :
    (e : ℝ) / p * (∑ i ∈ Finset.range q, (p : ℝ) ^ (-(i : ℤ))) * ((p : ℝ) - 1) =
      e - e * (p : ℝ) ^ (-(q : ℤ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p : ℝ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one]; exact_mod_cast hp.out.one_lt.ne'
  have hr : ∑ i ∈ Finset.range q, (p : ℝ) ^ (-(i : ℤ)) = ∑ i ∈ Finset.range q, ((p : ℝ)⁻¹) ^ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hr, geom_sum_eq hp1, zpow_neg, zpow_natCast, inv_pow]
  have hp1' : (p : ℝ)⁻¹ - 1 ≠ 0 := sub_ne_zero.2 hp1
  have hp1'' : (1 : ℝ) - p ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  field_simp
  ring

theorem nrm_normTrace_step_le (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1)
    {τ : Gal(PadicAlgCl p/K)} {b : ℕ} (hb2 : 2 ≤ b) (hτb : η τ ∈ unitsOneAdd p b)
    (hτb' : η τ ∉ unitsOneAdd p (b + 1)) {k : ℕ} (hkb : b ≤ k) (hk : artinLevel K η n₀ ≤ k)
    {y : PadicAlgCl p} (hy : y ∈ charTower η (k + 1)) :
    nrm K (normTrace (charTower η k) y) ≤ baseUnifNrm K (PadicAlgCl p) ^
      (-((absRamificationIndex K : ℝ) * (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) *
        nrm K y := by
  have : FiniteDimensional K (charTower η (k + 1)) := finiteDimensional_charTower hη (k + 1)
  obtain ⟨hτk, hτk'⟩ := pow_prime_pow_mem_not_mem hb2 hτb hτb' (k - b)
  rw [Nat.add_sub_cancel' hkb] at hτk hτk'
  have hk2 : 2 ≤ k := hb2.trans hkb
  have hητk : η (τ ^ p ^ (k - b)) = η τ ^ p ^ (k - b) := map_pow _ _ _
  have hτM : τ ^ p ^ (k - b) ∈ (charTower η k).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, hητk]; exact hτk
  have hτp : (τ ^ p ^ (k - b)) ^ p ∈ (charTower η (k + 1)).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_pow, hητk]
    exact (pow_prime_mem_iff hk2 hτk).1
  have hτ1 : τ ^ p ^ (k - b) ∉ (charTower η (k + 1)).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, hητk]; exact hτk'
  have hgen : ∀ σ ∈ (charTower η k).fixingSubgroup, ∃ j : ℕ,
      ∀ z ∈ charTower η (k + 1), σ z = ((τ ^ p ^ (k - b)) ^ j) z := by
    intro σ hσ
    rw [fixingSubgroup_charTower hη, mem_charTowerGal] at hσ
    obtain ⟨j, hj⟩ := exists_mul_inv_pow_mem hk2 hτk hτk' hσ (k + 1)
    refine ⟨j, fun z hz => ?_⟩
    have hmem : ((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ ∈ (charTower η (k + 1)).fixingSubgroup := by
      rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_mul, map_inv, map_pow, hητk,
        mul_comm]
      exact hj
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem z hz
    calc σ z = ((τ ^ p ^ (k - b)) ^ j * (((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ)) z := by
          rw [mul_inv_cancel_left]
      _ = ((τ ^ p ^ (k - b)) ^ j) ((((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ) z) := rfl
      _ = ((τ ^ p ^ (k - b)) ^ j) z := by rw [hfix]
  have hτM' : ∀ z ∈ charTower η (k + 1), (τ ^ p ^ (k - b)) z ∈ charTower η (k + 1) :=
    fun z hz => map_mem_charTower hη _ hz

  have hϖ0 : 0 < baseUnifNrm K (PadicAlgCl p) := baseUnifNrm_pos
  have hϖ1 : baseUnifNrm K (PadicAlgCl p) ≤ 1 := baseUnifNrm_le_one
  set X : ℝ := (absRamificationIndex K : ℝ) / p *
    ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hρ0 : 0 ≤ baseUnifNrm K (PadicAlgCl p) ^ X := Real.rpow_nonneg hϖ0.le X
  have hρ1 : baseUnifNrm K (PadicAlgCl p) ^ X ≤ 1 := Real.rpow_le_one hϖ0.le hϖ1 hX0
  have hρ : ∀ z ∈ charTower η (k + 1),
      nrm K ((τ ^ p ^ (k - b)) z - z) ≤ baseUnifNrm K (PadicAlgCl p) ^ X * nrm K z :=
    fun z hz => nrm_sub_le_of_mem_unitsOneAdd hη hA hn' h2 hper hk (by rw [hητk]; exact hτk) hz
  have h := nrm_normTrace_mul_le (M := charTower η k) (M' := charTower η (k + 1))
    (hMM' := charTower_mono η (Nat.le_succ k)) (hτM := hτM) (hτp := hτp) (hτ1 := hτ1)
    (hgen := hgen) (hτM' := hτM') (hρ0 := hρ0) (hρ1 := hρ1) (hρ := hρ) (hy := hy)

  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpe : nrm K (p : PadicAlgCl p) =
      baseUnifNrm K (PadicAlgCl p) ^ (absRamificationIndex K : ℝ) := by
    rw [nrm_natCast_prime_eq p, Real.rpow_natCast]
  have hρp : (baseUnifNrm K (PadicAlgCl p) ^ X) ^ (p - 1) =
      baseUnifNrm K (PadicAlgCl p) ^ (absRamificationIndex K : ℝ) *
        baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
          (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϖ0.le, ← Real.rpow_add hϖ0]
    congr 1
    rw [Nat.cast_sub hp1, Nat.cast_one, hXdef, div_mul_geom_sum_mul_sub_one]
    ring
  have hone : 1 ≤ baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
      (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hϖ0 hϖ1 (by
      have : 0 ≤ (absRamificationIndex K : ℝ) * (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)) := by
        positivity
      linarith)
  have hmax : max (nrm K (p : PadicAlgCl p)) ((baseUnifNrm K (PadicAlgCl p) ^ X) ^ (p - 1)) ≤
      nrm K (p : PadicAlgCl p) * baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) := by
    refine max_le (le_mul_of_one_le_right (nrm_nonneg _) hone) ?_
    rw [hρp, hpe]
  have hpos : 0 < nrm K (p : PadicAlgCl p) :=
    nrm_pos.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have h3 := h.trans (mul_le_mul_of_nonneg_right hmax (nrm_nonneg _))
  rw [mul_comm (nrm K (normTrace (charTower η k) y)), mul_assoc] at h3
  exact le_of_mul_le_mul_left h3 hpos

omit [FiniteDimensional ℚ_[p] K] in

theorem sum_zpow_neg_le (j : ℕ) :
    ∑ i ∈ Finset.range j, (p : ℝ) ^ (-(i : ℤ)) ≤ 2 - 2 * (p : ℝ) ^ (-(j : ℤ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have e : (p : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) = (p : ℝ) ^ (-(j : ℤ)) * (p : ℝ)⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hp0.ne']; congr 1; push_cast; ring
    rw [e]
    have hq : 0 ≤ (p : ℝ) ^ (-(j : ℤ)) := by positivity
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
    nlinarith

theorem nrm_normTrace_charTower_le (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1)
    {τ : Gal(PadicAlgCl p/K)} {b : ℕ} (hb2 : 2 ≤ b) (hτb : η τ ∈ unitsOneAdd p b)
    (hτb' : η τ ∉ unitsOneAdd p (b + 1)) {n : ℕ} (hnb : b ≤ n) (hn : artinLevel K η n₀ ≤ n)
    {m : ℕ} {y : PadicAlgCl p} (hy : y ∈ charTower η m) :
    nrm K (normTrace (charTower η n) y) ≤
      baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) * nrm K y := by
  have hfin : ∀ k, FiniteDimensional K (charTower η k) := fun k => finiteDimensional_charTower hη k
  have hϖ0 : 0 < baseUnifNrm K (PadicAlgCl p) := baseUnifNrm_pos
  have hϖ1 : baseUnifNrm K (PadicAlgCl p) ≤ 1 := baseUnifNrm_le_one
  have hone : 1 ≤ baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hϖ0 hϖ1 (by
      have : (0 : ℝ) ≤ 2 * absRamificationIndex K := by positivity
      linarith)
  rcases le_total m n with hmn | hnm
  · rw [normTrace_of_mem _ (charTower_mono η hmn hy)]
    exact le_mul_of_one_le_left (nrm_nonneg _) hone
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm

  have hclaim : ∀ j, ∀ z ∈ charTower η (n + j), nrm K (normTrace (charTower η n) z) ≤
      baseUnifNrm K (PadicAlgCl p) ^ (-(∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((n + i - artinLevel K η n₀ : ℕ) : ℤ)))) * nrm K z := by
    intro j
    induction j with
    | zero =>
      intro z hz
      rw [add_zero] at hz
      rw [normTrace_of_mem _ hz]
      simp
    | succ j ih =>
      intro z hz
      have hz' : normTrace (charTower η (n + j)) z ∈ charTower η (n + j) := normTrace_mem _ z
      have hcomp : normTrace (charTower η n) (normTrace (charTower η (n + j)) z) =
          normTrace (charTower η n) z :=
        normTrace_normTrace_of_le (charTower_mono η (Nat.le_add_right n j)) z
      have hstep := nrm_normTrace_step_le hη hA hn' h2 hper hb2 hτb hτb'
        (show b ≤ n + j by omega) (show artinLevel K η n₀ ≤ n + j by omega)
        (show z ∈ charTower η (n + j + 1) by simpa [add_assoc] using hz)
      rw [← hcomp]
      refine (ih _ hz').trans ?_
      rw [Finset.sum_range_succ, neg_add, Real.rpow_add hϖ0, mul_assoc]
      exact mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hϖ0.le _)
  refine (hclaim j y hy).trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  refine Real.rpow_le_rpow_of_exponent_ge hϖ0 hϖ1 (neg_le_neg ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  calc ∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((n + i - artinLevel K η n₀ : ℕ) : ℤ))
      ≤ ∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) * (p : ℝ) ^ (-(i : ℤ)) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact zpow_le_zpow_right₀ hp1 (by omega)
    _ = (absRamificationIndex K : ℝ) * ∑ i ∈ Finset.range j, (p : ℝ) ^ (-(i : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ (absRamificationIndex K : ℝ) * 2 := by
        refine mul_le_mul_of_nonneg_left ((sum_zpow_neg_le j).trans ?_) (Nat.cast_nonneg _)
        have : 0 ≤ (p : ℝ) ^ (-(j : ℤ)) := by positivity
        linarith
    _ = 2 * absRamificationIndex K := by ring

end SenTateChar

end GroundTheory.PAdicHodge
end
end
