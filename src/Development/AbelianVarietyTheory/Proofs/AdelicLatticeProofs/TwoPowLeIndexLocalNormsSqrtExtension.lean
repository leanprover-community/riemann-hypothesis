import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlaces

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_pow_card_le_index_iInf :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pow_card_le_index_iInf_of_independent : ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → 2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  atlas_forward_decl GlobalTheory.QNorm.two_pow_card_le_index_iInf
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_mod_local_squares : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  first | exact @GlobalTheory.QNorm.exists_approx_mod_squares | exact GlobalTheory.QNorm.exists_approx_mod_squares | (intros; apply GlobalTheory.QNorm.exists_approx_mod_squares <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  first | exact @GlobalTheory.QNorm.exists_local_nonnorm | exact GlobalTheory.QNorm.exists_local_nonnorm | (intros; apply GlobalTheory.QNorm.exists_local_nonnorm <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem relIndex_le_two_of_coset {G : Type} [CommGroup G] (H K : Subgroup G) (ε : G)
    (h : ∀ x ∈ K, x ∈ H ∨ x * ε⁻¹ ∈ H) : H.relIndex K ≤ 2 := by
  by_cases hK : K ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hK]; norm_num
  · obtain ⟨a, haK, haH⟩ := SetLike.not_le_iff_exists.mp hK
    have ha := (h a haK).resolve_left haH
    apply le_of_eq
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a⁻¹, K.inv_mem haK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ H
    · right
      refine ⟨hb, fun hba => haH ?_⟩
      have := H.mul_mem hb (H.inv_mem hba)
      simpa using this
    · left
      refine ⟨?_, hb⟩
      have := H.mul_mem ((h b b.2).resolve_left hb) (H.inv_mem ha)
      have e : (b : G) * ε⁻¹ * (a * ε⁻¹)⁻¹ = b * a⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at this

theorem relIndex_sqs_le_two_mul :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  intro G _ U H ε hHU hfin hε hsq
  have hle : ∀ V : Subgroup G, sqs V ≤ V := by
    rintro V x ⟨y, hy, rfl⟩
    exact V.pow_mem hy 2
  have hmono : sqs H ≤ sqs U := Subgroup.map_mono hHU
  have h1 := Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU
  have h2 := Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)
  set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'
  have h3 : H'.relIndex U = (sqs H).relIndex (sqs U) := by
    rw [hH', Subgroup.relIndex_comap]; rfl
  have hHH' : H ≤ H' ⊓ U := le_inf (Subgroup.le_comap_map _ _) hHU
  have h4 := Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right
  rw [Subgroup.inf_relIndex_right, h3] at h4
  have h5 : H.relIndex (H' ⊓ U) ≤ 2 := by
    apply relIndex_le_two_of_coset H _ ε
    rintro x ⟨⟨y, hy, hxy⟩, -⟩
    simp only [powMonoidHom_apply] at hxy
    have : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]
    rcases hε _ this with h | h
    · left
      rw [mul_inv_eq_one] at h
      rw [h]; exact hy
    · right
      have e : x * ε⁻¹ = y := by
        rw [← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]
      rw [e]; exact hy
  have hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0 := by
    rw [h2, ← h1]; exact mul_ne_zero hsq hfin
  obtain ⟨hb, ha⟩ := mul_ne_zero_iff.mp hne
  refine ⟨ha, ?_⟩
  apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)
  rw [h2, ← h1, ← h4]
  calc (sqs H).relIndex H * (H.relIndex (H' ⊓ U) * (sqs H).relIndex (sqs U))
      ≤ (sqs H).relIndex H * (2 * (sqs H).relIndex (sqs U)) := by gcongr
    _ = _ := by ring

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup : ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 → (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 → (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  atlas_forward_decl GlobalTheory.QNorm.relIndex_sqs_le_two_mul
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherUnits_le_squares_higherUnits : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤ sqs (hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  first | exact @GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | exact GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | (intros; apply GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < WithZero.exp m) :
    a ≤ WithZero.exp (m - 1) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem relIndex_hiUnits_succ_le :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  intro K _ w π R n hπ hR
  have hπn : w (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hπn0 : w (π ^ n) ≠ 0 := by rw [hπn]; exact WithZero.exp_ne_zero
  have hπn0' : π ^ n ≠ 0 := by
    intro h; rw [h] at hπn0; simp at hπn0
  have hex : ∀ x : hiUnits w n, ∃ r : R, w ((((x : Kˣ) : K) - 1) / π ^ n - r) < 1 := by
    intro x
    have hx : w (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := x.2.2
    obtain ⟨r, hr, h⟩ := hR ((((x : Kˣ) : K) - 1) / π ^ n) (by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hπn0), hπn]; exact hx)
    exact ⟨⟨r, hr⟩, h⟩
  choose f hf using hex
  have key : ∀ x y : hiUnits w n, f x = f y →
      x⁻¹ * y ∈ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) := by
    intro x y hxy
    have hx1 : w ((x : Kˣ) : K) = 1 := x.2.1
    have hy1 : w ((y : Kˣ) : K) = 1 := y.2.1
    have h1 := hf x
    have h2 := hf y
    rw [← hxy] at h2
    have h3 := w.map_sub_lt h2 h1
    have h4 : (((y : Kˣ) : K) - 1) / π ^ n - (f x : K) -
        ((((x : Kˣ) : K) - 1) / π ^ n - (f x : K)) =
        (((y : Kˣ) : K) - ((x : Kˣ) : K)) / π ^ n := by ring
    rw [h4, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hπn0), hπn] at h3
    have h5 := le_exp_sub_one_of_lt_exp h3
    rw [Subgroup.mem_subgroupOf]
    have hv : ((((x⁻¹ * y : hiUnits w n) : Kˣ)) : K) =
        ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) := by simp
    refine ⟨by rw [hv, map_mul, map_inv₀, hx1, hy1]; simp, ?_⟩
    have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h6 : ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) - 1 =
        ((x : Kˣ) : K)⁻¹ * (((y : Kˣ) : K) - ((x : Kˣ) : K)) := by
      field_simp
    rw [hv, h6, map_mul, map_inv₀, hx1, inv_one, one_mul]
    refine h5.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hinj : Function.Injective
      (fun q : hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) => f q.out) := by
    intro p q hpq
    have := key _ _ hpq
    rw [← QuotientGroup.eq] at this
    simpa using this
  have hfin : Finite (hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n)) :=
    Finite.of_injective _ hinj
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := R), Fintype.card_coe] at this
    exact this

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_higherUnits_succ_le_card : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) → (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧ (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  atlas_forward_decl GlobalTheory.QNorm.relIndex_hiUnits_succ_le
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_hiUnits_sup_sqs_of_even {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (p : Kˣ)
    (hp : w (p : K) = WithZero.exp (-1)) (x : Kˣ) (m : ℤ)
    (hx : w (x : K) = WithZero.exp (2 * m)) :
    x ∈ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ) := by
  have h1 : w ((x * (p ^ m) ^ 2 : Kˣ) : K) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow,
      map_zpow₀, hx, hp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp
  have hU : x * (p ^ m) ^ 2 ∈ hiUnits w 0 := by
    refine ⟨h1, ?_⟩
    refine le_trans (w.map_sub _ _) (max_le ?_ ?_)
    · rw [h1]; simp
    · simp
  have hS : ((p ^ m)⁻¹) ^ 2 ∈ sqs (⊤ : Subgroup Kˣ) := ⟨(p ^ m)⁻¹, trivial, rfl⟩
  have : x = (x * (p ^ m) ^ 2) * ((p ^ m)⁻¹) ^ 2 := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rw [this]
  exact Subgroup.mul_mem_sup hU hS

theorem index_sqs_top_le : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K),
    w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 →
    (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧
      (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  intro K _ w π hπ h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hdvd : (hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ)).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨Units.mk0 π hπ0, fun b => ?_⟩
    have hb : w (b : K) ≠ 0 := by simp
    have hb' : w (b : K) = WithZero.exp (WithZero.log (w (b : K))) := (WithZero.exp_log hb).symm
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (WithZero.log (w (b : K)))
    · right
      exact mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ b m (by rw [hb', hm])
    · left
      refine mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ _ m ?_
      rw [Units.val_mul, map_mul, hb', hm, Units.val_mk0, hπ, ← WithZero.exp_add]
      congr 1
      ring
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_right : sqs (⊤ : Subgroup Kˣ) ≤ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ))
  rw [Subgroup.relIndex_sup_right] at hmul
  have hle : sqs (hiUnits w 0) ≤ sqs (⊤ : Subgroup Kˣ) := Subgroup.map_mono le_top
  have hd2 := Subgroup.relIndex_dvd_of_le_left (hiUnits w 0) hle
  have hd : (sqs (⊤ : Subgroup Kˣ)).index ∣ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
    rw [← hmul, mul_comm]
    exact Nat.mul_dvd_mul hdvd hd2
  have hpos : 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 := mul_ne_zero two_ne_zero h0
  exact ⟨ne_zero_of_dvd_ne_zero hpos hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd⟩

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_squares_le_two_mul_units_squares : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K), w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 → (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧ (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  atlas_forward_decl GlobalTheory.QNorm.index_sqs_top_le
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  atlas_forward_decl GlobalTheory.QNorm.index_sqSub_adicCompletion_le
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem prod_absNorm_pow_le_two_pow :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_absNorm_pow_valuation_two_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  atlas_forward_decl GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem isSquare_real_iff_nonneg (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun h => h.nonneg, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩

theorem index_sqSub_real_dvd_two {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by
  by_cases h : ∀ x : Fˣ, x ∈ sqSub σ
  · rw [show sqSub σ = ⊤ from eq_top_iff.mpr fun x _ => h x, Subgroup.index_top]
    exact one_dvd 2
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have hne : ∀ x : Fˣ, σ (x : F) ≠ 0 := fun x => (x.isUnit.map σ).ne_zero
    have hmem : ∀ x : Fˣ, x ∈ sqSub σ ↔ 0 ≤ σ (x : F) := fun x =>
      (mem_sqSub σ x).trans (isSquare_real_iff_nonneg _)
    have ha' : σ (a : F) < 0 := not_le.mp fun h' => ha ((hmem a).mpr h')
    have h2 : (sqSub σ).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      rw [hmem, hmem, Units.val_mul, map_mul]
      rcases lt_or_gt_of_ne (hne b) with hb | hb
      · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hb.le ha'.le, not_le.mpr hb⟩
      · exact Or.inr ⟨hb.le, not_le.mpr (mul_neg_of_pos_of_neg hb ha')⟩
    rw [h2]

theorem exists_valuation_two_eq_exp {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ e : ℕ, v.valuation F 2 = WithZero.exp (-(e : ℤ)) := by
  have h2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
  have hle : v.valuation F 2 ≤ 1 := by
    rw [h2]
    exact v.valuation_le_one 2
  have hne : v.valuation F 2 ≠ 0 := (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hk : WithZero.log (v.valuation F 2) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log (v.valuation F 2)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

private theorem index_biInf_ne_zero_and_le_prod {G ι : Type} [Group G] [DecidableEq ι] (S : Finset ι)
    (f : ι → Subgroup G) :
    (∀ i ∈ S, (f i).index ≠ 0) →
      (⨅ i ∈ S, f i).index ≠ 0 ∧ (⨅ i ∈ S, f i).index ≤ ∏ i ∈ S, (f i).index := by
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    obtain ⟨h0, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 := hf a (Finset.mem_insert_self a s)
    exact ⟨Subgroup.index_inf_ne_zero ha0 h0,
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hle)⟩

theorem index_locSq_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  classical
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_two_eq_exp v
  have hP := GlobalTheory.T.prod_absNorm_pow_valuation_two_le F S e (fun v _ => he v)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e v :=
    fun v => GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le F v (e v) (he v)
  obtain ⟨hF0, hFle⟩ := index_biInf_ne_zero_and_le_prod S (fun v => sqSub (algebraMap F (v.adicCompletion F)))
    (fun v _ => (hN v).1)
  have hR2 : ∀ σ : F →+* ℝ, (sqSub σ).index ≤ 2 := fun σ =>
    Nat.le_of_dvd two_pos (index_sqSub_real_dvd_two σ)
  obtain ⟨hR0, hRle⟩ := index_biInf_ne_zero_and_le_prod (Finset.univ : Finset (F →+* ℝ)) (fun σ => sqSub σ)
    (fun σ _ => ne_zero_of_dvd_ne_zero two_ne_zero (index_sqSub_real_dvd_two σ))
  have hRu : (⨅ σ : F →+* ℝ, sqSub σ) = ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    simp
  have hloc : locSq F S = (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))) ⊓
      ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    rw [← hRu]
    rfl
  rw [hloc]
  refine ⟨Subgroup.index_inf_ne_zero hF0 hR0, ?_⟩
  have hF : (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))).index ≤
      4 ^ S.card * 2 ^ Module.finrank ℚ F := by
    refine hFle.trans ?_
    calc ∏ v ∈ S, (sqSub (algebraMap F (v.adicCompletion F))).index
        ≤ ∏ v ∈ S, (4 * Ideal.absNorm v.asIdeal ^ e v) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => (hN v).2)
      _ = 4 ^ S.card * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 4 ^ S.card * 2 ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ hP
  have hR : (⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ).index ≤
      2 ^ InfinitePlace.nrRealPlaces F := by
    refine hRle.trans ?_
    calc ∏ σ ∈ (Finset.univ : Finset (F →+* ℝ)), (sqSub σ).index
        ≤ ∏ _σ ∈ (Finset.univ : Finset (F →+* ℝ)), 2 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun σ _ => hR2 σ)
      _ = 2 ^ InfinitePlace.nrRealPlaces F := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' F]
  refine Subgroup.index_inf_le.trans ((Nat.mul_le_mul hF hR).trans (le_of_eq ?_))
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, show (4 : ℕ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

end GlobalTheory.QNorm
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.index_locSq_le | exact GlobalTheory.QNorm.index_locSq_le | (intros; apply GlobalTheory.QNorm.index_locSq_le <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem norm_of_isSquare_mul {L : Type} [Field L] {x y δ : L} (hx : x ≠ 0)
    (h : IsSquare (x * y)) (hn : ∃ a b : L, x = a ^ 2 - δ * b ^ 2) :
    ∃ a b : L, y = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨a * s / x, b * s / x, ?_⟩
  field_simp
  linear_combination x * hs + s ^ 2 * hab

theorem mem_normSub_real_of_pos {F : Type} [Field F] (σ : F →+* ℝ) (δ : F) (x : Fˣ)
    (h : 0 < σ (x : F)) : x ∈ normSub σ δ :=
  ⟨Real.sqrt (σ (x : F)), 0, by rw [Real.sq_sqrt h.le]; ring⟩

theorem locSq_le_locNorm_of_delta (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : locSq F S ≤ locNorm F δ S := by
  unfold locSq locNorm finSq
  exact inf_le_inf (iInf_mono fun v => iInf_mono fun _ => sqSub_le_normSub _ _)
    (iInf_mono fun σ => sqSub_le_normSub _ _)

theorem two_pow_le_index_locNorm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))),
      δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧
        2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  intro F _ _ δ S hδ
  classical
  have h0 : (locNorm F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le F S).1
      (Subgroup.index_dvd_of_le (locSq_le_locNorm_of_delta F δ S))
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)} with hA
  set B : Set (F →+* ℝ) := {σ | σ δ < 0} with hB
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  have hBf : B.Finite := Set.toFinite _
  letI : Fintype A := hAf.fintype
  letI : Fintype B := hBf.fintype
  let K : A ⊕ B → Subgroup Fˣ := Sum.elim
    (fun v => normSub (algebraMap F (v.1.adicCompletion F)) δ) (fun σ => normSub σ.1 δ)
  have hle : locNorm F δ S ≤ ⨅ i, K i := by
    refine le_iInf ?_
    rintro (v | σ)
    · exact inf_le_left.trans (iInf₂_le v.1 v.2.1)
    · exact inf_le_right.trans (iInf_le _ σ.1)
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card (A ⊕ B) = tFin F δ S + tReal F δ := by
    rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.two_pow_card_le_index_iInf_of_independent Fˣ (A ⊕ B) K ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  rintro (v | σ)
  · obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion F v.1 (algebraMap F _ δ) (by simpa using hδ) v.2.2
    obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 y)
      (fun _ => 1) (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simpa using hy0
        · simp [Function.update_of_ne hw]) (by simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      have h1 := hxv v.1 v.2.1
      rw [Function.update_self] at h1
      exact hy (norm_of_isSquare_mul (by simpa using hx0) h1 hm)
    · rintro (w | τ) hj
      · have hw : w.1 ≠ v.1 := fun h => hj (congrArg Sum.inl (Subtype.ext h))
        have h1 := hxv w.1 w.2.1
        rw [Function.update_of_ne hw, mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · exact mem_normSub_real_of_pos _ _ _ (by simpa using hxσ τ.1)
  · obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S (fun _ => 1)
      (fun τ => if τ = σ.1 then -1 else 1) (by simp) (by
        intro τ
        split_ifs <;> simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      have h1 := hxσ σ.1
      have h2 : σ.1 δ < 0 := σ.2
      simp only [if_true] at h1
      have h3 : σ.1 x = a ^ 2 - σ.1 δ * b ^ 2 := hab
      nlinarith [sq_nonneg a, mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg b)]
    · rintro (w | τ) hj
      · have h1 := hxv w.1 w.2.1
        rw [mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · have hw : τ.1 ≠ σ.1 := fun h => hj (congrArg Sum.inr (Subtype.ext h))
        exact mem_normSub_real_of_pos _ _ _ (by simpa [hw] using hxσ τ.1)

end GlobalTheory.QNorm
end

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension : ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧ 2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  atlas_forward_decl GlobalTheory.QNorm.two_pow_le_index_locNorm
end
