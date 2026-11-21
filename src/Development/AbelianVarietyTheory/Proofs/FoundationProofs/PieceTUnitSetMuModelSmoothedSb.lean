import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SumMulCoPtSbEqSumInv
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import BuildAid.ForwardExisting

section
noncomputable section

open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.Smoothing

namespace GlobalTheory.TameSmoothing

variable {K : Type*} [Field K] [CharZero K]

theorem modEq_scale_tame {N q : ℕ} [NeZero q] (e : ℤ) (y : ZMod q) (s : ℤ) :
    e * ((N : ℤ) * y.val + (q : ℤ) * s) ≡ (N : ℤ) * ((e : ZMod q) * y).val + (q : ℤ) * (e * s)
      [ZMOD ((N * q : ℕ) : ℤ)] := by
  have h : ((e * (y.val : ℤ) : ℤ) : ZMod q) = (((((e : ZMod q) * y).val : ℕ) : ℤ) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [Int.modEq_iff_dvd]
  exact ⟨w, by push_cast; linear_combination (N : ℤ) * hw⟩

theorem eisF_scale_tame {j N p n : ℕ} [NeZero p] (hN : 0 < N) {ζ : K} (hζ : ζ ^ (N * p ^ n) = 1) (e : ℤ)
    (γ δ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ)
    (h : ∀ l, (δ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l =
      (e : ZMod (p ^ n)) * (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l) :
    eisF j (N * p ^ n) ζ (e * (rowT N p n γ i w).1) (e * (rowT N p n γ i w).2) =
      eisF j (N * p ^ n) ζ (rowT N p n δ i (e * w.1, e * w.2)).1 (rowT N p n δ i (e * w.1, e * w.2)).2 := by
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (Nat.pos_of_ne_zero (NeZero.ne _))
  refine eisF_congr_mod hM hζ ?_ ?_
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0) w.1
    simpa only [rowT, h, Nat.cast_pow] using this
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1) w.2
    simpa only [rowT, h, Nat.cast_pow] using this

theorem sum_scaled_tame (p : ℕ) [hp : Fact p.Prime] (N n m k : ℕ) (ψ : DirichletCharacter K (p ^ m))
    (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ n)) (hN : 0 < N) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hpc : ¬ (p : ℤ) ∣ c) (hpd : ¬ (p : ℤ) ∣ d) (r : ℕ) :
    ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (c * (rowT N p n γ 0 w).1) (c * (rowT N p n γ 0 w).2))
           (eisF 1 (N * p ^ n) ζ (d * (rowT N p n γ 1 w').1) (d * (rowT N p n γ 1 w').2)) r =
    ψ⁻¹ (c : ZMod (p ^ m)) * ψ⁻¹ (d : ZMod (p ^ m)) *
      ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 (c * w.1, c * w.2)).1 (rowT N p n γ 0 (c * w.1, c * w.2)).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 (d * w'.1, d * w'.2)).1
             (rowT N p n γ 1 (d * w'.1, d * w'.2)).2) r := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have huc : IsUnit (c : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpc
  have hud : IsUnit (d : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpd
  have hψ : ∀ e : ℤ, ¬ (p : ℤ) ∣ e → ψ⁻¹ (e : ZMod (p ^ m)) * ψ (e : ZMod (p ^ m)) = 1 := by
    intro e he
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_intCast_of_not_dvd he)]
  have hcast : ∀ y : ZMod (p ^ n), ((y.val : ℕ) : ZMod (p ^ m)) =
      ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) y := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun γ => diagGL huc.unit hud.unit * γ)
    (fun γ => (diagGL huc.unit hud.unit)⁻¹ * γ) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    exact (diagGL_mul_mem hn _ _ γ).mpr hγ
  · intro γ hγ
    refine (diagGL_mul_mem hn huc.unit hud.unit _).mp ?_
    rwa [mul_inv_cancel_left]
  · intro γ _
    exact inv_mul_cancel_left _ _
  · intro γ _
    exact mul_inv_cancel_left _ _
  · intro γ _
    rw [eisF_scale_tame hN hζ.pow_eq_one c γ (diagGL huc.unit hud.unit * γ) 0 w
        (fun l => diagGL_mul_zero _ _ _ l),
      eisF_scale_tame hN hζ.pow_eq_one d γ (diagGL huc.unit hud.unit * γ) 1 w'
        (fun l => diagGL_mul_one _ _ _ l),
      diagGL_mul_det, hcast, hcast, IsUnit.unit_spec, IsUnit.unit_spec,
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))), map_mul ψ, map_mul ψ]
    have h1 := hψ c hpc
    have h2 := hψ d hpd
    generalize ψ⁻¹ (c : ZMod (p ^ m)) = A at h1 ⊢
    generalize ψ⁻¹ (d : ZMod (p ^ m)) = B at h2 ⊢
    generalize ψ (c : ZMod (p ^ m)) = A' at h1 ⊢
    generalize ψ (d : ZMod (p ^ m)) = B' at h2 ⊢
    generalize cmul (K := K) _ _ r = T
    generalize ψ (ZMod.castHom _ _ _) = S
    linear_combination (-(S * T)) * h1 - (A * A' * S * T) * h2

theorem pieceT_unitSet_eq_four_pieceTRaw :
    ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K), IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → ∀ r : ℕ, pieceT N p n m k ψ c d w w' ζ (unitSet p n) r = (c : K) ^ 2 * (d : K) ^ 2 * pieceTRaw N p n m k ψ w w' ζ (unitSet p n) r - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * pieceTRaw N p n m k ψ (c * w.1, c * w.2) w' ζ (unitSet p n) r - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ w (d * w'.1, d * w'.2) ζ (unitSet p n) r + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ (c * w.1, c * w.2) (d * w'.1, d * w'.2) ζ (unitSet p n) r := by
  intro p hp N n m k K _ _ ψ c d w w' ζ hζ hN _ hm hmn hk hpc hpd r
  have hp1 : ¬ (p : ℤ) ∣ 1 := (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one
  have h2 := sum_scaled_tame p N n m k ψ 1 d w w' ζ hζ hN hm hmn hp1 hpd r
  have h3 := sum_scaled_tame p N n m k ψ c 1 w w' ζ hζ hN hm hmn hpc hp1 r
  have h4 := sum_scaled_tame p N n m k ψ c d w w' ζ hζ hN hm hmn hpc hpd r
  simp only [one_mul, Int.cast_one, map_one, mul_one, Prod.mk.eta] at h2 h3
  have e1 : (2 : ℤ) - ((k - 1 : ℕ) : ℤ) = 3 - k := by omega
  have e2 : (2 : ℤ) - ((1 : ℕ) : ℤ) = 1 := by norm_num
  have hs : ∀ (e : ℤ) (j M : ℕ) (a b : ℤ), smF e j M ζ a b =
      fun i => (e : K) ^ 2 * eisF j M ζ a b i - (e : K) ^ ((2 : ℤ) - j) * eisF j M ζ (e * a) (e * b) i :=
    fun _ _ _ _ _ => rfl
  unfold pieceT pieceTRaw
  simp only [hs, cmul_expand, e1, e2, zpow_one, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [mul_left_comm (ψ _), ← Finset.mul_sum]
  rw [h2, h3, h4]
  ring

end GlobalTheory.TameSmoothing
end
end

section
section
open GlobalTheory.KummerEisensteinGalois Finset

namespace GlobalTheory.KummerEisensteinGalois.ChSum

theorem core {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      (if D + w * n₂ * D' = 0 then (M : K) else 0) * (ψ⁻¹ (w * D') * gaussSum ψ e) := by
  have step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D')) := by
    intro a
    let f : ZMod M ≃ ZMod M :=
      { toFun := fun s => w * (s + n₂ * a)
        invFun := fun b => n₁ * b - n₂ * a
        left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw
        right_inv := fun b => by simp only; linear_combination b * hw }
    rw [← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f, Equiv.coe_fn_mk]
    have h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s := by linear_combination (s + n₂ * a) * hw
    have h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D') := by ring
    rw [h1, h2, AddChar.map_add_eq_mul]; ring
  have hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e := by
    rw [← gaussSum_mulShift_of_isPrimitive e hψ]
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm s]
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]
  split_ifs <;> ring

theorem eval {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    (∀ u : (ZMod M)ˣ, D = u * (-n₂) → D' = u * n₁ →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
        (M : K) * ψ⁻¹ (u : ZMod M) * gaussSum ψ e) ∧
    ((¬ ∃ u : (ZMod M)ˣ, D = u * (-n₂) ∧ D' = u * n₁) →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = 0) := by
  rw [core ψ hψ e he n₁ n₂ w D D' hw]
  refine ⟨fun u hD hD' => ?_, fun hno => ?_⟩
  · have h0 : D + w * n₂ * D' = 0 := by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw
    have hl : w * D' = u := by rw [hD']; linear_combination (u : ZMod M) * hw
    rw [if_pos h0, hl]; ring
  · by_cases hc : D + w * n₂ * D' = 0
    · have hnu : ¬ IsUnit (w * D') := by
        rintro ⟨v, hv⟩
        refine hno ⟨v, ?_, ?_⟩
        · rw [hv]; linear_combination hc
        · rw [hv]; linear_combination (-D') * hw
      rw [if_pos hc, MulChar.map_nonunit _ hnu]; ring
    · rw [if_neg hc, zero_mul]

theorem zpow_eq {M : ℕ} [NeZero M] {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) (z : ℤ) :
    ζ ^ z = AddChar.zmodChar M hζ.pow_eq_one (z : ZMod M) := by
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
  rw [AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv z M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

theorem unit_of_not_dvd (p m : ℕ) (hp : p.Prime) (n : ℤ) (h : ¬ (p : ℤ) ∣ n) :
    ∃ w : ZMod (p ^ m), (n : ZMod (p ^ m)) * w = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc : IsCoprime n ((p : ℤ) ^ m) :=
    (((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨(u : ZMod (p ^ m)), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

theorem charSum : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  intro p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn
  have hp : p.Prime := Fact.out
  have he := AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ
  set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def
  have hG : gaussS p m ψ ζm = gaussSum ψ e := rfl
  have hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') =
      e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) := by
    intro a b
    rw [zpow_eq hζ]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hz, hG]
  rw [← Nat.cast_pow]
  by_cases h1 : (p : ℤ) ∣ n₁
  · have h2 : ¬ (p : ℤ) ∣ n₂ := fun h => hn ⟨h1, h⟩
    obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₂ h2
    have hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1 := by rw [neg_mul_neg, hw]
    have key := eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w)
      (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'
    have hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
          e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) =
        ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) *
          e (a * (d' : ZMod (p ^ m)) + b * (d : ZMod (p ^ m))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a =
        (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]
    rw [hswap]
    rw [neg_neg] at key
    exact ⟨fun u hd hd' => key.1 u hd' hd,
      fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩
  · obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₁ h1
    exact eval ψ hψ e he _ _ w _ _ hw

end GlobalTheory.KummerEisensteinGalois.ChSum
end

open GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveChar_doubleSum_primePow_eval : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  atlas_forward_decl GlobalTheory.KummerEisensteinGalois.ChSum.charSum
end

section
open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UnitPiece

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in

theorem sum_antidiag (n : ℕ) (G : ℤ → ℤ → K) :
    ∑ q ∈ (n : ℤ).divisorsAntidiag, G q.1 q.2 =
      ∑ d ∈ n.divisors, (G ((n / d : ℕ) : ℤ) d + G (-((n / d : ℕ) : ℤ)) (-(d : ℤ))) := by
  rw [Int.divisorsAntidiag_natCast, sum_disjUnion, sum_map, sum_map, ← sum_add_distrib]
  exact Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => G a b + G (-(a : ℤ)) (-(b : ℤ)))

theorem coefPos_eq (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) :
    coefPos j M ζ a₁ a₂ n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if q.1 ≡ a₁ [ZMOD M] then (q.2.sign : K) * ((q.1 : K) / M) ^ (j - 1) * ζ ^ (a₂ * q.2) else 0 := by
  rw [sum_antidiag n (fun A d => if A ≡ a₁ [ZMOD M] then (d.sign : K) * ((A : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0)]
  unfold coefPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0, sub_eq_add_neg]
  congr 1
  · split_ifs <;> simp [-Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]
  · split_ifs <;> simp [neg_div, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem ffPos_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) :
    ffPos N p m k ψ x t ζ false n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * q.2)) else 0 := by
  rw [sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d)) else 0)]
  unfold ffPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]

theorem eePos_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) :
    eePos N p m ψ t ζ false n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 then
        (q.2.sign : K) * (ψ⁻¹ (q.2 : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * q.2)) else 0 := by
  rw [sum_antidiag n (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d then
        (d.sign : K) * (ψ⁻¹ (d : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d)) else 0)]
  unfold eePos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one, mul_neg]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ n / d <;> simp [h1, h2, sub_eq_add_neg]

def primeTo (p m : ℕ) [NeZero p] : Finset (ZMod (p ^ m)) := univ.filter fun c => ¬ p ∣ c.val

omit [CharZero K] in

theorem sum_unitSet (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m))
    (H : ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ γ ∈ unitSet p m, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det.val : ℕ) : ZMod (p ^ m)) *
      H ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1)
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b := by
  have e : ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b =
      ∑ w ∈ primeTo p m ×ˢ ((univ : Finset (ZMod (p ^ m))) ×ˢ (primeTo p m ×ˢ (univ : Finset (ZMod (p ^ m))))),
        ψ (w.1 * w.2.2.2 - w.2.1 * w.2.2.1) * H w.1 w.2.1 w.2.2.1 w.2.2.2 := by
    simp only [sum_product]
  rw [e]
  refine sum_of_injOn (fun γ : GL (Fin 2) (ZMod (p ^ m)) =>
    ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1,
     (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1)) ?_ ?_ ?_ ?_
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  · intro γ hγ
    simpa [unitSet, primeTo] using hγ
  · rintro ⟨u, a, v, b⟩ hw hn
    by_cases hu : IsUnit (u * b - a * v)
    · exfalso
      apply hn
      refine ⟨Matrix.GeneralLinearGroup.mk'' !![u, a; v, b] (by simpa [Matrix.det_fin_two] using hu), ?_, ?_⟩
      · simpa [unitSet, primeTo] using hw
      · simp
    · simp only
      rw [MulChar.map_nonunit _ hu, zero_mul]
  · intro γ _
    simp only [ZMod.natCast_zmod_val, Matrix.det_fin_two]

theorem dvd_val_iff (p m : ℕ) [NeZero p] (hm : 1 ≤ m) (z : ℤ) :
    p ∣ (z : ZMod (p ^ m)).val ↔ (p : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, ZMod.val_intCast]
  have h : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by omega)
  rw [Int.emod_def]
  exact dvd_sub_left (h.mul_right _)

theorem row_sum (p m N j : ℕ) [NeZero p] (hm : 1 ≤ m) (hN : 0 < N) (ζ : K) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val) (s a) (N * n) =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then
      (q.2.sign : K) * ((q.1 : K) / (p : K) ^ m) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ (q.1 : ZMod (p ^ m)) a * ζ ^ (s a * q.2) else 0 := by
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val) (s a) (N * n) =
      ∑ q ∈ ((N * n : ℕ) : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, ← sum_product', ← sum_filter, ← sum_filter]
  symm
  refine sum_bij (fun q _ => ((q.1 : ZMod (p ^ m)), ((N : ℤ) * q.1, q.2))) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hq, hp⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Int.mem_divisorsAntidiag.mp hq
    refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · simpa [primeTo, dvd_val_iff p m hm] using hp
    · push_cast; rw [← h1]; ring
    · push_cast; exact mul_ne_zero hN' h2
    · simp only [ZMod.val_intCast]
      rw [Nat.cast_mul]
      exact (Int.mod_modEq _ _).symm.mul_left'
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.2.1) h.2.2
  · rintro ⟨u, A, d⟩ hw
    obtain ⟨hw, hA⟩ := mem_filter.mp hw
    obtain ⟨hu, hq⟩ := mem_product.mp hw
    obtain ⟨h1, h2⟩ := Int.mem_divisorsAntidiag.mp hq
    simp only at h1 hA hu
    obtain ⟨c, hc⟩ := hA.dvd
    have hA' : A = N * (u.val - (p ^ m : ℕ) * c) := by push_cast at hc ⊢; linear_combination -hc
    have hcast : (((u.val : ℤ) - (p ^ m : ℕ) * c : ℤ) : ZMod (p ^ m)) = u := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
    refine ⟨((u.val : ℤ) - (p ^ m : ℕ) * c, d), mem_filter.mpr ⟨Int.mem_divisorsAntidiag.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · apply mul_left_cancel₀ hN'
      rw [← mul_assoc, ← hA', h1]; push_cast; ring
    · intro h; apply h2; push_cast; rw [h, mul_zero]
    · rw [← dvd_val_iff p m hm, hcast]
      exact (mem_filter.mp hu).2
    · simp only [hcast, ← hA']
  · intro q _
    simp only
    congr 3
    push_cast
    field_simp

theorem col_sum (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (y₁ y₂ n₁ n₂ d d' : ℤ)
    (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₁ * d)) *
          (ψ⁻¹ (d' : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₂ * d')) else 0 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : 0 < N * p ^ m := Nat.mul_pos hN (pow_pos hp.pos m)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have hζN : IsPrimitiveRoot (ζ ^ N) (p ^ m) := hζ.pow hpos rfl
  have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self _ (by omega)
  have hunit : ∀ z : ℤ, IsUnit (z : ZMod (p ^ m)) ↔ ¬ (p : ℤ) ∣ z := by
    intro z
    rw [← dvd_val_iff p m hm, ← ZMod.natCast_zmod_val (z : ZMod (p ^ m)), ZMod.isUnit_iff_coprime,
      Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.natCast_zmod_val]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  obtain ⟨c1, c2⟩ := GlobalTheory.T.primitiveChar_doubleSum_primePow_eval p m K ψ (ζ ^ N) hm hψ hζN n₁ n₂ d d' (fun h => h₁ h.1)
  have e : ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      (∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
        (ζ ^ N) ^ ((a.val : ℤ) * d + (b.val : ℤ) * d')) *
        ((ζ ^ (p ^ m)) ^ (y₁ * d) * (ζ ^ (p ^ m)) ^ (y₂ * d')) := by
    simp only [sum_mul]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm a, mul_assoc, mul_assoc, ← zpow_natCast ζ N, ← zpow_natCast ζ (p ^ m), ← zpow_mul, ← zpow_mul,
      ← zpow_mul, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0]
    congr 2
    push_cast; ring
  rw [e]
  obtain ⟨w, hw⟩ := (hunit n₁).mpr h₁
  split_ifs with hc
  · obtain ⟨hs, -, hd'⟩ := hc
    obtain ⟨v, hv⟩ := (hunit d').mpr hd'
    rw [hdvd] at hs
    push_cast at hs
    rw [← hw, ← hv] at hs
    have hww : ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * w = 1 := w.inv_mul
    rw [c1 (v * w⁻¹) ?_ ?_]
    · have : ψ⁻¹ ((v * w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) = ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (d' : ZMod (p ^ m)) := by
        rw [Units.val_mul, map_mul, ← hw, ← hv, mul_comm]
        congr 1
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [this]; ring
    · rw [Units.val_mul]
      linear_combination ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * hs - (d : ZMod (p ^ m)) * hww
    · rw [Units.val_mul, ← hw, ← hv]
      linear_combination (-(v : ZMod (p ^ m))) * hww
  · rw [c2, zero_mul]
    rintro ⟨u, hd, hd'⟩
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hdvd]; push_cast; rw [hd, hd']; ring
    · rw [← hunit, hd]; exact u.isUnit.mul ((hunit n₂).mpr h₂).neg
    · rw [← hunit, hd']; exact u.isUnit.mul ((hunit n₁).mpr h₁)

theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (x t : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * t) (N * j)) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (((p : K) ^ m) ^ (k - 2))⁻¹ *
      (ffPos N p m k ψ x t ζ false i * eePos N p m ψ t ζ false j) else 0 := by
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * t) (N * j)) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * (q.1 : ZMod (p ^ m))) *
          ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * t) * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * (x * t)) (N * i) := by
    intro u a
    have := row_sum p m N 1 hm hN ζ (fun b => (N : ℤ) * b.val + (p : ℤ) ^ m * t) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hN ζ (fun a => (N : ℤ) * a.val + (p : ℤ) ^ m * (x * t))
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * (q.1 : ZMod (p ^ m))) *
          ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * t) * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffPos_eq, eePos_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  rw [if_pos h₁]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  simp only [if_pos h₂, mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum p m N hm hN ψ hψ ζ hζ (x * t) t q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

omit [CharZero K] in

theorem sum_affine (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (u c : ZMod (p ^ m)) (hu : IsUnit u) : ∑ b : ZMod (p ^ m), ψ (u * b + c) = 0 := by
  have hp : p.Prime := Fact.out
  have hne : ψ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hψ
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne hψ
  obtain ⟨w, rfl⟩ := hu
  rw [← MulChar.sum_eq_zero_of_ne_one hne]
  exact Equiv.sum_comp ((Units.mulLeft w).trans (Equiv.addRight c)) ψ

theorem isUnit_of_mem (p m : ℕ) [Fact p.Prime] {u : ZMod (p ^ m)} (hu : u ∈ primeTo p m) : IsUnit u := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hu).2).symm).pow_right m

omit [CharZero K] in

theorem sum_zero_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → K) (g : ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u * g v b) = 0 := by
  refine sum_eq_zero fun u _ => ?_
  rw [sum_comm]
  refine sum_eq_zero fun v hv => ?_
  rw [sum_comm]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_mul, ← zero_mul (f u * g v b), ← sum_affine p m hm ψ hψ (-v) (u * b) (isUnit_of_mem p m hv).neg]
  congr 1
  exact sum_congr rfl fun a _ => by congr 1; ring

omit [CharZero K] in

theorem sum_zero_right (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → ZMod (p ^ m) → K) (g : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u a * g v) = 0 := by
  refine sum_eq_zero fun u hu => sum_eq_zero fun a _ => sum_eq_zero fun v _ => ?_
  rw [← sum_mul, ← zero_mul (f u a * g v), ← sum_affine p m hm ψ hψ u (-(a * v)) (isUnit_of_mem p m hu)]
  simp only [sub_eq_add_neg]

theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val := by
        intro h
        have h' : N * p ^ m ∣ N * v.val := by exact_mod_cast h
        exact (mem_filter.mp hv).2 ((dvd_pow_self p (by omega)).trans (Nat.dvd_of_mul_dvd_mul_left hN h'))
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPiece
end

section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem ffMu_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a₀ : ℤ) (s : ℕ) :
    ffMu N p m k ψ a₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ a₀ [ZMOD N] then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ a₀ [ZMOD N] then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2)) else 0)]
  unfold ffMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem eeMu_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b₀ : ℤ) (s : ℕ) :
    eeMu N p m ψ b₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ b₀ [ZMOD N] then
        (q.2.sign : K) * ψ⁻¹ (q.2 : ZMod (p ^ m)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ b₀ [ZMOD N] then
        (d.sign : K) * ψ⁻¹ (d : ZMod (p ^ m)) else 0)]
  unfold eeMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  have hp : p.Prime := Fact.out
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val + (p : ℤ) ^ m * y) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val + (p : ℤ) ^ m * y := by
        intro h
        have h1 : (p : ℤ) ^ m ∣ N * v.val + (p : ℤ) ^ m * y :=
          (show (p : ℤ) ^ m ∣ ((N * p ^ m : ℕ) : ℤ) by push_cast; exact dvd_mul_left _ _).trans h
        have h2 : (p : ℤ) ∣ (N : ℤ) * v.val := by
          have := dvd_sub h1 (dvd_mul_right ((p : ℤ) ^ m) y)
          rw [add_sub_cancel_right] at this
          exact (dvd_pow_self (p : ℤ) (by omega)).trans this
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h3 | h3
        · exact hpN (Int.natCast_dvd_natCast.mp h3)
        · exact (mem_filter.mp hv).2 (Int.natCast_dvd_natCast.mp h3)
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

section
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem isUnit_iff_not_dvd_val (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (c : ZMod (p ^ m)) :
    IsUnit c ↔ ¬ p ∣ c.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem isUnit_natCast_of_not_dvd (p m N : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) : IsUnit (N : ZMod (p ^ m)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m

omit [CharZero K] in

theorem sum_pick (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (x z : ℤ) (F : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, (if z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then F u else 0) =
    if ¬ (p : ℤ) ∣ z ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N] then
      F ((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) else 0 := by
  have hp : p.Prime := Fact.out
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have h1 : (N : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) = 1 := Ring.mul_inverse_cancel _ hU
  have hP : (p : ZMod (p ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hcop : (N : ℤ).natAbs.Coprime ((p ^ m : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m
  have key : ∀ u : ZMod (p ^ m), z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] ↔
      (u = (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N]) := by
    intro u
    rw [Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hcop, and_comm]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hP, zero_mul, add_zero]
      constructor
      · intro h; rw [h]; linear_combination (-u) * h1
      · intro h; rw [h]; linear_combination (-(z : ZMod (p ^ m))) * h1
    · rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, add_sub_assoc]
      exact dvd_add_right (dvd_mul_right _ _)
  have hmem : (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∈ primeTo p m ↔ ¬ (p : ℤ) ∣ z := by
    rw [primeTo, mem_filter, ← isUnit_iff_not_dvd_val p m hm, ← dvd_val_iff p m hm, ← isUnit_iff_not_dvd_val p m hm,
      IsUnit.mul_iff]
    simp [hU.ringInverse]
  simp only [key]
  by_cases hx : z ≡ (p : ℤ) ^ m * x [ZMOD N]
  · simp only [hx, and_true, sum_ite_eq', hmem]
  · simp [hx]

theorem row_sum (p m N j : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (ζ : K) (x : ℤ) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m),
      Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ (p : ℤ) ^ m * x [ZMOD N] then
      (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) a * ζ ^ (s a * q.2)
      else 0 := by
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
      ∑ q ∈ (n : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  exact sum_pick p m N hm hpN x q.1 (fun u => (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
    ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2))

theorem col_sum_div (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (n₁ n₂ d d' : ℤ) (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m),
      ψ ((n₁ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) * b -
        a * ((n₂ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
        ζ ^ ((N : ℤ) * b.val * d')) * ζ ^ ((N : ℤ) * a.val * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (N : ZMod (p ^ m))) *
          ψ⁻¹ (d' : ZMod (p ^ m)) else 0 := by
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have hI := hU.ringInverse
  have hval : ∀ z : ℤ, ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ ((((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))).val : ℕ) : ℤ) := by
    intro z hz
    rw [Int.natCast_dvd_natCast, ← isUnit_iff_not_dvd_val p m hm]
    refine IsUnit.mul ?_ hI
    rwa [isUnit_iff_not_dvd_val p m hm, dvd_val_iff p m hm]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  have h := col_sum p m N hm hN ψ hψ ζ hζ 0 0 _ _ d d' (hval n₁ h₁) (hval n₂ h₂)
  simp only [mul_zero, add_zero, zero_mul, zpow_zero, mul_one, hdvd, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] at h
  rw [h, map_mul, ← MulChar.inv_apply]
  refine if_congr (and_congr_left' ?_) rfl rfl
  rw [hdvd, ← hI.mul_left_eq_zero (a := ((n₁ * d + n₂ * d' : ℤ) : ZMod (p ^ m)))]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (hm : 1 ≤ m) (hN : 0 < N)
    (hpN : ¬ p ∣ N) (_hk : 3 ≤ k) (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
      (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  have hx : ∀ c z : ℤ, z ≡ (p : ℤ) ^ m * (c * t) [ZMOD N] ↔ z ≡ c [ZMOD N] := by
    intro c z
    have h : (p : ℤ) ^ m * (c * t) ≡ c [ZMOD N] := by
      have := ht.mul_left c
      rwa [mul_one, mul_left_comm] at this
    exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i := by
    intro u a
    have := row_sum p m N 1 hm hpN ζ (b₀ * t) (fun b => (N : ℤ) * b.val) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one, hx] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hpN ζ (a₀ * t) (fun a => (N : ℤ) * a.val)
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffMu_eq, eeMu_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  simp only [hx]
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  by_cases g₁ : q.1 ≡ a₀ [ZMOD N]
  swap
  · simp [g₁]
  rw [if_pos ⟨h₁, g₁⟩]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  by_cases g₂ : q'.1 ≡ b₀ [ZMOD N]
  swap
  · simp [g₂]
  simp only [if_pos (And.intro h₂ g₂), mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum_div p m N hm hN hpN ψ hψ ζ hζ q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, g₁, g₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product : ∀ (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K], 1 ≤ m → 0 < N → ¬ p ∣ N → 3 ≤ k → ∀ (ψ : DirichletCharacter K (p ^ m)), ψ.IsPrimitive → ∀ (ζ : K), IsPrimitiveRoot ζ (N * p ^ m) → ∀ (a₀ b₀ t : ℤ), (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ (i j : ℕ), ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i * coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) = if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  atlas_forward_decl GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum
end

section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem pieceTRaw_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y : ℤ) (r : ℕ) :
    pieceTRaw N p m m k ψ (x, 0) (y, 0) ζ (unitSet p m) r = -((p : K) ^ ((m : ℤ) * ((k : ℤ) - 4))) *
      ∑ i ∈ range (r + 1),
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i)) := by
  unfold pieceTRaw cmul
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := drop_const p m N k hm hpN hk ψ hψ ζ x y 0 0 i (r - i)
  simp only [mul_zero, add_zero] at h
  rw [← h]
  have e := sum_unitSet p m ψ (fun u a v b =>
    eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i))
  rw [← e]
  refine sum_congr rfl fun γ _ => ?_
  simp [rowT]

theorem coef_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (r : ℕ) :
    pieceTRaw N p m m k ψ (a₀ * t, 0) (b₀ * t, 0) ζ (unitSet p m) r =
      if p ^ m ∣ r then -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
        (N : K) ^ ((2 : ℤ) - k) * coPtMu N p m k ψ a₀ b₀ r else 0 := by
  have hp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [pieceTRaw_eq p m N k hm hpN hk ψ hψ ζ]
  rw [sum_congr rfl fun i hi => by
    rw [GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product p m N k K hm hN hpN hk ψ hψ ζ hζ a₀ b₀ t ht,
      Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]]
  split_ifs with h
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e' : (p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹ = (p : K) ^ (-(m : ℤ)) * (N : K) ^ ((2 : ℤ) - ((k' + 2 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel, zpow_mul]
      push_cast
      rw [show ((k' : ℤ) + 2 - 4) = (k' : ℤ) - 2 by ring, show (2 : ℤ) - (k' + 2) = -(k' : ℤ) by ring,
        zpow_sub₀ (zpow_ne_zero _ hpK), zpow_neg, zpow_neg]
      simp only [zpow_natCast]
      field_simp
      ring
    unfold coPtMu cmul
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    calc _ = -((p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
          (ffMu N p m (k' + 2) ψ a₀ i * eeMu N p m ψ b₀ (r - i)) := by ring
      _ = _ := by rw [e']; ring
  · simp

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu

theorem GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (coPtMu N p m k ψ a b) r := by
  intro p _ N m k K _ _ ψ a b t ζ _ hζ hN hpN hm hk hψ ht
  refine ⟨fun r hr => ?_, fun r => ?_⟩
  · rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_neg hr]
  · unfold toQ up
    rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_pos (dvd_mul_right _ _)]
end

section
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LambdaValuationPowers

theorem pieceT_unitSet_muModel_smoothedSb : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (GlobalTheory.LambdaValuationPowers.coPtSb N p m k ψ c d a b) r := by
  intro p _ N m k K _ _ ψ c d a b t ζ hp2 hζ hN hpN hm hk hψ hc hd ht
  have hS : ∀ r : ℕ, pieceT N p m m k ψ c d (a * t, 0) (b * t, 0) ζ (unitSet p m) r = _ := fun r =>
    GlobalTheory.TameSmoothing.pieceT_unitSet_eq_four_pieceTRaw p N m m k K ψ c d (a * t, 0) (b * t, 0) ζ hζ hN hpN hm le_rfl hk hc hd r
  have e1 : ((c * (a * t), c * 0) : ℤ × ℤ) = (c * a * t, 0) := by ext <;> simp [mul_assoc]
  have e2 : ((d * (b * t), d * 0) : ℤ × ℤ) = (d * b * t, 0) := by ext <;> simp [mul_assoc]
  simp only [e1, e2] at hS
  obtain ⟨I1, T1⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I2, T2⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) b t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I3, T3⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ a (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  obtain ⟨I4, T4⟩ := GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq p N m k K ψ (c * a) (d * b) t ζ hp2 hζ hN hpN hm hk hψ ht
  refine ⟨fun n hn => ?_, fun r => ?_⟩
  · rw [hS n, I1 n hn, I2 n hn, I3 n hn, I4 n hn]; ring
  · simp only [toQ, up] at T1 T2 T3 T4 ⊢
    rw [hS, T1, T2, T3, T4]
    simp only [coPtSb]
    ring

end GlobalTheory.LambdaValuationPowers
end
