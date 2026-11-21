import ReciprocityTheory.DualLattices.TensorSpan
import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem int (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le

theorem v_eq_one {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h

theorem ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1

end IsTeich

def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)

def sS (ω : ZMod p → C) : C := ∑ b, wt ω b

def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0

def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a

section wt

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem wt_mul (a b : ZMod p) : wt ω (a * b) = wt ω a * wt ω b := by
  unfold wt
  rw [hω.mul, mul_pow]

theorem wt_zero : wt ω 0 = 0 := by
  unfold wt
  rw [hω.zero]
  exact zero_pow (by have := hp.out.two_le; omega)

theorem wt_mul_self {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]

theorem wt_inv {a : ZMod p} (ha : a ≠ 0) : wt ω a⁻¹ = ω a := by
  have h1 := hω.wt_mul_self (inv_ne_zero ha)
  have h2 : ω a⁻¹ * ω a = 1 := by
    rw [← hω.mul, inv_mul_cancel₀ ha, hω.one]
  calc wt ω a⁻¹ = wt ω a⁻¹ * (ω a⁻¹ * ω a) := by rw [h2, mul_one]
    _ = ω a := by rw [← mul_assoc, h1, one_mul]

theorem wt_int (a : ZMod p) : v (wt ω a) ≤ 1 := by
  unfold wt
  rw [map_pow]
  exact pow_le_one₀ (zero_le) (hω.int a)

private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem lam_scale (φ : ZMod p → C) (h : ZMod p) :
    ∑ a, u0 ω a * φ (h * a) = ω h * ∑ a, u0 ω a * φ a := by
  have e : ∀ g : ZMod p → C, ∑ a, u0 ω a * g a = ∑ a, wt ω a * (g a - g 0) :=
    fun g => lam_eq_sum_wt_mul_sub hω g
  rw [e (fun a => φ (h * a)), e φ]
  simp only [mul_zero]
  by_cases hh : h = 0
  · subst hh
    simp [hω.zero]
  · rw [Finset.mul_sum]
    calc ∑ a, wt ω a * (φ (h * a) - φ 0)
        = ∑ a, (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0)) (Equiv.mulLeft₀ h hh a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [inv_mul_cancel_left₀ hh]
      _ = ∑ b, wt ω (h⁻¹ * b) * (φ b - φ 0) := Equiv.sum_comp (Equiv.mulLeft₀ h hh) (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0))
      _ = ∑ b, ω h * (wt ω b * (φ b - φ 0)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hω.wt_mul, hω.wt_inv hh]
          ring

theorem lam_eq (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f

theorem lam_omega : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp

end IsTeich

end wt

theorem lam_sum (ω : ZMod p → C) {ι : Type} [Fintype ι] (c : ι → C) (g : ι → ZMod p → C) :
    lam ω (fun a => ∑ j, c j * g j a) = ∑ j, c j * lam ω (g j) := by
  unfold lam
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

section hopf

variable (hv : v.Integers R)
include hv

theorem cmul_mem {X : Type} (M : Submodule R (X → C)) {c : C} (hc : v c ≤ 1) {f : X → C}
    (hf : f ∈ M) : (fun t => c * f t) ∈ M := by
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hc
  have e : (fun t => c * f t) = r • f := by
    funext t
    simp [Algebra.smul_def, hr]
  rw [e]
  exact M.smul_mem r hf

omit hv in
theorem pow_mem' (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AA.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact AA.mul_mem _ _ ih hf

omit hv in
theorem scale_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (b : ZMod p) : (fun t => f (b * t)) ∈ AA.carrier := by
  have key : ∀ α β : ZMod p → ZMod p,
      (∀ g ∈ AA.carrier, (fun t => g (α t)) ∈ AA.carrier) →
      (∀ g ∈ AA.carrier, (fun t => g (β t)) ∈ AA.carrier) →
      ∀ F ∈ tensorSpan R AA.carrier, (fun t => F (α t, β t)) ∈ AA.carrier := by
    intro α β hα hβ F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, k, hk, rfl⟩ := hx
      exact AA.mul_mem _ _ (hα g hg) (hβ k hk)
    | zero => exact AA.carrier.zero_mem
    | add x y _ _ hx hy => exact AA.carrier.add_mem hx hy
    | smul a x _ hx => exact AA.carrier.smul_mem a hx
  have hn : ∀ n : ℕ, ∀ g ∈ AA.carrier, (fun t => g ((n : ZMod p) * t)) ∈ AA.carrier := by
    intro n
    induction n with
    | zero =>
      intro g hg
      have e : (fun t => g (((0 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) (t, -t) := by
        funext t
        simp [addPull]
      rw [e]
      exact key (fun t => t) (fun t => -t) (fun g hg => hg) (fun g hg => AA.antipode g hg) _
        (AA.comul g hg)
    | succ n ih =>
      intro g hg
      have e : (fun t => g (((n + 1 : ℕ) : ZMod p) * t)) =
          fun t => (addPull R (ZMod p) g) ((n : ZMod p) * t, t) := by
        funext t
        simp [addPull, add_mul]
      rw [e]
      exact key (fun t => (n : ZMod p) * t) (fun t => t) ih (fun g hg => hg) _ (AA.comul g hg)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h := hn b.val f hf
  simpa [ZMod.natCast_zmod_val] using h

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem lam_omega_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C}
    (hf : f ∈ AA.carrier) : (fun t => lam ω f * ω t) ∈ AA.carrier := by
  have hS : v (sS ω) ≤ 1 := by
    unfold sS
    exact v.map_sum_le fun b _ => hω.wt_int b
  have hu : ∀ a, v (u0 ω a) ≤ 1 := fun a => by
    unfold u0
    split_ifs
    · exact (v.map_sub _ _).trans (max_le (hω.wt_int a) hS)
    · rw [sub_zero]
      exact hω.wt_int a
  have key : (fun t => lam ω f * ω t) = ∑ a, (fun t => u0 ω a * f (a * t)) := by
    funext t
    simp only [Finset.sum_apply, lam]
    rw [mul_comm (∑ a, u0 ω a * f a) (ω t), ← hω.lam_scale f t]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm t a]
  rw [key]
  exact Submodule.sum_mem _ fun a _ => cmul_mem hv AA.carrier (hu a) (scale_mem AA hf a)

theorem exists_gen (AA : HopfOrder (C := C) R (ZMod p)) [CharZero C] :
    ∃ x1 : C, x1 ≠ 0 ∧ (fun t => x1 * ω t) ∈ AA.carrier ∧
      ∀ f ∈ AA.carrier, ∃ r : R, lam ω f = x1 * algebraMap R C r := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  set b : ZMod p → ZMod p → C := fun j x => B x j with hb
  have hbA : ∀ j, b j ∈ AA.carrier := fun j => by
    rw [hA]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_max_image Finset.univ (fun j => v (lam ω (b j))) Finset.univ_nonempty
  have hx1 : lam ω (b j0) ≠ 0 := by
    intro h0
    have hall : ∀ j, lam ω (b j) = 0 := fun j => by
      have h := hj0 j (Finset.mem_univ _)
      rw [h0, map_zero] at h
      exact (Valuation.zero_iff v).mp (le_antisymm h (zero_le))
    have hω' : ω = fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a := by
      funext a
      have h := congrFun (show B *ᵥ (B⁻¹ *ᵥ ω) = ω by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]) a
      rw [← h]
      simp [Matrix.mulVec, dotProduct, hb, mul_comm]
    have hl : lam ω ω = 0 :=
      calc lam ω ω = lam ω (fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a) := congrArg (lam ω) hω'
        _ = ∑ j, (B⁻¹ *ᵥ ω) j * lam ω (b j) := lam_sum ω _ b
        _ = 0 := by simp [hall]
    rw [hω.lam_omega] at hl
    exact sub_ne_zero.mpr (Nat.cast_ne_one.mpr hp.out.one_lt.ne') hl
  have hr : ∀ j, ∃ r : R, lam ω (b j) = lam ω (b j0) * algebraMap R C r := fun j => by
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := lam ω (b j) / lam ω (b j0)) (by
      rw [map_div₀]
      exact div_le_one_of_le₀ (hj0 j (Finset.mem_univ _)) (zero_le))
    exact ⟨r, by rw [hr]; field_simp⟩
  choose r hr using hr
  refine ⟨lam ω (b j0), hx1, lam_omega_mem hv hω AA (hbA j0), ?_⟩
  intro f hf
  rw [hA] at hf
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨∑ j, c j * r j, ?_⟩
  have e : (∑ i, c i • b i) = fun a => ∑ j, algebraMap R C (c j) * b j a := by
    funext a
    simp [Finset.sum_apply, Algebra.smul_def]
  rw [e, lam_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hr j, map_mul]
  ring

end hopf

end ReciprocityTheory.PGsh.Up.U3
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem exists_charEquiv [NeZero p] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ZMod p ≃ AddChar (ZMod p) C, (∀ h h', e (h + h') = e h * e h') ∧
      ∀ h a, e h a = ζ ^ (h * a).val := by
  have hp1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) C := AddChar.zmodChar p hp1
  have hψ : ∀ a, ψ a = ζ ^ a.val := fun a => AddChar.zmodChar_apply hp1 a
  let f : ZMod p → AddChar (ZMod p) C := fun h => ψ.mulShift h
  have hf : ∀ h a, f h a = ζ ^ (h * a).val := fun h a => by
    simp only [f, AddChar.mulShift_apply, hψ]
  have hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val := by
    intro χ a
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]
    exact AddChar.map_nsmul_eq_pow χ _ _
  have hinj : Function.Injective f := by
    intro h h' hh
    have := congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh
    simp only [hf, mul_one] at this
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)
  have hsurj : Function.Surjective f := by
    intro χ
    have h1 : χ 1 ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    obtain ⟨k, hk, hkχ⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(k : ZMod p), ?_⟩
    ext a
    rw [hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro h h'
    ext a
    show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul,
      AddChar.map_add_eq_mul]
  · intro h a
    exact hf h a

theorem v_gamma (hv : v.Integers R) (hpv : v (p : C) < 1) {ω : ZMod p → C} (hω : IsTeich v ω)
    {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    v (∑ a, u0 ω a * ζ ^ a.val) ^ (p - 1) = v (p : C) := by
  have hpp : 2 ≤ p := hp.out.two_le
  have hζ1 : v ζ ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 := one_lt_pow₀ h (show p ≠ 0 by omega)
    rw [← map_pow, hζ.pow_eq_one, map_one] at h2
    exact lt_irrefl _ h2
  have hπ1 : v (ζ - 1) < 1 := by
    by_contra h
    push_neg at h
    have h2 := one_le_pow₀ (n := p - 1) h
    rw [val_prim_root hζ] at h2
    exact absurd hpv (not_lt.mpr h2)
  have hnat : ∀ n : ℕ, v (n : C) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact Valuation.map_add_le v ih (by rw [map_one])
  have hdec : ∀ n : ℕ, ∃ s : C, v s ≤ 1 ∧ ζ ^ n - 1 = (ζ - 1) * (n + (ζ - 1) * s) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs1, hs⟩ := ih
      refine ⟨n + ζ * s, Valuation.map_add_le v (hnat n) (by rw [map_mul]; exact mul_le_one' hζ1 hs1), ?_⟩
      push_cast
      linear_combination ζ * hs
  choose s hs1 hs using hdec
  have h1 : ∑ a, u0 ω a * ζ ^ a.val = ∑ a, wt ω a * (ζ ^ a.val - 1) := by
    have := hω.lam_eq (fun a => ζ ^ a.val)
    simpa [lam, ZMod.val_zero] using this
  have h2 : ∑ a, wt ω a * ω a = (p : C) - 1 := by
    have := hω.lam_eq ω
    rw [hω.lam_omega, hω.zero] at this
    simpa using this.symm
  have hγ : ∑ a, u0 ω a * ζ ^ a.val = (ζ - 1) * (((p : C) - 1) +
      (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val)) := by
    rw [h1, ← h2]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs]
    ring
  have hδ : v (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val) < 1 := by
    apply Valuation.map_add_lt v
    · apply Valuation.map_sum_lt v one_ne_zero
      intro a _
      rw [map_mul]
      calc v (wt ω a) * v ((a.val : C) - ω a) ≤ 1 * v ((a.val : C) - ω a) := by
            gcongr; exact hω.wt_int a
        _ < 1 := by rw [one_mul, Valuation.map_sub_swap]; exact hω.cong a
    · rw [map_mul]
      have hsum : v (∑ a, wt ω a * s a.val) ≤ 1 :=
        Valuation.map_sum_le v fun a _ => by rw [map_mul]; exact mul_le_one' (hω.wt_int a) (hs1 _)
      calc v (ζ - 1) * v (∑ a, wt ω a * s a.val) ≤ v (ζ - 1) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hπ1
  have hp1 : v ((p : C) - 1) = 1 := by
    have hnd : ¬ (p : ℤ) ∣ (p : ℤ) - 1 := by
      intro hd
      have h1' : (p : ℤ) ∣ 1 := by simpa using dvd_sub (dvd_refl (p : ℤ)) hd
      have := Int.eq_one_of_dvd_one (by positivity) h1'
      omega
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    exact this
  have hunit : v ((p : C) - 1 + (∑ a, wt ω a * ((a.val : C) - ω a) +
      (ζ - 1) * ∑ a, wt ω a * s a.val)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left v (by rw [hp1]; exact hδ), hp1]
  rw [hγ, map_mul, hunit, mul_one]
  exact val_prim_root hζ

theorem fourierMap_smul_lambdaWeight {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by
  have hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0 := by
    intro h hh
    have := hω.sep h 0 hh
    rw [hω.zero, sub_zero] at this
    intro h0
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1 := by
    intro h hh
    have e1 := hω.pow h
    have : ω h ^ (p - 1) * ω h = 1 * ω h := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]
    exact mul_right_cancel₀ (hω0 h hh) this
  have hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1 := by
    intro h hh
    simp only [wt]
    rw [← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]
  have hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b := by
    intro a b; simp only [wt, hω.mul, mul_pow]
  have hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h := by
    intro h hh
    have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have e1 := hwt h⁻¹ hi
    have e2 : ω h⁻¹ * ω h = 1 := by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]
    calc wt ω h⁻¹ = wt ω h⁻¹ * (ω h⁻¹ * ω h) := by rw [e2, mul_one]
      _ = ω h := by rw [← mul_assoc, e1, one_mul]
  have hwt0 : wt ω 0 = 0 := by
    simp only [wt, hω.zero]; exact zero_pow (by omega)
  have hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω := by
    intro h hh
    have := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)
    simp only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this
    simp only [sS]; exact this.symm
  have hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b := by
    intro h hh b
    simp only [u0]
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, if_true, hwt0]
      nth_rewrite 1 [hS h hh]; ring
    · have : h⁻¹ * b ≠ 0 := mul_ne_zero (inv_ne_zero hh) hb
      simp only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]
  funext h
  simp only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]
  by_cases hh : h = 0
  · subst hh
    simp only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]
    rw [← Finset.mul_sum]
    simp only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [sS]
  · have hb := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val)
      (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)
    rw [← hb]
    simp only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end ReciprocityTheory.PGsh.Up.U3
end
end
