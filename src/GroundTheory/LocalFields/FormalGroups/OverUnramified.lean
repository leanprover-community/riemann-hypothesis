import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLimitOfApprox
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup

section
namespace GroundTheory.LocalField.FormalGroup

open IsLocalRing

section Approximation

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem smodEq_pow_iff_sub_mem {x y : R} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem exists_limit_of_approx [IsPrecomplete I R] (P : ℕ → R → Prop)
    (hstep : ∀ n x, P n x → ∃ y, y - x ∈ I ^ n ∧ P (n + 1) y) {x₀ : R} (h₀ : P 0 x₀) :
    ∃ x, ∀ n, ∃ y, P n y ∧ x - y ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx <;> assumption

theorem exists_eq_zero_of_approx [IsAdicComplete I R] (F : R → R)
    (hF : ∀ n x y, x - y ∈ I ^ n → F x - F y ∈ I ^ n)
    (hstep : ∀ n x, F x ∈ I ^ n → ∃ y, y - x ∈ I ^ n ∧ F y ∈ I ^ (n + 1))
    {m : ℕ} {x₀ : R} (h₀ : F x₀ ∈ I ^ m) : ∃ x, F x = 0 ∧ x - x₀ ∈ I ^ m := by
  obtain ⟨x, hx⟩ := exists_limit_of_approx I (fun n y => F y ∈ I ^ (m + n) ∧ y - x₀ ∈ I ^ m)
    (fun n y ⟨h1, h2⟩ => by
      obtain ⟨z, hz1, hz2⟩ := hstep (m + n) y h1
      refine ⟨z, Ideal.pow_le_pow_right (by omega) hz1, hz2, ?_⟩
      have e : z - x₀ = (z - y) + (y - x₀) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hz1) h2)
    ⟨by simpa using h₀, by simp⟩
  refine ⟨x, ?_, ?_⟩
  · refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨y, ⟨hy1, _⟩, hy⟩ := hx n
    have e : F x = (F x - F y) + F y := by ring
    rw [e]
    exact Ideal.add_mem _ (hF n x y hy) (Ideal.pow_le_pow_right (by omega) hy1)
  · obtain ⟨y, ⟨_, hy2⟩, hy⟩ := hx m
    have e : x - x₀ = (x - y) + (y - x₀) := by ring
    rw [e]
    exact Ideal.add_mem _ hy hy2

end Approximation

section HidaSetting

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

theorem irreducible_algebraMap (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    {π : A} (hπ : Irreducible π) : Irreducible (algebraMap A B π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hunr, hπ, Ideal.map_span, Set.image_singleton]

theorem mem_maximalIdeal_pow_iff {ϖ : B} (hϖ : Irreducible ϖ) {x : B} {n : ℕ} :
    x ∈ maximalIdeal B ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

end HidaSetting

section Solve

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)]
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

theorem one_lt_card_residueField : 1 < Nat.card (ResidueField A) :=
  Finite.one_lt_card

include hσ in

theorem exists_residue_sub_mul_add_eq_zero (v w : B) :
    ∃ z : B, residue B (σ z - v * z + w) = 0 := by
  open Polynomial in
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  set a := residue B v
  set b := residue B w
  have hlow : (C b - C a * X : (ResidueField B)[X]).degree < (X ^ q : (ResidueField B)[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by omega : 0 < q))
    · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast hq)
  have hdeg : (X ^ q + (C b - C a * X) : (ResidueField B)[X]).degree = q := by
    rw [degree_add_eq_left_of_degree_lt hlow, degree_X_pow]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q + (C b - C a * X) : (ResidueField B)[X])
    (by rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  obtain ⟨z', rfl⟩ := residue_surjective z
  refine ⟨z', ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hz
  rw [map_add, map_sub, map_mul, hσ]
  linear_combination hz

variable {π : A} (hπB : Irreducible (algebraMap A B π))
include hσ hπB

theorem exists_sub_mul_eq_of_mem [IsAdicComplete (maximalIdeal B) B] (v c : B) {m : ℕ} {x₀ : B}
    (h₀ : σ x₀ - v * x₀ - c ∈ maximalIdeal B ^ m) :
    ∃ x, σ x - v * x = c ∧ x - x₀ ∈ maximalIdeal B ^ m := by
  set ϖ := algebraMap A B π
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  obtain ⟨x, hx, hxm⟩ := exists_eq_zero_of_approx (maximalIdeal B) (fun x => σ x - v * x - c)
    (fun n x y hxy => by
      rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
      obtain ⟨t, ht⟩ := hxy
      refine ⟨σ t - v * t, ?_⟩
      have : x = y + ϖ ^ n * t := by rw [← ht]; ring
      simp only [this, map_add, hσϖ]
      ring)
    (fun n x hx => by
      rw [mem_maximalIdeal_pow_iff hπB] at hx
      obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz⟩ := exists_residue_sub_mul_add_eq_zero σ hσ v w
      rw [residue_eq_zero_iff, hπB.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨x + ϖ ^ n * z, ?_, ?_⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        exact ⟨z, by ring⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        refine ⟨t, ?_⟩
        simp only [map_add, hσϖ]
        have e : σ x - v * x - c = ϖ ^ n * w := hw
        linear_combination e + ϖ ^ n * ht)
    h₀
  exact ⟨x, sub_eq_zero.1 (by simpa using hx), hxm⟩


theorem exists_units_eq_mul [IsAdicComplete (maximalIdeal B) B] (v : Bˣ) :
    ∃ η : Bˣ, σ η = v * η := by
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue B v) (n := q - 1) (by omega)
  have hv0 : residue B v ≠ 0 := (residue_ne_zero_iff_isUnit _).2 v.isUnit
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact hv0 hz.symm
  obtain ⟨z', rfl⟩ := residue_surjective z
  have h₀ : σ z' - v * z' - 0 ∈ maximalIdeal B ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, sub_zero, map_sub, map_mul, hσ]
    have e : residue B z' ^ q = residue B z' ^ (q - 1) * residue B z' := by
      rw [← pow_succ]; congr 1; omega
    rw [e, hz, sub_self]
  obtain ⟨x, hx, hxm⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v 0 h₀
  have hxu : IsUnit x := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxm
    rwa [hxm]
  refine ⟨hxu.unit, ?_⟩
  simpa [sub_eq_zero] using hx

end Solve

section Kernel

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

include hunr hσ
end Kernel
end FormalGroup
end LocalField
end GroundTheory
end

section
namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {ι : Type*}

theorem map_substEach (g : PowerSeries A) (i : ι) :
    map φ (substEach g i : MvPowerSeries ι A) = substEach (PowerSeries.map φ g) i := by
  rw [substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]

theorem IsLubinTateLift.map [Finite ι] {f g : PowerSeries A}
    (hg0 : PowerSeries.constantCoeff g = 0) {ℓ Φ : MvPowerSeries ι A}
    (h : IsLubinTateLift f g ℓ Φ) :
    IsLubinTateLift (PowerSeries.map φ f) (PowerSeries.map φ g) (MvPowerSeries.map φ ℓ)
      (MvPowerSeries.map φ Φ) := by
  obtain ⟨h0, h2, he⟩ := h
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map φ)
  · have := congrArg (MvPowerSeries.map φ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
      MvPowerSeries.map_subst (hasSubst_substEach hg0)] at this
    rw [this]
    congr 1
    funext i
    exact map_substEach φ g i

end BaseChange

section Twisted

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι : Type*}

noncomputable def twistedDefect (g f : PowerSeries B) (φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  PowerSeries.subst (dropConst φ) g - subst (substEach f) (map σ (dropConst φ))

def twistOp (u π : B) (d : ℕ) (b : B) : B :=
  u * b - π ^ (d - 1) * σ b

noncomputable def twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) :
    MvPowerSeries ι B :=
  fun e => if e.degree ≤ 1 then coeff e ℓ else
    Function.invFun (twistOp σ u π e.degree)
      (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)))

theorem coeff_twistStep (u π : B) (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    coeff e (twistStep σ u π g f ℓ φ) = if e.degree ≤ 1 then coeff e ℓ else
      Function.invFun (twistOp σ u π e.degree)
        (twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ))) :=
  rfl

def IsTwistedLift (g f : PowerSeries B) (ℓ φ : MvPowerSeries ι B) : Prop :=
  constantCoeff φ = 0 ∧ (2 : ℕ∞) ≤ order (φ - ℓ) ∧
    PowerSeries.subst φ g = subst (substEach f) (map σ φ)

variable [Finite ι] {u π : B} {f g : PowerSeries B}
  (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = π)
  (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = u * π)

include hf0 hf1 hg0 hg1 in

theorem coeff_twistedDefect_sub_twistedDefect {φ ψ : MvPowerSeries ι B} {n : ℕ}
    (h : (n : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (twistedDefect σ g f φ) - coeff e (twistedDefect σ g f ψ) =
      u * π * coeff e (dropConst φ - dropConst ψ) -
        π ^ e.degree * σ (coeff e (dropConst φ - dropConst ψ)) := by
  have hδ : (n : ℕ∞) ≤ order (dropConst φ - dropConst ψ) := by
    refine nat_le_order fun d hd => ?_
    by_cases hd0 : d = 0
    · simp [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
    · rw [map_sub, coeff_dropConst _ hd0, coeff_dropConst _ hd0, ← map_sub]
      exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  have hδσ : (n : ℕ∞) ≤ order (map σ (dropConst φ - dropConst ψ)) := hδ.trans (le_order_map σ)
  have h1 := le_order_subst_substEach_sub_rescale hf0 hf1 hδσ
  have h2 := le_order_subst_sub_subst_sub_C_mul hg0 hg1 (constantCoeff_dropConst φ)
    (constantCoeff_dropConst ψ) hδ
  have h3 := le_order_sub h2 h1
  have hlt : (e.degree : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_of_le he
  have h0 := coeff_of_lt_order (hlt.trans_le h3)
  rw [map_sub (MvPowerSeries.map σ), subst_sub (hasSubst_substEach hf0)] at h0
  simp only [twistedDefect, map_sub, coeff_rescale_const, coeff_C_mul, coeff_map] at h0 ⊢
  linear_combination h0

variable (hreg : ∀ x : B, π * x = 0 → x = 0)
  (hT : ∀ d : ℕ, 2 ≤ d → Function.Bijective (twistOp σ u π d))
  (hdiv : ∀ (φ : MvPowerSeries ι B) (e : ι →₀ ℕ), π ∣ coeff e (twistedDefect σ g f φ))

include hf0 hf1 hg0 hg1 hreg hdiv in
theorem twistStep_contract (ℓ φ ψ : MvPowerSeries ι B) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (φ - ψ)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (twistStep σ u π g f ℓ φ - twistStep σ u π g f ℓ ψ) := by
  refine nat_le_order fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.1 he
  rw [map_sub, coeff_twistStep, coeff_twistStep]
  split_ifs with h1
  · exact sub_self _
  · replace h1 := not_le.1 h1
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at h1
    have hkey := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h he'
    rw [map_sub, coeff_dropConst _ he0, coeff_dropConst _ he0, map_sub] at hkey
    have hd : π * π ^ (e.degree - 1) = π ^ e.degree := by
      rw [← pow_succ']
      congr 1
      omega
    have harg : twistOp σ u π e.degree (coeff e φ) - divBy π (coeff e (twistedDefect σ g f φ)) =
        twistOp σ u π e.degree (coeff e ψ) - divBy π (coeff e (twistedDefect σ g f ψ)) := by
      rw [← sub_eq_zero]
      apply hreg
      have e1 := mul_divBy (hdiv φ e)
      have e2 := mul_divBy (hdiv ψ e)
      simp only [twistOp]
      linear_combination (-1 : B) * hkey - (σ (coeff e φ) - σ (coeff e ψ)) * hd - e1 + e2
    rw [harg, sub_self]

include hf0 hg0 in
theorem twistedDefect_zero : twistedDefect σ g f (0 : MvPowerSeries ι B) = 0 := by
  have h0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [twistedDefect, h0, map_zero, ← coe_substAlgHom (hasSubst_substEach hf0), map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero hg0, sub_zero]

omit [Finite ι] in

theorem eq_coeff_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : ι →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

omit [Finite ι] in
theorem constantCoeff_eq_zero_of_two_le_order_sub {φ ψ : MvPowerSeries ι B}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) (hφ : constantCoeff φ = 0) : constantCoeff ψ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← eq_coeff_of_two_le_order_sub h (by simp),
    coeff_zero_eq_constantCoeff_apply, hφ]

include hf0 hf1 hg0 hg1 hreg hT hdiv in

theorem twistStep_eq_self_iff {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ))
    (φ : MvPowerSeries ι B) :
    twistStep σ u π g f ℓ φ = φ ↔
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  have hdivBy0 : divBy π 0 = 0 := hreg _ (mul_divBy (dvd_zero π))
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  constructor
  · intro hs
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ := by
      intro e he
      have := congrArg (coeff e) hs
      rw [coeff_twistStep, if_pos he] at this
      exact this.symm
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      ext e
      rw [map_zero]
      by_cases he : e.degree ≤ 1
      · have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
          rw [sub_zero, Nat.cast_one]
          exact one_le_order_iff_constCoeff_eq_zero.2 hφ0
        have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he
        rw [twistedDefect_zero σ hf0 hg0, map_zero, sub_zero] at this
        rw [this]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
        · rw [Finsupp.degree_eq_zero_iff] at h
          subst h
          simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_dropConst]
        · have he0 : e ≠ 0 := by
            rintro rfl
            simp at h
          rw [hd0, sub_zero, coeff_dropConst _ he0, h, pow_one, hlin e (by omega), hℓ1 e h,
            sub_self]
      · have := congrArg (coeff e) hs
        rw [coeff_twistStep, if_neg he] at this
        have hT' := hT e.degree (by omega)
        have h2 := congrArg (twistOp σ u π e.degree) this
        rw [Function.invFun_eq (hT'.2 _)] at h2
        have hq : divBy π (coeff e (twistedDefect σ g f φ)) = 0 := by
          linear_combination -h2
        rw [← mul_divBy (hdiv φ e), hq, mul_zero]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ order (φ - ℓ) :=
      nat_le_order fun e he => by rw [map_sub, hlin e (by omega), sub_self]
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, sub_eq_zero] at hdef
    exact hdef
  · rintro ⟨h2, heq⟩
    have hlin : ∀ e : ι →₀ ℕ, e.degree ≤ 1 → coeff e φ = coeff e ℓ :=
      fun e he => eq_coeff_of_two_le_order_sub h2 he
    have hφ0 : constantCoeff φ = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hlin 0 (by simp),
        coeff_zero_eq_constantCoeff_apply, hℓ]
    have hdef : twistedDefect σ g f φ = 0 := by
      rw [twistedDefect, dropConst_of_constantCoeff_eq_zero hφ0, heq, sub_self]
    ext e
    rw [coeff_twistStep]
    split_ifs with he
    · exact (hlin e he).symm
    · rw [hdef, map_zero, hdivBy0, sub_zero]
      exact Function.leftInverse_invFun (hT e.degree (by omega)).1 _

include hf0 hf1 hg0 hg1 hreg hT hdiv in

theorem existsUnique_twisted {ℓ : MvPowerSeries ι B} (hℓ : constantCoeff ℓ = 0)
    (hℓ1 : ∀ e : ι →₀ ℕ, e.degree = 1 → u * π * coeff e ℓ = π * σ (coeff e ℓ)) :
    ∃! φ : MvPowerSeries ι B,
      (2 : ℕ∞) ≤ order (φ - ℓ) ∧ PowerSeries.subst φ g = subst (substEach f) (map σ φ) := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_fixedPoint (twistStep σ u π g f ℓ)
    (twistStep_contract σ hf0 hf1 hg0 hg1 hreg hdiv ℓ)
  exact ⟨φ, (twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 φ).1 hφ,
    fun ψ hψ => huniq ψ ((twistStep_eq_self_iff σ hf0 hf1 hg0 hg1 hreg hT hdiv hℓ hℓ1 ψ).2 hψ)⟩

include hf0 hf1 hg0 hg1 in

theorem IsTwistedLift.linear {ℓ φ : MvPowerSeries ι B} (h : IsTwistedLift σ g f ℓ φ)
    (e : ι →₀ ℕ) (he : e.degree = 1) : u * π * coeff e ℓ = π * σ (coeff e ℓ) := by
  obtain ⟨h0, h2, heq⟩ := h
  have hdef : twistedDefect σ g f φ = 0 := by
    rw [twistedDefect, dropConst_of_constantCoeff_eq_zero h0, heq, sub_self]
  have h1 : ((1 : ℕ) : ℕ∞) ≤ order (φ - 0) := by
    rw [sub_zero, Nat.cast_one]
    exact one_le_order_iff_constCoeff_eq_zero.2 h0
  have := coeff_twistedDefect_sub_twistedDefect σ hf0 hf1 hg0 hg1 h1 he.le
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hd0 : dropConst (0 : MvPowerSeries ι B) = 0 := by simp [dropConst]
  rw [hdef, twistedDefect_zero σ hf0 hg0, map_zero, sub_zero, hd0, sub_zero, coeff_dropConst _ he0,
    he, pow_one, eq_coeff_of_two_le_order_sub h2 he.le] at this
  linear_combination -this

include hf0 hf1 hg0 hg1 hreg hT hdiv in

theorem IsTwistedLift.unique {ℓ φ ψ : MvPowerSeries ι B} (hφ : IsTwistedLift σ g f ℓ φ)
    (hψ : IsTwistedLift σ g f ℓ ψ) : φ = ψ :=
  (existsUnique_twisted σ hf0 hf1 hg0 hg1 hreg hT hdiv
    (constantCoeff_eq_zero_of_two_le_order_sub hφ.2.1 hφ.1)
    (hφ.linear σ hf0 hf1 hg0 hg1)).unique ⟨hφ.2.1, hφ.2.2⟩ ⟨hψ.2.1, hψ.2.2⟩

end Twisted

section Composition

variable {B : Type*} [CommRing B] (σ : B →+* B) {ι τ : Type*} [Finite ι] [Finite τ]
  {f g h : PowerSeries B}

theorem IsTwistedLift.comp_lift (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Φ : MvPowerSeries τ B}
    (hΦ : IsTwistedLift σ g f ℓ Φ) {v u : τ → MvPowerSeries ι B}
    (hu : ∀ j, IsLubinTateLift f h (v j) (u j)) (hσu : ∀ j, map σ (u j) = u j) :
    IsTwistedLift σ g h (subst v ℓ) (subst u Φ) := by
  obtain ⟨hΦ0, hΦ2, hΦe⟩ := hΦ
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => (hu j).1
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΦ2 hΦ0
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hu j).2.1 (hu0 j)
  refine ⟨constantCoeff_subst_eq_zero hus hu0 hΦ0,
    two_le_order_subst_sub_subst_of hΦ2 hℓ0 hu0 hv0 (fun j => (hu j).2.1), ?_⟩
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  have hmu : (fun i => map σ (u i)) = u := funext hσu
  rw [← subst_powerSeries_subst hΦs hus, hΦe, subst_comp_subst_apply (hasSubst_substEach hf0) hus,
    map_subst hus, hmu, subst_comp_subst_apply hus (hasSubst_substEach hh0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hus, subst_X hus]
  exact (hu j).2.2

theorem IsLubinTateLift.comp_twisted (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) {ℓ Ψ : MvPowerSeries τ B}
    (hΨ : IsLubinTateLift g h ℓ Ψ) (hσΨ : MvPowerSeries.map σ Ψ = Ψ) {w v : τ → MvPowerSeries ι B}
    (hv : ∀ j, IsTwistedLift σ h f (w j) (v j)) :
    IsTwistedLift σ g f (subst w ℓ) (subst v Ψ) := by
  obtain ⟨hΨ0, hΨ2, hΨe⟩ := hΨ
  have hv0 : ∀ j, constantCoeff (v j) = 0 := fun j => (hv j).1
  have hvs : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hℓ0 : constantCoeff ℓ = 0 := constantCoeff_eq_zero_of_two_le_order_sub hΨ2 hΨ0
  have hw0 : ∀ j, constantCoeff (w j) = 0 := fun j =>
    constantCoeff_eq_zero_of_two_le_order_sub (hv j).2.1 (hv0 j)
  refine ⟨constantCoeff_subst_eq_zero hvs hv0 hΨ0,
    two_le_order_subst_sub_subst_of hΨ2 hℓ0 hv0 hw0 (fun j => (hv j).2.1), ?_⟩
  have hΨs : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero hΨ0
  have hσvs : HasSubst (fun j => MvPowerSeries.map σ (v j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_map, hv0 j, map_zero]
  rw [← subst_powerSeries_subst hΨs hvs, hΨe, subst_comp_subst_apply (hasSubst_substEach hh0) hvs,
    map_subst hvs, hσΨ, subst_comp_subst_apply hσvs (hasSubst_substEach hf0)]
  congr 1
  funext j
  rw [substEach_apply, subst_powerSeries_subst (PowerSeries.HasSubst.X j) hvs, subst_X hvs]
  exact (hv j).2.2

theorem IsTwistedLift.map (hf0 : PowerSeries.constantCoeff f = 0)
    (hσf : PowerSeries.map σ f = f) (hσg : PowerSeries.map σ g = g) {ℓ φ : MvPowerSeries ι B}
    (hφ : IsTwistedLift σ g f ℓ φ) : IsTwistedLift σ g f (map σ ℓ) (map σ φ) := by
  obtain ⟨h0, h2, he⟩ := hφ
  refine ⟨by rw [constantCoeff_map, h0, map_zero], ?_, ?_⟩
  · rw [← map_sub]
    exact h2.trans (le_order_map σ)
  · have := congrArg (MvPowerSeries.map σ) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), hσg,
      map_subst (hasSubst_substEach hf0)] at this
    rw [this]
    congr 1
    funext i
    rw [map_substEach σ f i, hσf]

end Composition

end GroundTheory.LocalField.FormalGroup
end

section
namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries IsLocalRing

theorem powerSeries_constantCoeff_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.map φ f) = φ (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem pair_eq_substEach {R : Type*} [CommRing R] (k : PowerSeries R) :
    (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) k,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) k] : Fin 2 → MvPowerSeries (Fin 2) R) =
      substEach k := by
  funext i
  fin_cases i <;> rfl

namespace Hom

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {F G : FormalGroup R}

noncomputable def map (h : Hom F G) : Hom (F.map φ) (G.map φ) where
  toPowerSeries := PowerSeries.map φ h.toPowerSeries
  constantCoeff_eq_zero := by
    rw [powerSeries_constantCoeff_map, h.constantCoeff_eq_zero, map_zero]
  map_add := by
    have := congrArg (MvPowerSeries.map φ) h.map_add
    rw [pair_eq_substEach, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      MvPowerSeries.map_subst (hasSubst_substEach h.constantCoeff_eq_zero)] at this
    rw [pair_eq_substEach, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, this]
    congr 1
    funext i
    exact map_substEach φ _ i

theorem map_toPowerSeries (h : Hom F G) :
    (h.map φ).toPowerSeries = PowerSeries.map φ h.toPowerSeries :=
  rfl

end Hom

section Fixed

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →ₐ[A] B)

theorem map_sigma_map_algebraMap {ι : Type*} (Φ : MvPowerSeries ι A) :
    MvPowerSeries.map (σ : B →+* B) (MvPowerSeries.map (algebraMap A B) Φ) =
      MvPowerSeries.map (algebraMap A B) Φ := by
  ext n
  simp [coeff_map]

theorem powerSeries_map_sigma_map_algebraMap (f : PowerSeries A) :
    PowerSeries.map (σ : B →+* B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.map (algebraMap A B) f :=
  map_sigma_map_algebraMap σ f

theorem map_C_mul_X {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    MvPowerSeries.map φ (PowerSeries.C a * PowerSeries.X : PowerSeries R) =
      PowerSeries.C (φ a) * PowerSeries.X := by
  change PowerSeries.map φ (PowerSeries.C a * PowerSeries.X) = _
  simp

theorem coeff_one_C_mul_X {R : Type*} [CommRing R] (a : R) :
    PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X) = a := by
  simp

theorem constantCoeff_C_mul_X {R : Type*} [CommRing R] (a : R) :
    constantCoeff (PowerSeries.C a * PowerSeries.X : MvPowerSeries Unit R) = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.C a * PowerSeries.X) = 0
  simp

theorem C_unit_eq {R : Type*} [CommRing R] (a : R) :
    (MvPowerSeries.C a : MvPowerSeries Unit R) = PowerSeries.C a :=
  rfl

end Fixed

section Hypotheses

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  (σ : B →ₐ[A] B)

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] in

theorem bijective_twistOp [IsAdicComplete (maximalIdeal B) B] {π : A}
    (hπB : Irreducible (algebraMap A B π)) {v : B} (hv : IsUnit v) {d : ℕ} (hd : 2 ≤ d) :
    Function.Bijective (twistOp (σ : B →+* B) v (algebraMap A B π) d) := by
  set ϖ := algebraMap A B π
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  have hadd : ∀ x y, twistOp (σ : B →+* B) v ϖ d x - twistOp (σ : B →+* B) v ϖ d y =
      twistOp (σ : B →+* B) v ϖ d (x - y) := by
    intro x y
    simp only [twistOp, map_sub]
    ring
  have hpow : ϖ ^ (d - 1) = ϖ ^ (d - 2) * ϖ := by
    rw [← pow_succ]
    congr 1
    omega
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    by_contra hz0
    have hz : v * (x - y) = ϖ ^ (d - 1) * σ (x - y) := by
      have := hadd x y
      rw [hxy, sub_self] at this
      simp only [twistOp, hσc] at this
      linear_combination -this
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hπB
    rw [hw, map_mul, map_pow, AlgHom.commutes] at hz
    have h1 : v * w = ϖ ^ (d - 1) * σ w :=
      mul_right_cancel₀ (pow_ne_zero n hπB.ne_zero) (by linear_combination hz)
    have hunit : IsUnit (ϖ ^ (d - 1) * σ w) := h1 ▸ hv.mul w.isUnit
    have hdvd : ϖ ∣ ϖ ^ (d - 1) * σ w := by
      rw [hpow, mul_assoc]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    exact hπB.not_isUnit (isUnit_of_dvd_unit hdvd hunit)
  · intro c
    obtain ⟨x, hx, -⟩ := exists_eq_zero_of_approx (maximalIdeal B)
      (fun x => twistOp (σ : B →+* B) v ϖ d x - c)
      (fun n x y hxy => by
        rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
        obtain ⟨t, ht⟩ := hxy
        refine ⟨v * t - ϖ ^ (d - 1) * σ t, ?_⟩
        have : x = y + ϖ ^ n * t := by rw [← ht]; ring
        simp only [twistOp, hσc, this, map_add, hσϖ]
        ring)
      (fun n x hx => by
        rw [mem_maximalIdeal_pow_iff hπB] at hx
        obtain ⟨w, hw⟩ := hx
        obtain ⟨v', hv'⟩ := hv.exists_right_inv
        refine ⟨x - ϖ ^ n * (v' * w), ?_, ?_⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          exact ⟨-(v' * w), by ring⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          refine ⟨ϖ ^ (d - 2) * σ (v' * w), ?_⟩
          simp only [twistOp, hσc, map_sub, hσϖ] at hw ⊢
          linear_combination hw - ϖ ^ n * w * hv' + ϖ ^ n * σ (v' * w) * hpow)
      (m := 0) (x₀ := 0) (by simp)
    exact ⟨x, sub_eq_zero.1 hx⟩

omit [Finite (ResidueField A)] in

theorem map_residue_map_eq_X_pow {π : A} (hmem : algebraMap A B π ∈ maximalIdeal B)
    {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries.map (residue B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.X ^ Nat.card (ResidueField A) := by
  ext n
  obtain ⟨c, hc⟩ := hf.dvd_coeff_sub n
  rw [map_sub] at hc
  have h1 : PowerSeries.coeff n f =
      PowerSeries.coeff n (PowerSeries.X ^ Nat.card (ResidueField A) : PowerSeries A) + π * c := by
    rw [← hc]
    ring
  have h0 : residue B (algebraMap A B π) = 0 := (residue_eq_zero_iff _).2 hmem
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, h1, map_add, map_add, map_mul, map_mul, h0,
    zero_mul, add_zero, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

variable (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ

theorem dvd_coeff_twistedDefect {π : A} (hπB : Irreducible (algebraMap A B π)) {u : A}
    {f g : PowerSeries A} (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)
    {ι : Type*} [Finite ι] (φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    algebraMap A B π ∣ coeff e (twistedDefect (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) φ) := by
  classical
  have := isLocalHom_of_map_maximalIdeal hunr
  let := Fintype.ofFinite (ResidueField A)
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' (ResidueField A)
  have := hcp
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero (ResidueField.map (algebraMap A B)) p hp.ne_zero
  have hq : Nat.card (ResidueField A) = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hq0 : p ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hmemf : algebraMap A B π ∈ maximalIdeal B :=
    (mem_maximalIdeal _).2 hπB.not_isUnit
  have hmemg : algebraMap A B (u * π) ∈ maximalIdeal B := by
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hmemf
  have hf0 : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hcomp : (residue B).comp (σ : B →+* B) =
      (iterateFrobenius (ResidueField B) p n).comp (residue B) := by
    ext x
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← hq]
    exact hσ x
  rw [← residue_eq_zero_iff_dvd hπB, ← coeff_map]
  set ψ := MvPowerSeries.map (residue B) (dropConst φ)
  have hs : PowerSeries.HasSubst (dropConst φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)
  have hs' : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero (by
    rw [constantCoeff_map, constantCoeff_dropConst, map_zero])
  have hE := hasSubst_substEach (σ := ι) hf0
  have hmapE : (fun i => MvPowerSeries.map (residue B)
      (substEach (PowerSeries.map (algebraMap A B) f) i : MvPowerSeries ι B)) =
      fun i => X i ^ (p ^ (n : ℕ)) := by
    funext i
    rw [map_substEach, substEach_apply, map_residue_map_eq_X_pow hmemf hf,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
      PowerSeries.subst_X (PowerSeries.HasSubst.X i), hq]
  have hfrob : MvPowerSeries.map (residue B) (MvPowerSeries.map (σ : B →+* B) (dropConst φ)) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ := by
    ext d
    simp only [coeff_map, ψ]
    exact RingHom.congr_fun hcomp _
  have h3 : subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ)))
      (MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n)
        (subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ))) ψ) := by
    rw [map_subst (HasSubst.X_pow hq0)]
    simp only [map_pow, map_X]
  have h4 := map_iterateFrobenius_expand p hp.ne_zero ψ n
  simp only [expand, coe_substAlgHom] at h4
  rw [twistedDefect, map_sub, map_subst hE, PowerSeries.map_subst hs,
    map_residue_map_eq_X_pow hmemg hg, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE,
    hfrob, h3, h4, hq, sub_self, map_zero]

end Hypotheses

section Main

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
  {π : A} (hπ : Irreducible π) (u : Aˣ) {f g : PowerSeries A}
  (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)

include hunr hσ hπ hf hg

omit [IsAlgClosed (ResidueField B)] in

theorem isTwistedLift_unique {ι : Type*} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B}
    (hφ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ φ)
    (hψ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ ψ) : φ = ψ := by
  have hπB := irreducible_algebraMap hunr hπ
  refine hφ.unique (σ : B →+* B) (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hψ

omit [IsAlgClosed (ResidueField B)] in

theorem exists_isTwistedLift {ε : B} (hε : σ ε = algebraMap A B u * ε) :
    ∃ θ : PowerSeries B, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (PowerSeries.C ε * PowerSeries.X) θ := by
  have hπB := irreducible_algebraMap hunr hπ
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hℓ0 : constantCoeff (PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) = 0 := by
    change PowerSeries.constantCoeff (PowerSeries.C ε * PowerSeries.X) = 0
    simp
  obtain ⟨θ, ⟨h2, he⟩, -⟩ := existsUnique_twisted (σ : B →+* B) (ι := Unit)
    (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hℓ0 (fun e he => by
      have hd' : e = Finsupp.single () (e ()) := by ext; simp
      rw [hd', Finsupp.degree_single] at he
      rw [hd', he]
      change algebraMap A B u * algebraMap A B π * PowerSeries.coeff 1
          (PowerSeries.C ε * PowerSeries.X) =
        algebraMap A B π * σ (PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X))
      rw [coeff_one_C_mul_X, hε]
      ring)
  have h2' : (2 : ℕ∞) ≤ order ((PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) - θ) := by
    rw [← neg_sub, order_neg]
    exact h2
  exact ⟨θ, constantCoeff_eq_zero_of_two_le_order_sub h2' hℓ0, h2, he⟩

theorem exists_iso_lubinTateFormalGroup :
    ∃ θ : Iso ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
        ((lubinTateFormalGroup ((irreducible_units_mul u).2 hπ) hg).map (algebraMap A B)),
      IsUnit (PowerSeries.coeff 1 θ.hom.toPowerSeries) ∧
      σ (PowerSeries.coeff 1 θ.hom.toPowerSeries) =
        algebraMap A B u * PowerSeries.coeff 1 θ.hom.toPowerSeries ∧
      PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
          θ.hom.toPowerSeries ∧
      (∀ a : A, θ.hom.comp ((lubinTateHom hπ hf hf a).map (algebraMap A B)) =
        ((lubinTateHom ((irreducible_units_mul u).2 hπ) hg hg a).map (algebraMap A B)).comp
          θ.hom) ∧
      PowerSeries.subst θ.hom.toPowerSeries (PowerSeries.map (algebraMap A B) g) =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) f)
          (PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries) := by
  have hπ' : Irreducible (u * π) := (irreducible_units_mul u).2 hπ
  have hπB := irreducible_algebraMap hunr hπ
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hf0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hg0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) g) = 0 := by
    rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero]

  obtain ⟨η, hη⟩ := exists_units_eq_mul σ hσ hπB (Units.map (algebraMap A B : A →* B) u)
  set ε : B := (η : B)
  have hε : σ ε = algebraMap A B u * ε := by simpa using hη

  obtain ⟨θ, hθ⟩ := exists_isTwistedLift hunr σ hσ hπ u hf hg hε
  have hθ0 : PowerSeries.constantCoeff θ = 0 := hθ.1
  have hθ1 : PowerSeries.coeff 1 θ = ε := by
    have := eq_coeff_of_two_le_order_sub hθ.2.1 (e := Finsupp.single () 1) (by simp)
    change PowerSeries.coeff 1 θ = PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X) at this
    rw [this, coeff_one_C_mul_X]

  have hL : MvPowerSeries.map (algebraMap A B) (sum₂ (![1, 1] : Fin 2 → A)) =
      X 0 + X 1 := by
    rw [linearForm_fin_two]
    simp
  have hFf : IsLubinTateLift (PowerSeries.map (algebraMap A B) f)
      (PowerSeries.map (algebraMap A B) f) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ hf hf _).map (algebraMap A B) hf.constantCoeff_eq_zero
  have hFg : IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) g) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ' hg).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ' hg hg _).map (algebraMap A B) hg.constantCoeff_eq_zero
  have hHom : ∀ {h h' : PowerSeries A} (hh : IsLubinTateSeries π h) (hh' : IsLubinTateSeries π h')
      (hπ₀ : Irreducible π) (a : A), IsLubinTateLift (PowerSeries.map (algebraMap A B) h)
        (PowerSeries.map (algebraMap A B) h') (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ₀ hh hh' a).toPowerSeries) := by
    intro h h' hh hh' hπ₀ a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ₀ hh hh' a).map (algebraMap A B) hh'.constantCoeff_eq_zero
  have hHom' : ∀ a : A, IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
        (PowerSeries.map (algebraMap A B) g) (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ' hg hg a).toPowerSeries) := by
    intro a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ' hg hg a).map (algebraMap A B) hg.constantCoeff_eq_zero
  have uniq := fun {ι : Type} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B} hφ hψ =>
    isTwistedLift_unique hunr σ hσ hπ u hf hg (ℓ := ℓ) (φ := φ) (ψ := ψ) hφ hψ

  have hX : ∀ j : Fin 2, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (C ε * X j)
      (PowerSeries.subst (X j : MvPowerSeries (Fin 2) B) θ) := by
    intro j
    have := hθ.comp_lift (σ : B →+* B) hf0B hf0B (v := fun _ : Unit => (X j : MvPowerSeries (Fin 2) B))
      (u := fun _ => X j) (fun _ => isLubinTateLift_X hf0B j) (fun _ => map_X _ _)
    rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.X j)] at this
  have hD := hθ.comp_lift (σ : B →+* B) hf0B hf0B
    (v := fun _ : Unit => (X 0 + X 1 : MvPowerSeries (Fin 2) B))
    (u := fun _ => MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries)
    (fun _ => hFf) (fun _ => map_sigma_map_algebraMap σ _)
  rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
    powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))] at hD
  have hE := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B hFg
    (map_sigma_map_algebraMap σ _)
    (w := ![C ε * X 0, C ε * X 1])
    (v := ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) B) θ,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) B) θ])
    (fun j => by fin_cases j <;> simpa using hX _)
  have hs2 : HasSubst (![C ε * X 0, C ε * X 1] : Fin 2 → MvPowerSeries (Fin 2) B) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_add hs2, subst_X hs2, subst_X hs2] at hE
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hE
  rw [← mul_add] at hE
  have hDE := uniq hD hE
  let θh : Hom ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
      ((lubinTateFormalGroup hπ' hg).map (algebraMap A B)) :=
    { toPowerSeries := θ
      constantCoeff_eq_zero := hθ0
      map_add := by
        rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, hDE] }
  let θi := Iso.ofIsUnit θh (by
    change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit)
  refine ⟨θi, ?_, ?_, ?_, ?_, ?_⟩
  · change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit
  · change σ (PowerSeries.coeff 1 θ) = _ * PowerSeries.coeff 1 θ
    rw [hθ1, hε]
  ·
    change PowerSeries.map (σ : B →+* B) θ = PowerSeries.subst _ θ
    have h1 := hθ.map (σ : B →+* B) hf0B (powerSeries_map_sigma_map_algebraMap σ f)
      (powerSeries_map_sigma_map_algebraMap σ g)
    have h2 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B u) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
      (fun _ => hHom hf hf hπ u) (fun _ => map_sigma_map_algebraMap σ _)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [map_C_mul_X, hσc, hε] at h1
    rw [C_unit_eq, ← mul_assoc, ← map_mul, mul_comm ε] at h2
    exact uniq h1 h2
  ·
    intro a
    apply Hom.ext
    rw [Hom.toPowerSeries_comp, Hom.toPowerSeries_comp, Hom.map_toPowerSeries,
      Hom.map_toPowerSeries]
    change PowerSeries.subst _ θ = PowerSeries.subst θ _
    have h1 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B a) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf a).toPowerSeries)
      (fun _ => hHom hf hf hπ a) (fun _ => map_sigma_map_algebraMap σ _)
    have h2 := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B (hHom' a)
      (map_sigma_map_algebraMap σ _)
      (w := fun _ : Unit => PowerSeries.C ε * PowerSeries.X) (v := fun _ => θ) (fun _ => hθ)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h1
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [C_unit_eq] at h1 h2
    have e : PowerSeries.C ε * (PowerSeries.C (algebraMap A B a) * PowerSeries.X) =
        PowerSeries.C (algebraMap A B a) * (PowerSeries.C ε * PowerSeries.X) := by ring
    rw [e] at h1
    exact uniq h1 h2
  ·
    change PowerSeries.subst θ _ = PowerSeries.subst _ (PowerSeries.map (σ : B →+* B) θ)
    rw [hθ.2.2, subst_substEach_unit]
    rfl

end Main

end GroundTheory.LocalField.FormalGroup
end
