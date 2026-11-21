import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesFin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian

section
section
open Matrix Filter Topology

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem val_lt_exp_of_dvdPow_succ {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {N : ℕ} (hx : DvdPow ϖ (N + 1) x) : Valued.v x < WithZero.exp (-(N : ℤ)) := by
  obtain ⟨b, hb, hxb⟩ := hx
  rw [hxb, map_mul, map_pow, hϖ]
  calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
        mul_le_mul' le_rfl hb
    _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
    _ < WithZero.exp (-(N : ℤ)) := WithZero.exp_lt_exp.2 (by push_cast; omega)

theorem isClosed_dvdPow_sub {ϖ : L} (h0 : ϖ ≠ 0) (m : ℕ) (c : L) : IsClosed {x : L | DvdPow ϖ m (x - c)} := by
  have hp : ϖ ^ m ≠ 0 := pow_ne_zero _ h0
  have he : {x : L | DvdPow ϖ m (x - c)} =
      (fun x => (ϖ ^ m)⁻¹ * (x - c)) ⁻¹' ((Valued.v (R := L)).integer : Set L) := by
    ext x
    constructor
    · rintro ⟨b, hb, hxb⟩
      show Valued.v ((ϖ ^ m)⁻¹ * (x - c)) ≤ 1
      rw [hxb, inv_mul_cancel_left₀ hp]; exact hb
    · intro hx
      exact ⟨(ϖ ^ m)⁻¹ * (x - c), hx, by rw [mul_inv_cancel_left₀ hp]⟩
  rw [he]
  exact (Valued.isClosed_integer L).preimage (by fun_prop)

theorem exists_limit_dvdPow (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (a : ℕ → L) (ha : ∀ k, DvdPow ϖ (k + 1) (a (k + 1) - a k)) :
    ∃ b : L, ∀ k, DvdPow ϖ (k + 1) (b - a k) := by
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hint : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ]
    show WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.2 (by omega)
  have hstep : ∀ k m, k ≤ m → DvdPow ϖ (k + 1) (a m - a k) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rw [sub_self]; exact dvdPow_zero ϖ _
    | succ m hkm ih =>
      have := dvdPow_add (dvdPow_mono hint (Nat.succ_le_succ hkm) (ha m)) ih
      rwa [sub_add_sub_cancel] at this
  have hc : CauchySeq a := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by
      simp
    obtain ⟨e, he⟩ : ∃ e, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e :=
      ⟨_, (WithZero.exp_log hγ).symm⟩
    refine ⟨(-e).toNat, fun m hm n hn => ?_⟩
    show Valued.v.restrict (a n - a m) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    have h1 := dvdPow_sub (hstep _ n hn) (hstep _ m hm)
    rw [sub_sub_sub_cancel_right] at h1
    refine (val_lt_exp_of_dvdPow_succ hϖ h1).trans_le (WithZero.exp_le_exp.2 ?_)
    have := Int.self_le_toNat (-e)
    omega
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨b, fun k => ?_⟩
  exact (isClosed_dvdPow_sub h0 (k + 1) (a k)).mem_of_tendsto hb
    (eventually_atTop.2 ⟨k, fun m hm => hstep k m hm⟩)

end GlobalTheory.Hk3.IntWittBase
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_newton_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  atlas_forward_decl GlobalTheory.Hk3.UnitaryNewton.newton_step
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev OV (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

abbrev Res (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : Type :=
  IsLocalRing.ResidueField (OV L)

theorem isUnit_iff (x : OV L) : IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : OV L) : L) ≤ 1 := (u : OV L).2
    have h2 : Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) ≤ 1 := ((u⁻¹ : (OV L)ˣ) : OV L).2
    have h3 : ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [show ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = (((u : OV L) * ((u⁻¹ : (OV L)ˣ) : OV L) : OV L) : L) from rfl, Units.mul_inv]; rfl
    have h4 : Valued.v ((u : OV L) : L) * Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [← map_mul, h3, map_one]
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
      _ ≤ Valued.v ((u : OV L) : L) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _
  · intro h
    have hx : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hm : (x : L)⁻¹ ∈ OV L := by
      show Valued.v (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one (b := (⟨_, hm⟩ : OV L)) (Subtype.ext (mul_inv_cancel₀ hx))

theorem lt_one_iff_le {a : WithZero (Multiplicative ℤ)} :
    a < 1 ↔ a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, a = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
    show WithZero.exp m < WithZero.exp 0 ↔ WithZero.exp m ≤ WithZero.exp (-1)
    rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem residue_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : OV L) : IsLocalRing.residue (OV L) x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hx1 : Valued.v (x : L) ≤ 1 := x.2
  constructor
  · intro h
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx1 h
    rw [lt_one_iff_le, ← hϖ] at hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hlt zero_le'
  · rintro ⟨b, hb, hxb⟩ h
    have hb' : Valued.v b ≤ 1 := hb
    have : Valued.v (x : L) ≤ Valued.v ϖ := by
      rw [hxb, map_mul, pow_one]
      calc Valued.v ϖ * Valued.v b ≤ Valued.v ϖ * 1 := mul_le_mul' le_rfl hb'
        _ = _ := mul_one _
    rw [h, hϖ] at this
    exact absurd (lt_one_iff_le.2 le_rfl) (not_lt.2 this)

def sigO (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : OV L →+* OV L :=
  (σ.comp (OV L).subtype).codRestrict (OV L) fun x => by
    show Valued.v (σ (x : L)) ≤ 1
    rw [hσv]; exact x.2

theorem sigO_coe (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    ((sigO σ hσv x : OV L) : L) = σ x := rfl

theorem sigO_le (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsLocalRing.maximalIdeal (OV L) ≤ Ideal.comap (sigO σ hσv) (IsLocalRing.maximalIdeal (OV L)) := by
  intro x hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff, sigO_coe, hσv,
    ← isUnit_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  exact hx

def sigK (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : Res L →+* Res L :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (OV L)) (sigO σ hσv) (sigO_le σ hσv)

theorem sigK_residue (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    sigK σ hσv (IsLocalRing.residue (OV L) x) = IsLocalRing.residue (OV L) (sigO σ hσv x) := rfl

end GlobalTheory.Hk3.ResWitt

end

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

open Classical in

noncomputable def redL (x : L) : Res L := if h : x ∈ OV L then IsLocalRing.residue (OV L) ⟨x, h⟩ else 0

theorem redL_coe (x : OV L) : redL (x : L) = IsLocalRing.residue (OV L) x := by
  unfold redL; rw [dif_pos x.2]

theorem redL_of_mem {x : L} (hx : x ∈ intL L) : redL x = IsLocalRing.residue (OV L) ⟨x, hx⟩ :=
  redL_coe ⟨x, hx⟩

theorem redL_add {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x + y) = redL x + redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).add_mem hx hy), ← map_add]; rfl

theorem redL_mul {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x * y) = redL x * redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).mul_mem hx hy), ← map_mul]; rfl

theorem redL_sub {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x - y) = redL x - redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).sub_mem hx hy), ← map_sub]; rfl

theorem redL_sum {ι : Type} (s : Finset ι) (f : ι → L) (hf : ∀ i, f i ∈ intL L) :
    redL (∑ i ∈ s, f i) = ∑ i ∈ s, redL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, redL_of_mem (intL L).zero_mem]; exact map_zero _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, redL_add (hf j) (Subring.sum_mem _ fun i _ => hf i), ih]

theorem redL_sigma (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    redL (σ x) = sigK σ hσv (redL x) := by
  have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  rw [redL_of_mem hx, redL_of_mem hσx, sigK_residue]; rfl

theorem redL_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ∈ intL L) : redL x = 0 ↔ DvdPow ϖ 1 x := by
  rw [redL_of_mem hx]; exact residue_eq_zero_iff hϖ ⟨x, hx⟩

theorem redL_surj (a : Res L) : ∃ x ∈ intL L, redL x = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  exact ⟨y, y.2, redL_coe y⟩

theorem redL_ne_zero_of_v {x : L} (hx : Valued.v x = 1) : redL x ≠ 0 := by
  have hxi : x ∈ intL L := by show Valued.v x ≤ 1; rw [hx]
  rw [redL_of_mem hxi, Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not, isUnit_iff]
  exact hx

theorem sigK_invol (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσσ : ∀ x, σ (σ x) = x) (a : Res L) :
    sigK σ hσv (sigK σ hσv a) = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  rw [sigK_residue, sigK_residue]; congr 1; exact Subtype.ext (hσσ _)

theorem isQA_sigK {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) :
    GlobalTheory.SgAlg.IsQA (sigK σ h.2.1) := by
  obtain ⟨hσσ, hσv, -, -, ⟨x, hx, hxv⟩, -⟩ := id h
  refine ⟨sigK_invol σ _ hσσ, ⟨redL x, ?_⟩, inferInstance, ?_, fun y _ hy => hy.isUnit⟩
  · intro he
    have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
    apply redL_ne_zero_of_v hxv
    rw [redL_sub hσx hx, redL_sigma σ hσv hx, he, sub_self]
  · have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two h hq
    have hne := redL_ne_zero_of_v h2
    have h2i : (2 : L) ∈ intL L := by show Valued.v (2 : L) ≤ 1; rw [h2]
    have : redL (2 : L) = 2 := by
      rw [show (2 : L) = 1 + 1 by norm_num, redL_add (intL L).one_mem (intL L).one_mem,
        redL_of_mem (intL L).one_mem]
      rw [show (⟨1, (intL L).one_mem⟩ : OV L) = 1 from rfl, map_one]; norm_num
    rw [this] at hne
    exact hne.isUnit

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def redM {a b : Type} (A : Matrix a b L) : Matrix a b (Res L) := A.map redL

def IntM {a b : Type} (A : Matrix a b L) : Prop := ∀ i j, A i j ∈ intL L

theorem intM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => (intL L).mul_mem (hA i l) (hB l j)

theorem intM_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : IntM (Formalism.UG.cT σ A) := by
  intro i j; show Valued.v (σ (A j i)) ≤ 1; rw [hσv]; exact hA j i

theorem redM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    redM (A * B) = redM A * redM B := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.mul_apply]
  rw [redL_sum _ _ fun l => (intL L).mul_mem (hA i l) (hB l j)]
  exact Finset.sum_congr rfl fun l _ => redL_mul (hA i l) (hB l j)

theorem redM_sub {a b : Type} {A B : Matrix a b L} (hA : IntM A) (hB : IntM B) :
    redM (A - B) = redM A - redM B := by
  ext i j; simp only [redM, Matrix.map_apply, Matrix.sub_apply]; exact redL_sub (hA i j) (hB i j)

theorem redM_cT (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : redM (Formalism.UG.cT σ A) = GlobalTheory.SgAlg.cT (sigK σ hσv) (redM A) := by
  ext i j
  show redL (σ (A j i)) = sigK σ hσv (redL (A j i))
  exact redL_sigma σ hσv (hA j i)

theorem redM_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {a b : Type} {A : Matrix a b L} (hA : IntM A) : redM A = 0 ↔ ∀ i j, DvdPow ϖ 1 (A i j) := by
  constructor
  · intro h i j; rw [← redL_eq_zero_iff hϖ (hA i j)]; exact congrFun (congrFun h i) j
  · intro h; ext i j; exact (redL_eq_zero_iff hϖ (hA i j)).2 (h i j)

theorem redM_one {a : Type} [DecidableEq a] : redM (1 : Matrix a a L) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · rw [redL_of_mem (intL L).one_mem]; exact map_one _
  · rw [redL_of_mem (intL L).zero_mem]; exact map_zero _

theorem free_redM {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {z : ι → Fin n → L} (hz : ∀ i r, z i r ∈ intL L)
    (hI : IndepMod ϖ z) : GlobalTheory.SgAlg.Free (redM (Matrix.of fun r i => z i r)) := by
  set X : Matrix (Fin n) ι (Res L) := redM (Matrix.of fun r i => z i r)
  have hinj : LinearMap.ker (Matrix.toLin' X) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro e he
    choose d hd hde using fun i => redL_surj (e i)
    have hs : ∀ r, DvdPow ϖ 1 (∑ i, d i * z i r) := by
      intro r
      rw [← redL_eq_zero_iff hϖ (Subring.sum_mem _ fun i _ => (intL L).mul_mem (hd i) (hz i r)),
        redL_sum _ _ fun i => (intL L).mul_mem (hd i) (hz i r)]
      have := congrFun he r
      rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at this
      rw [Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [redL_mul (hd i) (hz i r), hde, mul_comm]; rfl
    have h0 := hI d hd hs
    funext i
    rw [← hde i]
    exact (redL_eq_zero_iff hϖ (hd i)).2 (h0 i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem hform_eq_entry (σ : L →+* L) {n : ℕ} {ι : Type} (J : Matrix (Fin n) (Fin n) L) (z : ι → Fin n → L) (a b : ι) :
    Formalism.UG.hform σ J (z a) (z b) = (Formalism.UG.cT σ (Matrix.of fun r i => z i r) * J * Matrix.of fun r i => z i r) a b := by
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

theorem exists_int_unitary_mod_of_gram_mod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hJh ι _ z z' hz hz' hI hI' hG
  classical
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ := hU.2.2.2.1
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  obtain ⟨g0, hg0⟩ := hJT
  have hJi : IntM J := by
    intro i j; rw [hJdef, ← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (intL L)) i j).2
  have hJinv : IntM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    intro i j; rw [← hg0, ← map_inv]; exact (((g0⁻¹ : GL (Fin n') (intL L)) : Matrix (Fin n') (Fin n') (intL L)) i j).2
  set X : Matrix (Fin n') ι L := Matrix.of fun r i => z i r with hXdef
  set X' : Matrix (Fin n') ι L := Matrix.of fun r i => z' i r with hX'def
  have hXi : IntM X := fun r i => hz i r
  have hX'i : IntM X' := fun r i => hz' i r

  have hHerm : GlobalTheory.SgAlg.IsHermU (sigK σ hσv) (redM J) := by
    refine ⟨?_, ?_⟩
    · rw [← redM_cT σ hσv hJi]; congr 1; ext i j; exact hJh j i
    · refine Matrix.isUnit_det_of_right_inverse (B := redM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) ?_
      rw [← redM_mul hJi hJinv, hJdef, ← Units.val_mul, mul_inv_cancel, Units.val_one, redM_one]
  have hgram : ∀ (Y : Matrix (Fin n') ι L), IntM Y →
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM Y) (redM Y) = redM (Formalism.UG.cT σ Y * J * Y) := by
    intro Y hY
    rw [redM_mul (intM_mul (intM_cT hσv hY) hJi) hY, redM_mul (intM_cT hσv hY) hJi, redM_cT σ hσv hY]
    rfl
  have hP : GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X) (redM X) =
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X') (redM X') := by
    rw [hgram X hXi, hgram X' hX'i]
    have hint : ∀ Y : Matrix (Fin n') ι L, IntM Y → IntM (Formalism.UG.cT σ Y * J * Y) :=
      fun Y hY => intM_mul (intM_mul (intM_cT hσv hY) hJi) hY
    have h0 : redM (Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) = 0 := by
      rw [redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) (fun i j => (intL L).sub_mem (hint X' hX'i i j) (hint X hXi i j))]
      intro a b
      have := hG a b
      rwa [hform_eq_entry, hform_eq_entry] at this
    rw [redM_sub (hint X' hX'i) (hint X hXi), sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨gb, hgU, hgX⟩ := GlobalTheory.witt_free_tuples (sigK σ hσv) (isQA_sigK hU hq) (redM J) hHerm (redM X) (redM X')
    (free_redM hϖ hz hI) (free_redM hϖ hz' hI') hP
  choose g hgi hge using fun i j => redL_surj (gb i j)
  have hgI : IntM (Matrix.of g) := fun i j => hgi i j
  have hred : redM (Matrix.of g) = gb := by ext i j; exact hge i j
  refine ⟨Matrix.of g, hgi, ?_, ?_⟩
  · have hint1 : IntM (Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g) := intM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI
    refine (redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g - J) (fun i j => (intL L).sub_mem (hint1 i j) (hJi i j))).1 ?_
    rw [redM_sub hint1 hJi, redM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI, redM_mul (intM_cT hσv hgI) hJi,
      redM_cT σ hσv hgI, hred]
    exact sub_eq_zero.2 hgU
  · intro i r
    have hint2 : IntM (Matrix.of g * X) := intM_mul hgI hXi
    have h0 : redM (Matrix.of g * X - X') = 0 := by
      rw [redM_sub hint2 hX'i, redM_mul hgI hXi, hred, hgX, sub_self]
    have := (redM_eq_zero_iff hϖ (A := Matrix.of g * X - X') (fun i j => (intL L).sub_mem (hint2 i j) (hX'i i j))).1 h0 r i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hXdef, hX'def] using this

end GlobalTheory.Hk3.ResWitt
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_integral_vectors_pairing : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  atlas_forward_decl GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod
end

section
section
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_unitary_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWittBase.witt_mod_base
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isUnit_valuationSubring_iff (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := congrArg (fun y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring =>
      Valued.v (y : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1
    have hu : Valued.v ((u : _) : L) ≤ 1 := ((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)).2
    have hw : Valued.v ((u⁻¹ : _) : L) ≤ 1 := ((u⁻¹ : _) : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).2
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v ((u : _) : L) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    let y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring :=
      ⟨(x : L)⁻¹, by
        show Valued.v (x : L)⁻¹ ≤ 1
        rw [map_inv₀, h, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem residue_eq_zero_iff_dvdPow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsLocalRing.residue _ x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_valuationSubring_iff]
  have hx : Valued.v (x : L) ≤ 1 := x.2
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  constructor
  · intro hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    have hle := le_exp_neg_one_of_lt_one' hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀, hϖ]
    have hpos : (0 : WithZero (Multiplicative ℤ)) < ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
      WithZero.zero_lt_coe _
    exact (div_le_one₀ hpos).2 hle
  · rintro ⟨b, hb, hxb⟩ h1
    have hb' : Valued.v b ≤ 1 := hb
    rw [hxb, pow_one, map_mul, hϖ] at h1
    have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * Valued.v b ≤
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * 1 := by gcongr
    rw [h1, mul_one] at this
    exact absurd this (by decide)

theorem exists_dual_of_indepMod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  intro L _ _ ϖ hϖ m ι _ _ z hz hind
  classical
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  let Z : Matrix ι (Fin m) O := fun i r => ⟨z i r, hz i r⟩
  let Zb : Matrix ι (Fin m) k := Z.map res

  have hinj : LinearMap.ker (Matrix.mulVecLin Zbᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let d : ι → O := fun i => (hres (w i)).choose
    have hd : ∀ i, res (d i) = w i := fun i => (hres (w i)).choose_spec
    have hsum : ∀ r, DvdPow ϖ 1 (∑ i, ((d i : O) : L) * z i r) := by
      intro r
      have h1 : res (∑ i, d i * Z i r) = 0 := by
        have := congrFun hw r
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
        rw [map_sum]
        simpa [Zb, hd, mul_comm] using this
      have h2 := (residue_eq_zero_iff_dvdPow hϖ _).1 h1
      simpa [Z] using h2
    have hdi := hind (fun i => (d i : L)) (fun i => (d i).2) hsum
    funext i
    rw [← hd i]
    exact (residue_eq_zero_iff_dvdPow hϖ _).2 (hdi i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let B : Matrix ι (Fin m) k := LinearMap.toMatrix' g
  have hB : B * Zbᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  let Bo : Matrix ι (Fin m) O := fun i r => (hres (B i r)).choose
  have hBo : Bo.map res = B := by
    ext i r; exact (hres (B i r)).choose_spec
  let M : Matrix ι ι O := Bo * Zᵀ
  have hM : M.map res = 1 := by
    simp only [M, Matrix.map_mul, Matrix.transpose_map, hBo]
    exact hB
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : res M.det = 1 := by
      rw [RingHom.map_det]
      change (M.map res).det = 1
      rw [hM, Matrix.det_one]
    rw [show IsLocalRing.residue O M.det = res M.det from rfl, this]
    exact one_ne_zero
  let A : Matrix ι (Fin m) O := M⁻¹ * Bo
  have hA : A * Zᵀ = 1 := by
    simp only [A, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul M hdet
  refine ⟨fun i r => (A i r : L), fun i r => (A i r).2, fun i j => ?_⟩
  have h := congrArg (fun x : O => (x : L)) (congrFun (congrFun hA i) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have h2 : ((∑ r, A i r * Z j r : O) : L) = ∑ r, (A i r : L) * z j r := by
    simp [Z, O]
  rw [h2] at h
  rw [h]
  split_ifs <;> simp

end GlobalTheory.Hk3.IntWitt
end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_of_independentModUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  atlas_forward_decl GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _
      simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y
      simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  atlas_forward_decl GlobalTheory.Hk3.SkewLift.skew_lift
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.CayleyCong

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

theorem cayley_cong : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hermT C hskew hCI k hk
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσv := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hvϖ : Valued.v ϖ < 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1 by decide)
  have hϖI : ϖ ∈ Formalism.UG.intL L := le_of_lt hvϖ
  have hvϖk : Valued.v (ϖ ^ k) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hvϖ (by omega)
  have hhalf : Valued.v ((2 : L)⁻¹) ≤ 1 := by rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set Jt : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJt
  set Jti : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJti
  have hJtiI : IsIntM Jti := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJJi : Jt * Jti = 1 := by rw [hJt, hJti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcJt : Formalism.UG.cT σ Jt = Jt := cT_herm σ hermT
  have hcC : Formalism.UG.cT σ C = -C := cT_skew σ hskew
  have hcJti : Formalism.UG.cT σ Jti * Jt = 1 := by
    calc Formalism.UG.cT σ Jti * Jt = Formalism.UG.cT σ Jti * Formalism.UG.cT σ Jt := by rw [hcJt]
      _ = Formalism.UG.cT σ (Jt * Jti) := (Formalism.UG.cT_mul σ _ _).symm
      _ = 1 := by rw [hJJi, Formalism.UG.cT_one]
  set M : Matrix (Fin n') (Fin n') L := Jti * C with hMdef
  have hMI : IsIntM M := isIntM_mul hJtiI hCI
  set Y : Matrix (Fin n') (Fin n') L := ϖ ^ k • M with hYdef
  have hσϖk : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hσϖ]
  have hY : Formalism.UG.cT σ Y * Jt = -(ϖ ^ k • C) := by
    rw [hYdef, cT_smul, hσϖk, Matrix.smul_mul, hMdef, Formalism.UG.cT_mul, hcC, Matrix.mul_assoc, hcJti, Matrix.mul_one,
      smul_neg]
  have hJY : Jt * Y = ϖ ^ k • C := by
    rw [hYdef, Matrix.mul_smul, hMdef, ← Matrix.mul_assoc, hJJi, Matrix.one_mul]
  set Z : Matrix (Fin n') (Fin n') L := (2⁻¹ : L) • Y with hZdef
  have hZZ : Z + Z = Y := by
    rw [hZdef, ← add_smul]
    have : (2⁻¹ + 2⁻¹ : L) = 1 := by
      have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      field_simp; norm_num
    rw [this, one_smul]
  have hZ : Formalism.UG.cT σ Z * Jt = -(Jt * Z) := by
    rw [hZdef, cT_smul, hσhalf, Matrix.smul_mul, hY, Matrix.mul_smul, hJY, smul_neg]
  have hYsmall : IsSmallM Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul]; exact lt_one_mul hvϖk (hMI i j)
  have hZsmall : IsSmallM Z := small_smul hhalf hYsmall
  obtain ⟨hPdet, hPiI⟩ := inv_one_sub hZsmall
  obtain ⟨hQdet, hQiI⟩ := inv_one_add hZsmall
  set Pi := (1 - Z)⁻¹ with hPi
  set Qi := (1 + Z)⁻¹ with hQi
  have hP1 : Pi * (1 - Z) = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hP2 : (1 - Z) * Pi = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hQ1 : Qi * (1 + Z) = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hQ2 : (1 + Z) * Qi = 1 := Matrix.mul_nonsing_inv _ hQdet
  have hPs : Formalism.UG.cT σ Pi * (1 - Formalism.UG.cT σ Z) = 1 := by
    rw [← Formalism.UG.cT_one σ, ← cT_sub, ← Formalism.UG.cT_mul, hP2]
  let g : GL (Fin n') L := ⟨Pi * (1 + Z), Qi * (1 - Z), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Z), hQ2, Matrix.one_mul, hP1], by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Z), hP2, Matrix.one_mul, hQ1]⟩
  have hgU : g ∈ Formalism.UG.UJ σ Jt := by
    show Formalism.UG.cT σ (Pi * (1 + Z)) * Jt * (Pi * (1 + Z)) = Jt
    rw [Formalism.UG.cT_mul, cT_add, Formalism.UG.cT_one]
    exact cayley_unitary_ring hZ hP1 hP2 hQ1 hQ2 hPs
  have hone : IsIntM (1 : Matrix (Fin n') (Fin n') L) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hIZ : IsIntM (1 + Z) := isIntM_add hone (isIntM_of_small hZsmall)
  have hIZ' : IsIntM (1 - Z) := by
    rw [sub_eq_add_neg]; exact isIntM_add hone (isIntM_neg (isIntM_of_small hZsmall))
  have hgI : g ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) :=
    mem_GLint_of_int (isIntM_mul hPiI hIZ) (isIntM_mul hQiI hIZ')
  obtain ⟨hr1, hr2⟩ := cayley_ring hP1 hP2
  have hg1 : Pi * (1 + Z) - 1 = ϖ ^ k • (M * Pi) := by
    rw [hr1, hZZ, hYdef, Matrix.smul_mul]
  have hg2 : Pi * (1 + Z) - 1 - Y = (ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹)) • (M * Pi * M) := by
    have e : ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹) = ϖ ^ k * (2⁻¹ * ϖ ^ k) := by
      have : k + 1 + (k - 1) = k + k := by omega
      rw [← mul_assoc, ← pow_add, this, pow_add]; ring
    rw [e, hr1, hZZ]
    have e2 : Y * Pi - Y = Y * (Pi - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [e2, hr2, hZdef, hYdef]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
    congr 1; ring
  refine ⟨⟨g, hgU⟩, hgI, fun r s => ?_, fun r s => ?_⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s =
        (Pi * (1 + Z) - 1) r s := by rw [Matrix.sub_apply]
    rw [this, hg1, Matrix.smul_apply, smul_eq_mul]
    exact ⟨_, isIntM_mul hMI hPiI r s, rfl⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s =
        (Pi * (1 + Z) - 1 - Y) r s := by rw [Matrix.sub_apply, Matrix.sub_apply]
    rw [this, hg2, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    refine ⟨_, mul_mem (mul_mem (pow_mem hϖI _) hhalf) (isIntM_mul (isIntM_mul hMI hPiI) hMI r s), rfl⟩

end GlobalTheory.Hk3.CayleyCong
end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_transform_integral_unitary_congruent_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  atlas_forward_decl GlobalTheory.Hk3.CayleyCong.cayley_cong
end

section
section
open Matrix

namespace GlobalTheory.Hk3.IntWitt

theorem hensel_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hherm ι _ z z' k hk hz hz' hind hdiff hgram
  classical
  have hv := hU.2.2.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hσv := hU.2.1
  have hϖI : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 from by decide)
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJI : ∀ r s, J r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hJiI : ∀ r s, Ji r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  choose w hwI hwe using hdiff
  have hz'e : ∀ i r, z' i r = z i r + ϖ ^ k * w i r := fun i r => by rw [← hwe]; ring
  have hz'v : ∀ i, z' i = z i + ϖ ^ k • w i := fun i => funext fun r => by simp [hz'e]

  have hformI : ∀ x y : Fin n' → L, (∀ r, x r ∈ Formalism.UG.intL L) → (∀ r, y r ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ J x y ∈ Formalism.UG.intL L := by
    intro x y hx hy
    refine sum_mem fun r _ => sum_mem fun s _ => mul_mem (mul_mem ?_ (hJI r s)) (hy s)
    show Valued.v (σ (x r)) ≤ 1
    rw [hσv]; exact hx r
  have key : ∀ i j, Formalism.UG.hform σ J (z' i) (z' j) - Formalism.UG.hform σ J (z i) (z j) =
      ϖ ^ k * (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) + ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
    intro i j
    simp only [Formalism.UG.hform, hz'e, map_add, map_mul, map_pow, hσϖ, mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hgram1 : ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j)) := by
    intro i j
    have h1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) +
        ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      obtain ⟨b, hb, hbe⟩ := hgram i j
      refine ⟨b, hb, ?_⟩
      have := (key i j).symm.trans hbe
      rw [pow_succ, mul_assoc] at this
      rw [pow_one]
      exact mul_left_cancel₀ (pow_ne_zero k hϖ0) this
    have h2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      refine ⟨ϖ ^ (k - 1) * Formalism.UG.hform σ J (w i) (w j),
        mul_mem (pow_mem hϖI _) (hformI _ _ (hwI i) (hwI j)), ?_⟩
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have := GlobalTheory.Hk3.IntWitt.dvdPow_sub h1 h2
    simpa using this
  obtain ⟨a, haI, ha⟩ := GlobalTheory.T.exists_integral_dual_of_independentModUniformizer L ϖ hv n' ι z hz hind
  obtain ⟨C, hCs, hCI, hCz⟩ := GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer L ϖ σ q hU hq n' JT hJT hherm ι z w a hz hwI haI ha hgram1
  obtain ⟨g, hgI, hg1, hg2⟩ := GlobalTheory.T.cayley_transform_integral_unitary_congruent_one L ϖ σ q hU hq n' JT hJT hherm C hCs hCI k hk
  refine ⟨g, hgI, hg1, fun i r => ?_⟩
  set G : Matrix (Fin n') (Fin n') L := ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hGdef
  have e : G *ᵥ z i - z' i = (G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i + ϖ ^ k • (Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec (w i) Ji J, hJiJ, Matrix.one_mulVec, hz'v, smul_sub]
    abel
  have e' := congrFun e r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
  rw [e']
  have t1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (((G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (∑ s, (G - 1 - ϖ ^ k • (Ji * C)) r s * z i s)
    refine GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => ?_
    rw [mul_comm]
    exact GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hg2 r s) (hz i s)
  have t2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (∑ s, Ji r s * (C *ᵥ z i - J *ᵥ w i) s)
    exact GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hCz i s) (hJiI r s)
  refine GlobalTheory.Hk3.IntWitt.dvdPow_add t1 ?_
  obtain ⟨b, hb, hbe⟩ := t2
  exact ⟨b, hb, by rw [hbe, pow_succ]; ring⟩

end GlobalTheory.Hk3.IntWitt
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_hensel_step_families : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWitt.hensel_step
end

section
section
noncomputable section

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem pi_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem glint_entry {n : ℕ} {h : GL (Fin n) L} (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (r s : Fin n) :
    (h : Matrix (Fin n) (Fin n) L) r s ∈ Formalism.UG.intL L := by
  obtain ⟨g0, hg0⟩ := hh
  rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) r s).2

theorem mulVec_int {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : (M *ᵥ v) r ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun s _ => (Formalism.UG.intL L).mul_mem (hM r s) (hv s)

theorem dvdPow_mulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, DvdPow ϖ k (M r s))
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]; exact dvdPow_mul_int (hM r s) (hv s)

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (h : Formalism.UG.UJ σ J) (x y : Fin n → L) :
    Formalism.UG.hform σ J (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
      (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hu : Formalism.UG.cT σ ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J := h.2
  rw [hform_eq_dot, hform_eq_dot]
  set H := ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have e1 : (fun i => σ ((H *ᵥ x) i)) = (H.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; exact RingHom.map_mulVec σ H x i
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  exact congrArg (· *ᵥ y) hu

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_intMulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, DvdPow ϖ k (v r)) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  exact dvdPow_sum _ _ fun s _ => dvdPow_mul_int (hv s) (hM r s)

theorem indepMod_mulVec {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {h : GL (Fin n) L}
    (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) {z : ι → Fin n → L} (hz : IndepMod ϖ z) :
    IndepMod ϖ (fun i => (h : Matrix (Fin n) (Fin n) L) *ᵥ z i) := by
  intro d hd hs i
  refine hz d hd (fun r => ?_) i
  set w : Fin n → L := ∑ j, d j • z j with hw
  have e1 : ∀ s, ((h : Matrix (Fin n) (Fin n) L) *ᵥ w) s = ∑ j, d j * ((h : Matrix (Fin n) (Fin n) L) *ᵥ z j) s := by
    intro s
    simp [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
  have e2 : ∑ j, d j * z j r = (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ ((h : Matrix (Fin n) (Fin n) L) *ᵥ w)) r := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp [hw, Finset.sum_apply]
  rw [e2]
  exact dvdPow_intMulVec (glint_entry ((Formalism.UG.GLint _ _).inv_mem hh)) (fun s => by rw [e1]; exact hs s) r

theorem indepMod_sub {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {z : ι → Fin n → L} (hz : IndepMod ϖ z)
    (p : ι → Prop) [DecidablePred p] : IndepMod ϖ (fun i : {i // p i} => z i.1) := by
  intro d hd hs i
  let d' : ι → L := fun j => if hj : p j then d ⟨j, hj⟩ else 0
  have h1 : ∀ j, d' j ∈ Formalism.UG.intL L := by
    intro j; by_cases hj : p j
    · simp only [d', dif_pos hj]; exact hd _
    · simp only [d', dif_neg hj]; exact (Formalism.UG.intL L).zero_mem
  have h2 : ∀ r, ∑ j, d' j * z j r = ∑ j : {i // p i}, d j * z j.1 r := by
    intro r
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => d' j * z j r)]
    have a1 : ∑ j : {i // ¬ p i}, d' j.1 * z j.1 r = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [d', dif_neg j.2]
    rw [a1, add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp [d', dif_pos j.2]
  have := hz d' h1 (fun r => by rw [h2]; exact hs r) i.1
  simpa [d', dif_pos i.2] using this

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

theorem witt_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJT hJh ι _ a z z' ha hz hz' hiz hiz' hG
  classical
  have hϖ := pi_int hU
  have key : ∀ k, 1 ≤ k → ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
      (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, DvdPow ϖ (min (a i) k) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h, hh, hc⟩ := GlobalTheory.T.integral_witt_unitary_mod_uniformizer L ϖ σ q hU hq n' JT hJT hJh ι z z' hz hz' hiz hiz'
        (fun i j => dvdPow_mono hϖ (le_min (ha i) (ha j)) (hG i j))
      refine ⟨h, hh, fun i r => ?_⟩
      rw [min_eq_right (ha i)]; exact hc i r
    | succ k hk ih =>
      obtain ⟨h, hh, hc⟩ := ih
      have hHint := glint_entry hh
      obtain ⟨g, hg, hg1, hgc⟩ := GlobalTheory.T.unitaryGroup_hensel_step_families L ϖ σ q hU hq n' JT hJT hJh {i // k < a i}
        (fun i => ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i.1) (fun i => z' i.1) k hk
        (fun i r => mulVec_int hHint (hz i.1) r) (fun i r => hz' i.1 r)
        (indepMod_sub (indepMod_mulVec hh hiz) (fun i => k < a i))
        (fun i r => by
          have h0 := hc i.1 r
          rw [min_eq_right i.2.le] at h0
          have h1 := dvdPow_neg h0
          rwa [neg_sub] at h1)
        (fun i j => by
          simp only [hform_unitary]
          exact dvdPow_mono hϖ (le_min i.2 j.2) (hG i.1 j.1))
      refine ⟨g * h, (Formalism.UG.GLint _ _).mul_mem hg hh, fun i r => ?_⟩
      have e : (((g * h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i
          = ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) := by
        simp [Matrix.mulVec_mulVec]
      rw [e]
      by_cases hki : k < a i
      · rw [min_eq_right (Nat.succ_le_of_lt hki)]
        exact hgc ⟨i, hki⟩ r
      · push_neg at hki
        rw [min_eq_left (by omega)]
        have h2 := hc i r
        rw [min_eq_left hki] at h2
        have h1 : DvdPow ϖ (a i) (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
            (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r) :=
          dvdPow_mono hϖ hki (dvdPow_mulVec (fun r s => by simpa [Matrix.sub_apply] using hg1 r s)
            (mulVec_int hHint (hz i)) r)
        have e2 : (((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r - z' i r
            = (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
              (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r)
              + ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
        rw [e2]; exact dvdPow_add h1 h2
  obtain ⟨h, hh, hc⟩ := key (1 + ∑ i, a i) (by omega)
  refine ⟨h, hh, fun i r => ?_⟩
  have h0 := hc i r
  have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  rwa [min_eq_left (by omega)] at h0

end GlobalTheory.Hk3.IntWittMod

end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralWittTheorem_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWittMod.witt_mod_pow
end
