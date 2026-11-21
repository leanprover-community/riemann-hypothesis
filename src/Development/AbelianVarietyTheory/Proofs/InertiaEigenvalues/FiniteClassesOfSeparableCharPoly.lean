import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.UnitsPowers
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra

section
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  obtain ⟨vr, top, hloc, -⟩ := GlobalTheory.LocFieldOfDVR.exists_isNonarchimedeanLocalField K.O K.E
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  atlas_forward_decl GlobalTheory.UnitLemma.UQ.finite_units_mod_sq
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.ClFin

variable {K : UQ} (B : InvAlg K)

def sigU : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)

theorem sigU_val (u : B.Aˣ) : ((sigU B u : B.Aˣ) : B.A) = B.σ u := rfl

def fixG : Subgroup B.Aˣ where
  carrier := {x | B.σ (x : B.A) = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = 1 := by
      calc B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = B.σ ((a⁻¹ : B.Aˣ) : B.A) * B.σ (a : B.A) := by
            rw [ha]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * ((a⁻¹ : B.Aˣ) : B.A)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, h, one_mul]

def normHom : B.Aˣ →* fixG B where
  toFun u := ⟨u * sigU B u, by
    show B.σ ((u : B.A) * B.σ u) = (u : B.A) * B.σ u
    rw [map_mul, B.σ_σ, mul_comm]⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp [sigU_val]
  map_mul' := by
    intro a b
    apply Subtype.ext; apply Units.ext
    simp only [Units.val_mul, sigU_val, map_mul, Subgroup.coe_mul]
    ring

theorem finite_quot (hsq : Finite (B.Aˣ ⧸ (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range))
    (hmu : Set.Finite {x : B.A | x ^ 2 = 1}) : Finite (fixG B ⧸ (normHom B).range) := by
  set Sq := (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range
  set φ : fixG B →* B.Aˣ ⧸ Sq := (QuotientGroup.mk' Sq).comp (fixG B).subtype
  haveI : Finite (fixG B ⧸ φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  set M := {x : fixG B | ((x : B.Aˣ) : B.A) ^ 2 = 1}
  haveI : Finite M := by
    have : Finite {x : B.A | x ^ 2 = 1} := hmu.to_subtype
    refine Finite.of_injective (fun x : M => (⟨((x.1 : B.Aˣ) : B.A), x.2⟩ : {x : B.A | x ^ 2 = 1})) ?_
    intro a b h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact congrArg Subtype.val h
  let g : (fixG B ⧸ φ.ker) × M → fixG B ⧸ (normHom B).range :=
    fun p => QuotientGroup.mk (Quotient.out p.1 * p.2.1)
  refine Finite.of_surjective g ?_
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set x₀ : fixG B := Quotient.out (QuotientGroup.mk x : fixG B ⧸ φ.ker)
  have hx₀ : x₀⁻¹ * x ∈ φ.ker := by
    have : (QuotientGroup.mk x₀ : fixG B ⧸ φ.ker) = QuotientGroup.mk x := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  rw [MonoidHom.mem_ker] at hx₀
  simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx₀
  obtain ⟨y, hy⟩ := hx₀
  rw [powMonoidHom_apply] at hy

  have hfix : B.σ ((y : B.A) ^ 2) = (y : B.A) ^ 2 := by
    have := (x₀⁻¹ * x).2
    rw [← Units.val_pow_eq_pow_val, hy]
    exact this
  set ε : B.Aˣ := y * (sigU B y)⁻¹
  have hε2 : (ε : B.A) ^ 2 = 1 := by
    have h1 : ((sigU B y : B.Aˣ) : B.A) ^ 2 = (y : B.A) ^ 2 := by rw [sigU_val, ← map_pow, hfix]
    have h1' : (sigU B y) ^ 2 = y ^ 2 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h1])
    have h2 : ((sigU B y)⁻¹ : B.Aˣ) ^ 2 = (y ^ 2)⁻¹ := by rw [inv_pow, h1']
    rw [← Units.val_pow_eq_pow_val]
    simp only [ε, mul_pow, h2, mul_inv_cancel, Units.val_one]
  have hεfix : B.σ (ε : B.A) = ε := by

    have hσ : B.σ (ε : B.A) * (ε : B.A) = 1 := by
      have hyinv : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
        have : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
          calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A)
              = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * B.σ (B.σ (y : B.A)) := by rw [B.σ_σ]
            _ = 1 := by rw [← map_mul, ← sigU_val, Units.inv_mul, map_one]
        calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A)
            = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by
              rw [Units.mul_inv, mul_one]
          _ = ((y⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, this, one_mul]
      simp only [ε, Units.val_mul, map_mul, hyinv]
      calc B.σ (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A))
          = (((sigU B y) : B.Aˣ) : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A) *
              ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by rw [sigU_val]; ring
        _ = 1 := by rw [Units.mul_inv, Units.mul_inv, one_mul]
    calc B.σ (ε : B.A) = B.σ (ε : B.A) * ((ε : B.A) * (ε : B.A)) := by rw [← sq, hε2, mul_one]
      _ = ε := by rw [← mul_assoc, hσ, one_mul]
  let εG : fixG B := ⟨ε, hεfix⟩
  refine ⟨(QuotientGroup.mk x, ⟨εG, hε2⟩), ?_⟩
  show QuotientGroup.mk (x₀ * εG) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  refine ⟨y, ?_⟩
  apply Subtype.ext; apply Units.ext

  have hxy : ((x : fixG B) : B.Aˣ) = (x₀ : B.Aˣ) * y ^ 2 := by
    rw [hy]; simp
  show ((y : B.A) * B.σ (y : B.A)) = (((x₀ * εG)⁻¹ * x : fixG B) : B.Aˣ).val
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxy, εG, ε]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, sigU_val]
  have : ((x₀ : B.Aˣ)⁻¹ : B.Aˣ).val * (x₀ : B.Aˣ).val = 1 := Units.inv_mul _
  have hy1 : (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv y
  rw [sq]
  linear_combination (-(B.σ (y : B.A) * (y : B.A))) * hy1 +
    (-(B.σ (y : B.A) * (y : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A))) * this

def toCl : fixG B ⧸ (normHom B).range → B.Cl :=
  Quotient.lift (fun x : fixG B => (Quot.mk _ ⟨(x : B.Aˣ), x.2⟩ : B.Cl)) (by
    intro a b hab
    have h := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨u, hu⟩ := h
    apply Quot.sound
    refine ⟨u, ?_⟩
    have hb : (b : B.Aˣ) = (a : B.Aˣ) * ((normHom B u : fixG B) : B.Aˣ) := by
      rw [hu]; simp
    show ((b : B.Aˣ) : B.A) = ((a : B.Aˣ) : B.A) * ((u : B.A) * B.σ (u : B.A))
    rw [hb, Units.val_mul]
    rfl)

theorem toCl_surjective : Function.Surjective (toCl B) := by
  intro k
  induction k using Quot.ind with
  | mk x => exact ⟨QuotientGroup.mk ⟨x.1, x.2⟩, rfl⟩

theorem finite_Cl (K : UQ) (B : InvAlg K) : Finite B.Cl := by
  have hsq := GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields K.E (GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic K) B.A
  have hmu := GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero K.E B.A
  haveI := finite_quot B hsq hmu
  exact Finite.of_surjective _ (toCl_surjective B)

theorem finite_Cl_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl :=
  fun K B _ => finite_Cl K B

end GlobalTheory.UnitLemma.ClFin
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_of_separable_charPoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl := by
  atlas_forward_decl GlobalTheory.UnitLemma.ClFin.finite_Cl_of_separable
end
