import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (exact GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (intros; apply GlobalTheory.OrbFinAf.isIntV_mul_eventually' <;> assumption)
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add, MulOpposite.unop_add, hx, hy, map_add, MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i
  rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finset_sum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
end
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_preserves_integrality : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v (starT G.star (Qv v) a).unop := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_star_eventually) | (exact GlobalTheory.OrbFinAf.isIntV_star_eventually) | (intros; apply GlobalTheory.OrbFinAf.isIntV_star_eventually  <;> assumption)
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  first | (exact @GlobalTheory.OrbFinAf.intV_order_eventually) | (exact GlobalTheory.OrbFinAf.intV_order_eventually) | (intros; apply GlobalTheory.OrbFinAf.intV_order_eventually  <;> assumption)
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntV_one_tmul : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  first | (exact @GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (exact GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (intros; apply GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually  <;> assumption)
end

section
open IsDedekindDomain Polynomial

namespace GlobalTheory

theorem hensel_norm_lift_of_involution :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  intro A _ I _ τ hτ h2 hI a t₀ ha hτa ht₀ hclose
  set c := t₀ * τ t₀ with hc_def
  have hc : IsUnit c := ht₀.mul (ht₀.map τ)
  have hτc : τ c = c := by
    simp only [hc_def, map_mul, hτ]; ring
  obtain ⟨w, hw⟩ := hc.exists_right_inv
  have hτw : τ w = w := by
    apply hc.mul_left_cancel
    rw [hw, ← hτc, ← map_mul, hw, map_one]
  set b := a * w with hb_def
  have hτb : τ b = b := by simp only [hb_def, map_mul, hτa, hτw]
  have hb1 : 1 - b ∈ I := by
    have : 1 - b = w * (c - a) := by
      rw [hb_def]; linear_combination (-1 : A) * hw
    rw [this]; exact I.mul_mem_left w hclose
  obtain ⟨s, hs, hs1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - C b)
    (monic_X_pow_sub_C b (by norm_num)) 1 (by simpa using hb1)
    (by
      have : (derivative (X ^ 2 - C b)).eval (1 : A) = 2 := by simp [one_add_one_eq_two]
      rw [this]; exact h2.map _)
  have hs2 : s ^ 2 = b := by
    have := hs.eq_zero; simp at this; linear_combination this
  have hτs2 : τ s ^ 2 = b := by rw [← map_pow, hs2, hτb]
  have hτs1 : τ s - 1 ∈ I := by
    have := hI _ hs1; simpa using this
  have hsum : IsUnit (s + τ s) := by
    have hj : (s - 1) + (τ s - 1) ∈ Ideal.jacobson (⊥ : Ideal A) :=
      HenselianRing.jac (Ideal.add_mem I hs1 hτs1)
    obtain ⟨v, hv⟩ := h2.exists_right_inv
    have hu := (Ideal.mem_jacobson_bot.1 hj) v
    have : s + τ s = (((s - 1) + (τ s - 1)) * v + 1) * 2 := by
      linear_combination (-(s - 1 + (τ s - 1))) * hv
    rw [this]; exact hu.mul h2
  have hfix : τ s = s := by
    have h0 : (s - τ s) * (s + τ s) = 0 := by linear_combination hs2 - hτs2
    have := (hsum.mul_left_eq_zero).1 h0
    linear_combination -this
  have hbu : IsUnit b := ha.mul (IsUnit.of_mul_eq_one_right c hw)
  have hsu : IsUnit s := by
    rw [← hs2, pow_two] at hbu; exact isUnit_of_mul_isUnit_left hbu
  refine ⟨t₀ * s, ht₀.mul hsu, ?_⟩
  rw [map_mul, hfix]
  have : t₀ * s * (τ t₀ * s) = c * s ^ 2 := by rw [hc_def]; ring
  rw [this, hs2, hb_def]
  linear_combination a * hw

end GlobalTheory
end

section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_norm_lift : ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  first | (exact @GlobalTheory.hensel_norm_lift_of_involution) | (exact GlobalTheory.hensel_norm_lift_of_involution) | (intros; apply GlobalTheory.hensel_norm_lift_of_involution <;> assumption)
end

section
namespace GlobalTheory.FieldCaseReduction

open Polynomial

theorem field_case (F : Type) [Field F] [Finite F] (t m f : F) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ a b : F, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  classical
  by_cases h2 : ringChar F = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two h2 f
    exact ⟨a, 0, by rw [ha]; ring⟩
  · haveI := Fintype.ofFinite F
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hp : (X ^ 2 : F[X]).degree = 2 := by simp
    have hq : (C (-(t ^ 2 - 4 * m)) * X ^ 2 + C 0 * X + C (-(4 * f)) : F[X]).degree = 2 :=
      degree_quadratic (neg_ne_zero.mpr hD)
    obtain ⟨x, b, hxb⟩ := FiniteField.exists_root_sum_quadratic hp hq hodd
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hxb
    refine ⟨(x - t * b) / 2, b, ?_⟩
    field_simp
    linear_combination hxb

theorem main (S : Type) [inst : CommRing S] [Finite S] [IsReduced S] (t m f : S)
    (hD : IsUnit (t ^ (2 : ℕ) - (4 : S) * m)) (_hf : IsUnit f) :
    ∃ (a : S) (b : S), a ^ (2 : ℕ) + t * a * b + m * b ^ (2 : ℕ) = f := by
  classical
  haveI : IsArtinianRing S := isArtinian_of_finite
  let e := (IsArtinianRing.equivPi S).toRingEquiv
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 + e t I * a * b + e m I * b ^ 2 = e f I := by
    intro I
    haveI := I.isMaximal
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    apply field_case
    have h := (hD.map ((Pi.evalRingHom (fun J : MaximalSpectrum S => S ⧸ J.asIdeal) I).comp
      e.toRingHom)).ne_zero
    simp only [map_sub, map_mul, map_pow, map_ofNat] at h
    exact h
  choose a b hab using key
  refine ⟨e.symm a, e.symm b, e.injective ?_⟩
  simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply]
  funext I
  exact hab I

end GlobalTheory.FieldCaseReduction
end

section
open Polynomial

namespace GlobalTheory

theorem binQuad_represents_unit_of_finite_reduced (S : Type) [CommRing S] [Finite S]
    [IsReduced S] (t m f : S) (hd : IsUnit (t ^ 2 - 4 * m)) (hf : IsUnit f) :
    ∃ a b : S, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  first
  | exact @_root_.GlobalTheory.FieldCaseReduction.main
  | exact _root_.GlobalTheory.FieldCaseReduction.main
  | (apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FieldCaseReduction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FieldCaseReduction.main ..)

theorem norm_surj_of_finite_reduced_involution : ∀ (R : Type) [CommRing R] [Finite R]
    [IsReduced R] (τ : R →+* R), (∀ x, τ (τ x) = x) → ∀ θ : R, IsUnit (θ - τ θ) →
    ∀ f : R, IsUnit f → τ f = f → ∃ c : R, τ c * c = f := by
  intro R _ _ _ τ hτ θ hθ f hf hτf
  classical
  let A : Subring R := τ.eqLocus (RingHom.id R)
  have memA : ∀ x, τ x = x → x ∈ A := fun x hx => show τ x = RingHom.id R x from hx
  have fixA : ∀ x : A, τ (x : R) = x := fun x => x.2
  obtain ⟨u, hu⟩ := hθ
  have h4 : ((4 : A) : R) = 4 := map_ofNat A.subtype 4
  have hτd : τ (θ - τ θ) = -(θ - τ θ) := by rw [map_sub, hτ]; ring
  have hτdi : τ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : τ (↑u⁻¹ : R) * (θ - τ θ) = -1 := by
      have := congrArg τ u.inv_mul
      rw [map_mul, map_one, hu, hτd] at this
      linear_combination -this
    calc τ (↑u⁻¹ : R) = τ ↑u⁻¹ * ((θ - τ θ) * ↑u⁻¹) := by rw [← hu, u.mul_inv, mul_one]
      _ = -↑u⁻¹ := by rw [← mul_assoc, h1]; ring
  obtain ⟨v, hv⟩ := hf
  have hτfi : τ (↑v⁻¹ : R) = ↑v⁻¹ := by
    have h1 : τ (↑v⁻¹ : R) * f = 1 := by
      rw [← hτf, ← map_mul, ← hv, v.inv_mul, map_one]
    calc τ (↑v⁻¹ : R) = τ ↑v⁻¹ * (f * ↑v⁻¹) := by rw [← hv, v.mul_inv, mul_one]
      _ = ↑v⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let tA : A := ⟨θ + τ θ, memA _ (by rw [map_add, hτ, add_comm])⟩
  let mA : A := ⟨θ * τ θ, memA _ (by rw [map_mul, hτ, mul_comm])⟩
  let fA : A := ⟨f, memA _ hτf⟩
  let wA : A := ⟨↑u⁻¹ * ↑u⁻¹, memA _ (by rw [map_mul, hτdi]; ring)⟩
  let vA : A := ⟨↑v⁻¹, memA _ hτfi⟩
  have hdisc : IsUnit (tA ^ 2 - 4 * mA) := by
    suffices h : (tA ^ 2 - 4 * mA) * wA = 1 from ⟨⟨_, wA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    have e1 : (θ + τ θ) ^ 2 - 4 * (θ * τ θ) = ↑u * ↑u := by rw [hu]; ring
    push_cast [tA, mA, wA]
    rw [h4, e1, show (↑u : R) * ↑u * (↑u⁻¹ * ↑u⁻¹) = (↑u * ↑u⁻¹) * (↑u * ↑u⁻¹) by ring, u.mul_inv,
      one_mul]
  have hfA : IsUnit fA := by
    suffices h : fA * vA = 1 from ⟨⟨_, vA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    push_cast [fA, vA]
    rw [← hv, v.mul_inv]
  haveI : IsReduced A := ⟨fun x hx => Subtype.ext (IsNilpotent.eq_zero (hx.map A.subtype))⟩
  obtain ⟨a, b, hab⟩ := binQuad_represents_unit_of_finite_reduced A tA mA fA hdisc hfA
  have hab' := congrArg Subtype.val hab
  push_cast [tA, mA, fA] at hab'
  refine ⟨(a : R) + θ * b, ?_⟩
  rw [map_add, map_mul, fixA a, fixA b]
  linear_combination hab'

end GlobalTheory
end

section
open IsDedekindDomain

namespace GlobalTheory

theorem finite_quotient_jacobson_of_finite_residueField (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] : Finite (A ⧸ (⊥ : Ideal A).jacobson) := by
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ

  have hm : ∀ m ∈ IsLocalRing.maximalIdeal O, algebraMap O A m ∈ J := by
    intro m hm
    rw [hJ, Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have : (M.comap (algebraMap O A)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h := IsLocalRing.eq_maximalIdeal this
    have : m ∈ M.comap (algebraMap O A) := h ▸ hm
    exact this
  have hfin : Module.Finite O (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ J)
  have hsurj : Function.Surjective (IsLocalRing.residue O) := Ideal.Quotient.mk_surjective
  let f : (Fin n → IsLocalRing.ResidueField O) → A ⧸ J :=
    fun y ↦ ∑ i, Function.surjInv hsurj (y i) • s i
  have : Function.Surjective f := by
    intro q
    have hq : q ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hq
    refine ⟨fun i ↦ IsLocalRing.residue O (c i), ?_⟩
    simp only [f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hd : Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i ∈
        IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, Function.surjInv_eq hsurj, sub_self]
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    have h0 : algebraMap O (A ⧸ J) (Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i)
        = 0 := by
      rw [IsScalarTower.algebraMap_apply O A (A ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hm _ hd
    rw [h0, zero_mul]
  exact Finite.of_surjective f this

theorem exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type)
      [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) →
      ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a →
      ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  intro O _ _ _ A _ _ _ τ hτ θ hθ a ha hτa
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ
  have : Finite (A ⧸ J) := finite_quotient_jacobson_of_finite_residueField O A
  have : IsReduced (A ⧸ J) := by
    refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.isRadical_jacobson ⊥ ⟨k, hk⟩)
  have hτJ : J ≤ J.comap τ := by
    intro x hx
    rw [Ideal.mem_comap, hJ, Ideal.mem_jacobson_bot] at *
    intro b
    have h := (hx (τ b)).map τ
    simpa [hτ] using h
  let τ' : A ⧸ J →+* A ⧸ J := Ideal.quotientMap J τ hτJ
  have hτ' : ∀ x, τ' (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (τ x) := fun x ↦
    Ideal.quotientMap_mk
  have hinv : ∀ x, τ' (τ' x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ', hτ', hτ]
  obtain ⟨c, hc⟩ := norm_surj_of_finite_reduced_involution (A ⧸ J) τ' hinv
    (Ideal.Quotient.mk J θ) (by rw [hτ', ← map_sub]; exact hθ.map _)
    (Ideal.Quotient.mk J a) (ha.map _) (by rw [hτ', hτa])
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, isUnit_of_isUnit_mk_of_le_jacobson le_rfl ?_, ?_⟩
  · have : IsUnit (τ' (Ideal.Quotient.mk J t) * Ideal.Quotient.mk J t) := hc ▸ ha.map _
    exact isUnit_of_mul_isUnit_right this
  · rw [← Ideal.Quotient.eq, map_mul, ← hτ', mul_comm, hc]

end GlobalTheory
end

section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) → ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a → ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  first | (exact @GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (exact GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (intros; apply GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField  <;> assumption)
end

section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  first | (exact @GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (exact GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (intros; apply GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField <;> assumption)
end

section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.OrbFinAf
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem normStep_isIntV_add {G : HTGroup p} {v : AwayP p} {y z : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y)
    (hz : IsIntV G v z) : IsIntV G v (y + z) := by
  intro i; rw [map_add, Finsupp.add_apply]; exact add_mem (hy i) (hz i)

theorem normStep_isIntV_neg {G : HTGroup p} {v : AwayP p} {y : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y) :
    IsIntV G v (-y) := by
  intro i; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy i)

theorem normStep_isIntV_zero {G : HTGroup p} {v : AwayP p} : IsIntV G v 0 := by
  intro i; rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem normStep_isIntV_smul {G : HTGroup p} {v : AwayP p} {r : Qv v} {y : Qv v ⊗[ℚ] G.C}
    (hr : r ∈ v.1.adicCompletionIntegers ℚ) (hy : IsIntV G v y) : IsIntV G v (r • y) := by
  intro i; rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hr (hy i)

theorem normStep_star_star (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R y).unop).unop = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem normStep_star_mul (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y z : R ⊗[ℚ] G.C) :
    (starT G.star R (y * z)).unop = (starT G.star R z).unop * (starT G.star R y).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem normStep_star_comm (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (y : Qv v ⊗[ℚ] G.C) (hy : y * g = g * y) :
    (starT G.star (Qv v) y).unop * g = g * (starT G.star (Qv v) y).unop := by
  set yh := (starT G.star (Qv v) y).unop with hyh
  set gh := (starT G.star (Qv v) (g : Qv v ⊗[ℚ] G.C)).unop with hgh
  set cc := algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c with hcc'
  have key : gh * yh = yh * gh := by
    have := congrArg (fun x => (starT G.star (Qv v) x).unop) hy
    simpa only [normStep_star_mul] using this
  have hgi : gh = (↑g⁻¹ : Qv v ⊗[ℚ] G.C) * cc := by rw [← hg, ← mul_assoc, Units.inv_mul, one_mul]
  have hcu : IsUnit cc := c.isUnit.map _
  have hcc : ∀ x, cc * x = x * cc := fun x => Algebra.commutes _ _
  have h1 : yh * (↑g⁻¹ : Qv v ⊗[ℚ] G.C) = ↑g⁻¹ * yh := by
    apply hcu.mul_left_injective
    show yh * ↑g⁻¹ * cc = ↑g⁻¹ * yh * cc
    calc yh * ↑g⁻¹ * cc = yh * gh := by rw [hgi, mul_assoc]
      _ = gh * yh := key.symm
      _ = ↑g⁻¹ * yh * cc := by rw [hgi, mul_assoc, mul_assoc, hcc yh]
  calc yh * ↑g = ↑g * (↑g⁻¹ * yh) * ↑g := by rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = ↑g * (yh * ↑g⁻¹) * ↑g := by rw [h1]
    _ = ↑g * yh := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem normStep_exists (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ)
    (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (hstar : ∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop)
    (hcomm : ∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y)
    (θ θ' h : Qv v ⊗[ℚ] G.C) (hθg : θ * g = g * θ) (hθ'g : θ' * g = g * θ') (hhg : h * g = g * h)
    (hθi : IsIntV G v θ) (hθ'i : IsIntV G v θ') (hhi : IsIntV G v h)
    (hθθ' : (θ - (starT G.star (Qv v) θ).unop) * θ' = 1) (h2 : 2 * h = 1)
    (s : (Qv v ⊗[ℚ] G.C)ˣ) (hsg : s * g = g * s) (hsi : IsIntV G v (s : Qv v ⊗[ℚ] G.C))
    (hsii : IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hsfix : (starT G.star (Qv v) s).unop = s) :
    ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧
      IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
      (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  classical
  let A : Subring (Qv v ⊗[ℚ] G.C) :=
    { carrier := {y | y * g = g * y ∧ IsIntV G v y}
      mul_mem' := fun {a b} ha hb => ⟨Commute.mul_left ha.1 hb.1, hmul _ _ ha.2 hb.2⟩
      one_mem' := ⟨Commute.one_left _, h1⟩
      add_mem' := fun {a b} ha hb => ⟨Commute.add_left ha.1 hb.1, normStep_isIntV_add ha.2 hb.2⟩
      zero_mem' := ⟨Commute.zero_left _, normStep_isIntV_zero⟩
      neg_mem' := fun {a} ha => ⟨Commute.neg_left ha.1, normStep_isIntV_neg ha.2⟩ }
  letI : CommRing A :=
    { (inferInstance : Ring A) with mul_comm := fun a b => Subtype.ext (hcomm _ _ a.2.1 b.2.1) }
  have hτmem : ∀ y ∈ A, (starT G.star (Qv v) y).unop ∈ A := fun y hy =>
    ⟨normStep_star_comm G v g c hg y hy.1, hstar y hy.2⟩
  let τ : A →+* A :=
    { toFun := fun y => ⟨(starT G.star (Qv v) y).unop, hτmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) * b)).unop =
          (starT G.star (Qv v) a).unop * (starT G.star (Qv v) b).unop
        rw [normStep_star_mul]; exact hcomm _ _ (hτmem b b.2).1 (hτmem a a.2).1)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) + b)).unop =
          (starT G.star (Qv v) a).unop + (starT G.star (Qv v) b).unop
        rw [map_add, MulOpposite.unop_add]) }
  have hτinv : ∀ a, τ (τ a) = a := fun a => Subtype.ext (normStep_star_star G (Qv v) a)
  let O := v.1.adicCompletionIntegers ℚ
  let φ : O →+* A := ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (algebraMap O (Qv v))).codRestrict A
    (fun r => ⟨Algebra.commutes _ _, by
      show IsIntV G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r))
      rw [Algebra.algebraMap_eq_smul_one]
      exact normStep_isIntV_smul r.2 h1⟩)
  letI : Algebra O A := φ.toAlgebra
  let cf : A →ₗ[O] (Fin (Module.finrank ℚ G.C) → O) :=
    { toFun := fun y i => ⟨(basV G v).repr (y : Qv v ⊗[ℚ] G.C) i, y.2.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext
        show (basV G v).repr ((a : Qv v ⊗[ℚ] G.C) + b) i = (basV G v).repr a i + (basV G v).repr b i
        rw [map_add, Finsupp.add_apply]
      map_smul' := fun r a => by
        funext i; apply Subtype.ext
        show (basV G v).repr (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r) * a) i =
          (r : Qv v) * (basV G v).repr a i
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        rfl }
  have hinj : Function.Injective cf := by
    intro a b hab
    apply Subtype.ext
    apply (basV G v).repr.injective
    exact Finsupp.ext fun i => congrArg (fun f => ((f i : O) : Qv v)) hab
  haveI : Module.Finite O A := Module.Finite.of_injective cf hinj
  obtain ⟨hhen, hfin⟩ := GlobalTheory.T.padicIntegers_henselian_finiteResidue v.1
  haveI := hhen
  haveI := hfin
  let θA : A := ⟨θ, hθg, hθi⟩
  have hθu : IsUnit (θA - τ θA) := IsUnit.of_mul_eq_one (a := θA - τ θA) (⟨θ', hθ'g, hθ'i⟩ : A) (Subtype.ext hθθ')
  have hsg' : s⁻¹ * g = g * s⁻¹ := Commute.inv_left hsg
  let sA : A := ⟨s, congrArg Units.val hsg, hsi⟩
  let siA : A := ⟨↑s⁻¹, congrArg Units.val hsg', hsii⟩
  have hsu : IsUnit sA := IsUnit.of_mul_eq_one (a := sA) siA (Subtype.ext s.mul_inv)
  have hτs : τ sA = sA := Subtype.ext hsfix
  obtain ⟨t₀, ht₀, ht₀J⟩ := GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson O A τ hτinv θA hθu sA hsu hτs
  haveI : HenselianRing A (⊥ : Ideal A).jacobson := GlobalTheory.henselianRing_of_finite O _ le_rfl
  have hτJ : ∀ a ∈ (⊥ : Ideal A).jacobson, τ a ∈ (⊥ : Ideal A).jacobson := by
    intro a ha
    rw [Ideal.mem_jacobson_bot] at ha ⊢
    intro b
    have := (ha (τ b)).map τ
    rwa [map_add, map_mul, hτinv, map_one] at this
  have h2A : IsUnit (2 : A) := IsUnit.of_mul_eq_one (a := (2 : A)) (⟨h, hhg, hhi⟩ : A) (Subtype.ext (by
    show ((2 : A) : Qv v ⊗[ℚ] G.C) * h = 1
    rw [show ((2 : A) : Qv v ⊗[ℚ] G.C) = 2 from map_ofNat A.subtype 2]
    exact h2))
  obtain ⟨t, ht, htt⟩ := GlobalTheory.T.henselian_norm_lift A _ τ hτinv h2A hτJ sA t₀ hsu hτs ht₀ ht₀J
  refine ⟨Units.map (A.subtype : A →* Qv v ⊗[ℚ] G.C) ht.unit, ?_, ?_, ?_, ?_⟩
  · exact Units.ext t.2.1
  · exact t.2.2
  · exact ((ht.unit⁻¹ : Aˣ) : A).2.2
  · exact congrArg Subtype.val htt

end GlobalTheory.OrbFinAf
end
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_order_centralizer_stable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ), (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c → IsIntV G v 1 → (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) → (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) → (∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y) → ∀ θ θ' h : Qv v ⊗[ℚ] G.C, θ * g = g * θ → θ' * g = g * θ' → h * g = g * h → IsIntV G v θ → IsIntV G v θ' → IsIntV G v h → (θ - (starT G.star (Qv v) θ).unop) * θ' = 1 → 2 * h = 1 → ∀ s : (Qv v ⊗[ℚ] G.C)ˣ, s * g = g * s → IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) → (starT G.star (Qv v) s).unop = s → ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧ (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  first | (exact @GlobalTheory.OrbFinAf.normStep_exists) | (exact GlobalTheory.OrbFinAf.normStep_exists) | (intros; apply GlobalTheory.OrbFinAf.normStep_exists  <;> assumption)
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.KottAlmost

section Generic

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

def shU (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : Aˣ where
  val := (σ u).unop
  inv := (σ ((u⁻¹ : Aˣ) : A)).unop
  val_inv := by rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  inv_val := by rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem shU_inv_val (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : (((shU σ u)⁻¹ : Aˣ) : A) = (σ ((u⁻¹ : Aˣ) : A)).unop := rfl

theorem sh_mul (σ : A →+* Aᵐᵒᵖ) (a b : A) : (σ (a * b)).unop = (σ b).unop * (σ a).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem comm_sh (σ : A →+* Aᵐᵒᵖ) (a : A) (y : Aˣ) (cy : Kˣ)
    (hy : (y : A) * (σ y).unop = algebraMap K A cy) (ha : a * y = y * a) :
    (σ a).unop * y = y * (σ a).unop := by
  have hsy : (σ y).unop = ((y⁻¹ : Aˣ) : A) * algebraMap K A cy := by
    rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
  have h := congrArg (fun z => (σ z).unop) ha
  simp only [sh_mul] at h
  rw [hsy] at h
  have h' : (((y⁻¹ : Aˣ) : A) * (σ a).unop) * algebraMap K A cy =
      ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * algebraMap K A cy := by
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, h]; simp only [mul_assoc]
  have hk : IsUnit (algebraMap K A cy) := cy.isUnit.map (algebraMap K A)
  have h'' := hk.mul_right_cancel h'
  calc (σ a).unop * y = y * (((y⁻¹ : Aˣ) : A) * (σ a).unop) * y := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = y * ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * y := by rw [h'']
    _ = y * (σ a).unop := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

end Generic

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

section Step

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

theorem step (σ : A →+* Aᵐᵒᵖ) (hinv : ∀ a, (σ (σ a).unop).unop = a)
    (I : A → Prop) (J : K → Prop) (hJ1 : J 1)
    (h1 : ∀ a b, I a → I b → I (a * b)) (h2 : ∀ a, I a → I (σ a).unop)
    (γ : uGroup (A := K) σ)
    (h3 : ∀ g : Aˣ, I ((g⁻¹ * (γ : Aˣ × Kˣ).1 * g : Aˣ) : A) → I ((g⁻¹ * (γ : Aˣ × Kˣ).1⁻¹ * g : Aˣ) : A) →
      ∃ e : Aˣ, e * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * e ∧ I ((e⁻¹ * g : Aˣ) : A) ∧ I ((g⁻¹ * e : Aˣ) : A))
    (h4 : ∀ s : Aˣ, s * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * s → I (s : A) → I ((s⁻¹ : Aˣ) : A) →
      (σ s).unop = s → ∃ t : Aˣ, t * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * t ∧ I (t : A) ∧ I ((t⁻¹ : Aˣ) : A) ∧
        (t : A) * (σ t).unop = s)
    (g : uGroup (A := K) σ)
    (hg : I (((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1 : A) ∧
      I (((((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A)) :
    ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id _) γ, ∃ d : uGroup (A := K) σ,
      (I ((d : Aˣ × Kˣ).1 : A) ∧ I ((((d : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A) ∧ J ((d : Aˣ × Kˣ).2 : K) ∧
        J ((((d : Aˣ × Kˣ).2)⁻¹ : Kˣ) : K)) ∧ g = c * d := by
  obtain ⟨⟨g1, cg⟩, hgm⟩ := g
  obtain ⟨⟨y, cy⟩, hym⟩ := γ
  have hgm' : (g1 : A) * (σ g1).unop = algebraMap K A cg := hgm
  have hym' : (y : A) * (σ y).unop = algebraMap K A cy := hym
  have hg1 : I ((g1⁻¹ * y * g1 : Aˣ) : A) := hg.1
  have hg2 : I ((g1⁻¹ * y⁻¹ * g1 : Aˣ) : A) := by
    have e : (g1⁻¹ * y * g1 : Aˣ)⁻¹ = g1⁻¹ * y⁻¹ * g1 := by group
    rw [← e]; exact hg.2
  obtain ⟨e, he, hu1, hu2⟩ := h3 g1 hg1 hg2
  obtain ⟨u, hu⟩ : ∃ u : Aˣ, u = e⁻¹ * g1 := ⟨_, rfl⟩
  rw [← hu] at hu1
  have hu2' : I ((u⁻¹ : Aˣ) : A) := by
    have : u⁻¹ = g1⁻¹ * e := by rw [hu]; group
    rw [this]; exact hu2
  obtain ⟨s, hs⟩ : ∃ s : Aˣ, s = u * shU σ u := ⟨_, rfl⟩
  have hsv : (s : A) = (u : A) * (σ u).unop := by rw [hs]; rfl
  have hsI : I (s : A) := by rw [hsv]; exact h1 _ _ hu1 (h2 _ hu1)
  have hsI' : I ((s⁻¹ : Aˣ) : A) := by
    rw [hs, _root_.mul_inv_rev, Units.val_mul, shU_inv_val]
    exact h1 _ _ (h2 _ hu2') hu2'
  have hss : (σ s).unop = s := by
    rw [hsv, sh_mul, hinv]
  have hsval : (s : A) = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop := by
    rw [hsv, hu, Units.val_mul, sh_mul, ← hgm']
    simp only [mul_assoc]
  have hey : ((e⁻¹ : Aˣ) : A) * y = y * ((e⁻¹ : Aˣ) : A) := by
    have : e⁻¹ * y = y * e⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, he, mul_inv_cancel_right]
    exact congrArg Units.val this
  have hby := comm_sh σ ((e⁻¹ : Aˣ) : A) y cy hym' hey
  have hsy : s * y = y * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsval]
    calc ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop * y
        = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (y * (σ ((e⁻¹ : Aˣ) : A)).unop) := by rw [mul_assoc, hby]
      _ = ((e⁻¹ : Aˣ) : A) * (y * algebraMap K A cg) * (σ ((e⁻¹ : Aˣ) : A)).unop := by
          rw [mul_assoc ((e⁻¹ : Aˣ) : A), ← mul_assoc (algebraMap K A cg), Algebra.commutes]; simp only [mul_assoc]
      _ = (y : A) * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) := by
          rw [← mul_assoc ((e⁻¹ : Aˣ) : A) (y : A), hey]; simp only [mul_assoc]
  obtain ⟨t, ht, htI, htI', hts⟩ := h4 s hsy hsI hsI' hss
  have hcm : ((e * t : Aˣ) : A) * (σ ((e * t : Aˣ) : A)).unop = algebraMap K A cg := by
    rw [Units.val_mul, sh_mul]
    calc (e : A) * t * ((σ t).unop * (σ e).unop) = e * (t * (σ t).unop) * (σ e).unop := by
          simp only [mul_assoc]
      _ = e * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) * (σ e).unop := by
          rw [hts, hsval]
      _ = algebraMap K A cg * ((σ ((e⁻¹ : Aˣ) : A)).unop * (σ e).unop) := by
          simp only [← mul_assoc, Units.mul_inv, one_mul]
      _ = _ := by rw [← sh_mul, Units.mul_inv, map_one, MulOpposite.unop_one, mul_one]
  have hdm : ((t⁻¹ * u : Aˣ) : A) * (σ ((t⁻¹ * u : Aˣ) : A)).unop = algebraMap K A ((1 : Kˣ) : K) := by
    rw [Units.val_mul, sh_mul, Units.val_one, map_one]
    calc ((t⁻¹ : Aˣ) : A) * u * ((σ u).unop * (σ ((t⁻¹ : Aˣ) : A)).unop)
        = ((t⁻¹ : Aˣ) : A) * ((u : A) * (σ u).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by simp only [mul_assoc]
      _ = ((t⁻¹ : Aˣ) : A) * ((t : A) * (σ t).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by
          rw [hts, hsv]
      _ = 1 := by
          rw [← mul_assoc, Units.inv_mul, one_mul, ← sh_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  refine ⟨⟨(e * t, cg), hcm⟩, ?_, ⟨(t⁻¹ * u, 1), hdm⟩, ⟨h1 _ _ htI' hu1, ?_, hJ1, by rw [inv_one]; exact hJ1⟩, ?_⟩
  · apply Subtype.ext; apply Prod.ext
    · show e * t * y = y * (e * t)
      rw [mul_assoc, ht, ← mul_assoc, he, mul_assoc]
    · show cg * cy = cy * cg
      exact mul_comm _ _
  · show I (((t⁻¹ * u)⁻¹ : Aˣ) : A)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    exact h1 _ _ hu2' htI
  · apply Subtype.ext; apply Prod.ext
    · show g1 = e * t * (t⁻¹ * u)
      rw [hu]; group
    · show cg = cg * 1
      rw [mul_one]

end Step

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

theorem starT_starT {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R a).unop).unop = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => rw [starT_tmul, starT_tmul, G.star_star]
  | add a b ha hb => rw [map_add, MulOpposite.unop_add, map_add, MulOpposite.unop_add, ha, hb]

end GlobalTheory.OrbFinAf.KottAlmost
end
end
