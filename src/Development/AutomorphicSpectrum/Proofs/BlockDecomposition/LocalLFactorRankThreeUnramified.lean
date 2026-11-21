import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Mathlib

section
namespace GlobalTheory.CompanionTheory.EulerThree

noncomputable def cubicFactor (p : ℕ) (a b c s : ℂ) : ℂ :=
  (1 - a * (p : ℂ) ^ (-s))⁻¹ * (1 - b * (p : ℂ) ^ (-s))⁻¹ * (1 - c * (p : ℂ) ^ (-s))⁻¹

theorem norm_param_mul {p : ℕ} (hp : 2 ≤ p) {a : ℂ} (ha : ‖a‖ = 1) (s : ℂ) :
    ‖a * (p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, ha, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem rpow_neg_le_half {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hp'
  exact h1.trans h2

theorem one_sub_ne_zero_of_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : 1 - x ≠ 0 := by
  intro h
  have : x = 1 := (sub_eq_zero.1 h).symm
  rw [this, norm_one] at hx
  norm_num at hx

theorem norm_inv_one_sub_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 - x)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
  have hne := one_sub_ne_zero_of_le hx
  have hlow : 1 / 2 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have e : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
    field_simp
    ring
  rw [e, norm_mul, norm_inv]
  have hinv : ‖1 - x‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [norm_nonneg x]

theorem norm_three_sub_one_le {y₁ y₂ y₃ : ℂ} {t : ℝ} (ht : t ≤ 1 / 2)
    (h₁ : ‖y₁‖ ≤ 2 * t) (h₂ : ‖y₂‖ ≤ 2 * t) (h₃ : ‖y₃‖ ≤ 2 * t) :
    ‖(1 + y₁) * (1 + y₂) * (1 + y₃) - 1‖ ≤ 14 * t := by
  have ht0 : 0 ≤ t := by nlinarith [norm_nonneg y₁]
  have e : (1 + y₁) * (1 + y₂) * (1 + y₃) - 1 =
      y₁ + y₂ + y₃ + y₁ * y₂ + y₁ * y₃ + y₂ * y₃ + y₁ * y₂ * y₃ := by ring
  have m₁₂ : ‖y₁ * y₂‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₂]
  have m₁₃ : ‖y₁ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₃]
  have m₂₃ : ‖y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₂, norm_nonneg y₃]
  have m₁₂₃ : ‖y₁ * y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    have : ‖y₃‖ ≤ 1 := by linarith
    nlinarith [norm_nonneg (y₁ * y₂), norm_nonneg y₃]
  rw [e]
  calc _ ≤ ‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₁ * y₂‖ + ‖y₁ * y₃‖ + ‖y₂ * y₃‖ + ‖y₁ * y₂ * y₃‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_add_le _ _
    _ ≤ 14 * t := by linarith

theorem norm_cubicFactor_sub_one_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    ‖cubicFactor p a b c s - 1‖ ≤ 14 * (p : ℝ) ^ (-s.re) := by
  have ht := rpow_neg_le_half hp hs
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      ‖(1 - u * (p : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * (p : ℝ) ^ (-s.re) := fun hu => by
    have hn := norm_param_mul hp hu s
    have := norm_inv_one_sub_sub_one_le (x := _) (hn.le.trans ht)
    rwa [hn] at this
  have := norm_three_sub_one_le ht (key ha) (key hb) (key hc)
  simpa [cubicFactor] using this

theorem differentiableAt_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun z => cubicFactor p a b c z) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      DifferentiableAt ℂ (fun z : ℂ => (1 - u * (p : ℂ) ^ (-z))⁻¹) s := fun hu => by
    refine ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv ?_
    exact one_sub_ne_zero_of_le ((norm_param_mul hp hu s).le.trans (rpow_neg_le_half hp hs))
  exact ((key ha).mul (key hb)).mul (key hc)

variable {ι : Type*} {p : ι → ℕ} {a b c : ι → ℂ}

theorem summable_rpow_neg (hinj : Function.Injective p) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun i => (p i : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.2 (by linarith)).comp_injective hinj

theorem multipliable_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun i => cubicFactor (p i) (a i) (b i) (c i) s := by
  have hsum : Summable fun i => cubicFactor (p i) (a i) (b i) (c i) s - 1 :=
    Summable.of_norm_bounded ((summable_rpow_neg hinj hs).mul_left 14)
      fun i => norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i) hs.le
  simpa using multipliable_one_add_of_summable hsum.norm

theorem differentiableOn_tprod_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) :
    DifferentiableOn ℂ (fun s => ∏' i, cubicFactor (p i) (a i) (b i) (c i) s)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs : 1 < s.re := hs
  obtain ⟨σ₀, h1, h2⟩ : ∃ σ₀ : ℝ, 1 < σ₀ ∧ σ₀ < s.re := exists_between hs
  let K : Set ℂ := {z | σ₀ < z.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hKd : ∀ i, DifferentiableOn ℂ (fun z => cubicFactor (p i) (a i) (b i) (c i) z) K :=
    fun i z hz => (differentiableAt_cubicFactor (hp i) (ha i) (hb i) (hc i)
      (by have : σ₀ < z.re := hz
          linarith)).differentiableWithinAt
  have hprod := ((summable_rpow_neg hinj h1).mul_left 14).hasProdLocallyUniformlyOn_one_add
    (f := fun i z => cubicFactor (p i) (a i) (b i) (c i) z - 1) hK
    (.of_forall fun i z hz => by
      have hz' : σ₀ < z.re := hz
      refine (norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i)
        (by linarith)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have : (2 : ℝ) ≤ p i := by exact_mod_cast hp i
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    (fun i => ((hKd i).sub (differentiableOn_const _)).continuousOn)
  have hd : DifferentiableOn ℂ
      (fun z => ∏' i, (1 + (cubicFactor (p i) (a i) (b i) (c i) z - 1))) K :=
    hprod.differentiableOn (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ => hKd i)) hK
  have h3 := hd.differentiableAt (hK.mem_nhds h2)
  simp only [add_sub_cancel] at h3
  exact h3.differentiableWithinAt

end GlobalTheory.CompanionTheory.EulerThree
end

section
open Ad3 Ad3.S

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)

namespace GlobalTheory.CompanionTheory.EulerThree.HalfWt

open GlobalTheory.CompanionTheory.EulerThree

theorem unr_mul {v : Pl} {μ κ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ)
    (hκ : IsUnramifiedChar κ) : IsUnramifiedChar (μ * κ) := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  have h2 : κ u = 1 := hκ hu
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]

theorem unr_inv {v : Pl} {μ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) :
    IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]

def parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  (((D.ν v * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parB (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((localChar c v (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((((D.ν v)⁻¹ * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

theorem norm_localChar (c : HeckeCharacter ℚ) (v : Pl) (x : (Qv v)ˣ) :
    ‖((localChar c v x : ℂˣ) : ℂ)‖ = 1 :=
  Circle.norm_coe _

theorem norm_parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parA D c v‖ = 1 := by
  rw [parA, MonoidHom.mul_apply, Units.val_mul, norm_mul, (D.unit v).2, norm_localChar, one_mul]

theorem norm_parB (c : HeckeCharacter ℚ) (v : Pl) : ‖parB c v‖ = 1 :=
  norm_localChar c v _

theorem norm_parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parC D c v‖ = 1 := by
  rw [parC, MonoidHom.mul_apply, Units.val_mul, norm_mul, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, norm_inv, (D.unit v).2, inv_one, norm_localChar, one_mul]

theorem two_le_pOf (hE : faceMap_comp_succAbove_castSucc) (v : Pl) : 2 ≤ pOf v := by
  obtain ⟨e, he⟩ := hE.1
  rw [← he v]
  exact (e v).2.two_le

theorem pOf_injective (hE : faceMap_comp_succAbove_castSucc) : Function.Injective pOf := by
  obtain ⟨e, he⟩ := hE.1
  intro v w h
  apply e.injective
  apply Subtype.ext
  rw [he, he, h]

theorem local_l_factor_rank_three_unramified (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {v : Pl} (hv : v ∉ S) (s : ℂ) :
    lf3 (D.ν v) (localChar c v) s = cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s := by
  have hν : IsUnramifiedChar (D.ν v) := D.unr v (fun h => hv (hA.bad h))
  have hc : IsUnramifiedChar (localChar c v) := hA.unr v hv
  rw [lf3, cubicFactor, hE.2 v _ (unr_mul hν hc), hE.2 v _ hc, hE.2 v _ (unr_mul (unr_inv hν) hc)]
  rfl

theorem multipliable_sub (hE : faceMap_comp_succAbove_castSucc) (D : Dat) (c : HeckeCharacter ℚ) (A : Set Pl) {s : ℂ}
    (hs : 1 < s.re) :
    Multipliable fun v : A => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s :=
  multipliable_cubicFactor (p := fun v : A => pOf v) (a := fun v : A => parA D c v)
    (b := fun v : A => parB c v) (c := fun v : A => parC D c v)
    ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v)
    (fun v => norm_parA D c v) (fun v => norm_parB c v) (fun v => norm_parC D c v) hs

theorem eul_eq (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {T : Finset Pl} (hST : S ⊆ T) (s : ℂ) :
    eul D c T s = ∏' v : {v : Pl // v ∉ T},
      cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s := by
  unfold eul
  exact tprod_congr fun v => local_l_factor_rank_three_unramified hE hA (fun h => v.2 (hST h)) s

theorem norm_lt_one {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_param_mul hp ha]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

theorem one_sub_ne_zero {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : a * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have := norm_lt_one hp ha hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem differentiableAt_factor {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => (1 - a * (p : ℂ) ^ (-z))⁻¹) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv
    (one_sub_ne_zero hp ha hs)

theorem norm_factor_le {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖(1 - a * (p : ℂ) ^ (-s))⁻¹‖ ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have ht1 : (p : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hx : ‖a * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [norm_param_mul hp ha]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hlow : 1 - (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ‖1 - a * (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a * (p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

theorem differentiableOn_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) : DifferentiableOn ℂ (cubicFactor p a b c) (HP 0) := by
  intro s hs
  have hs : 0 < s.re := hs
  exact (((differentiableAt_factor hp ha hs).mul (differentiableAt_factor hp hb hs)).mul
    (differentiableAt_factor hp hc hs)).differentiableWithinAt

theorem norm_cubicFactor_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖cubicFactor p a b c s‖ ≤ ((1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) ^ 3 := by
  have hA := norm_factor_le hp ha hs
  have hB := norm_factor_le hp hb hs
  have hC := norm_factor_le hp hc hs
  have hK : 0 ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := (norm_nonneg _).trans hA
  rw [cubicFactor, norm_mul, norm_mul, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hK) hC (norm_nonneg _) (mul_nonneg hK hK)

open Classical in

theorem adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3 := by
  intro hE D c δ S hA
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hd := differentiableOn_tprod_cubicFactor (p := fun v : {v : Pl // v ∉ S} => pOf v.1)
      (a := fun v => parA D c v.1) (b := fun v => parB c v.1) (c := fun v => parC D c v.1)
      ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v.1)
      (fun v => norm_parA D c v.1) (fun v => norm_parB c v.1) (fun v => norm_parC D c v.1)
    have he : eul D c S = fun s => ∏' v : {v : Pl // v ∉ S},
        cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s :=
      funext (eul_eq hE hA (subset_refl S))
    rw [he]
    exact hd s hs
  · intro T hST s hs
    set G : Pl → ℂ := fun v => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s with hG
    have h1 : ∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s = ∏ v ∈ T \ S, G v :=
      Finset.prod_congr rfl fun v hv => local_l_factor_rank_three_unramified hE hA (Finset.mem_sdiff.1 hv).2 s
    rw [h1, eul_eq hE hA (subset_refl S), eul_eq hE hA hST]
    change (∏' v : ({v | v ∉ S} : Set Pl), G v) = (∏ v ∈ T \ S, G v) * ∏' v : ({v | v ∉ T} : Set Pl), G v
    rw [tprod_subtype, tprod_subtype, ← Finset.tprod_subtype' (T \ S) G, tprod_subtype]
    have m1 : Multipliable ((↑(T \ S) : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    have m2 : Multipliable (({v | v ∉ T} : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    rw [← m1.tprod_mul m2]
    refine tprod_congr fun v => ?_
    by_cases hS : v ∈ S
    · have hT : v ∈ T := hST hS
      simp [Set.mulIndicator_apply, hS, hT]
    · by_cases hT : v ∈ T
      · simp [Set.mulIndicator_apply, hS, hT]
      · simp [Set.mulIndicator_apply, hS, hT]
  · intro v hv
    have he : lf3 (D.ν v) (localChar c v) =
        cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) := funext (local_l_factor_rank_three_unramified hE hA hv)
    rw [he]
    refine ⟨differentiableOn_cubicFactor (two_le_pOf hE v) (norm_parA D c v) (norm_parB c v)
      (norm_parC D c v), _, fun s hs => norm_cubicFactor_le (two_le_pOf hE v) (norm_parA D c v)
      (norm_parB c v) (norm_parC D c v) hs⟩

end GlobalTheory.CompanionTheory.EulerThree.HalfWt
end
end
