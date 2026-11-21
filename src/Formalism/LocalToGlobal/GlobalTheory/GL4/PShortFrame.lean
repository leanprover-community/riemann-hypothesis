import Formalism.LocalRingCardinality.PosOfIsomEmb
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
import Formalism.LocalToGlobal.GlobalTheory.GL4.PShortSpan

section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

variable {E : Type} [Field E] [NumberField E]

theorem abs_norm_eq_prod_re (a : E) (hpos : ∀ φ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ a = c) :
    |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ φ : E →+* ℂ, (φ a).re := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, σ a = ∏ φ : E →+* ℂ, φ a :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ ↦ rfl
  have hre : ∀ φ : E →+* ℂ, ‖φ a‖ = (φ a).re := by
    intro φ
    obtain ⟨c, hc, he⟩ := hpos φ
    rw [he, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.ofReal_re]
  have h4 : ‖(algebraMap ℚ ℂ (Algebra.norm ℚ a))‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
    rw [show (algebraMap ℚ ℂ (Algebra.norm ℚ a)) = (((Algebra.norm ℚ a : ℚ) : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← h4, h2, h3, norm_prod]
  exact Finset.prod_congr rfl fun φ _ ↦ hre φ

theorem sum_re_ge (a : E) (hpos : ∀ φ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ a = c) (X : ℝ) (hX : 0 < X)
    (h1 : 1 ≤ |((Algebra.norm ℚ a : ℚ) : ℝ)| * X) :
    (Module.finrank ℚ E : ℝ) * X ^ (-(1 / (Module.finrank ℚ E : ℝ))) ≤ ∑ φ : E →+* ℂ, (φ a).re := by
  set d : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hd
  have hcard : (Fintype.card (E →+* ℂ) : ℝ) = d := by rw [hd, Embeddings.card]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hc : ∀ φ : E →+* ℂ, 0 < (φ a).re := by
    intro φ
    obtain ⟨c, hc, he⟩ := hpos φ
    rw [he, Complex.ofReal_re]; exact hc
  have hP : ∏ φ : E →+* ℂ, (φ a).re = |((Algebra.norm ℚ a : ℚ) : ℝ)| := (abs_norm_eq_prod_re a hpos).symm
  have hPX : X⁻¹ ≤ ∏ φ : E →+* ℂ, (φ a).re := by
    rw [hP, inv_le_iff_one_le_mul₀ hX, mul_comm]; linarith
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (E →+* ℂ)) (fun _ ↦ 1 / d)
    (fun φ ↦ (φ a).re) (fun _ _ ↦ by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp)
    (fun φ _ ↦ (hc φ).le)
  rw [Real.finsetProd_rpow _ _ (fun φ _ ↦ (hc φ).le), ← Finset.mul_sum] at hgm
  have hmono : X⁻¹ ^ (1 / d) ≤ (∏ φ : E →+* ℂ, (φ a).re) ^ (1 / d) :=
    Real.rpow_le_rpow (by positivity) hPX (by positivity)
  rw [Real.inv_rpow hX.le, ← Real.rpow_neg hX.le] at hmono
  calc d * X ^ (-(1 / d)) ≤ d * (1 / d * ∑ φ : E →+* ℂ, (φ a).re) := by gcongr; exact hmono.trans hgm
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField Matrix
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def trR (a : E) : ℝ := (∑ σ : E →+* ℂ, σ a).re

theorem trR_eq (a : E) : trR a = ((Algebra.trace ℚ E a : ℚ) : ℝ) := by
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := a)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ a = ∑ φ : E →+* ℂ, φ a :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ ↦ rfl
  unfold trR
  rw [← h3, ← h2]
  simp

theorem trR_add (a b : E) : trR (a + b) = trR a + trR b := by
  simp [trR, Finset.sum_add_distrib]

theorem trR_star (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (a : E) : trR (star a) = trR a := by
  unfold trR
  simp only [hσ, ← star_sum]
  simp

structure Model (S : HSpace E) where
  Y : (E →+* ℂ) → Matrix (Fin S.rank) (Fin S.rank) ℂ
  hY : ∀ σ (y : S.V), ∑ i, ‖(Y σ *ᵥ fun j ↦ σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re

theorem model_exists (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) : Nonempty (Model S) := by
  have h : ∀ σ : E →+* ℂ, ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ,
      ∀ y : S.V, ∑ i, ‖(Y *ᵥ fun j ↦ σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
    intro σ
    have hs := hsig σ
    rw [hpos σ] at hs
    obtain ⟨Y, -, hY⟩ := S.frame_of_pos σ (fun a ↦ hσ σ a) hs
    exact ⟨Y, hY⟩
  choose Y hY using h
  exact ⟨⟨Y, hY⟩⟩

abbrev Idx (S : HSpace E) := (E →+* ℂ) × Fin S.rank × Bool

def vec {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x : S.V) : Fin S.rank → ℂ :=
  M.Y σ *ᵥ fun j ↦ σ (S.frame.repr x j)

theorem vec_add {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x y : S.V) :
    vec M σ (x + y) = vec M σ x + vec M σ y := by
  unfold vec
  rw [← Matrix.mulVec_add]
  congr 1
  ext j
  simp

theorem vec_rat {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (r : ℚ) (x : S.V) :
    vec M σ ((r : E) • x) = (r : ℂ) • vec M σ x := by
  unfold vec
  rw [← Matrix.mulVec_smul]
  congr 1
  ext j
  simp

def psi {S : HSpace E} (M : Model S) : S.V →+ EuclideanSpace ℝ (Idx S) where
  toFun x := WithLp.toLp 2 fun p ↦ if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im
  map_zero' := by
    ext p
    simp only [vec, map_zero, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h0 : (fun _ : Fin S.rank ↦ (0 : ℂ)) = 0 := rfl
    rw [h0, Matrix.mulVec_zero]
    split_ifs <;> simp
  map_add' x y := by
    ext p
    simp only [vec_add, Pi.add_apply, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> rfl

theorem psi_apply {S : HSpace E} (M : Model S) (x : S.V) (p : Idx S) :
    psi M x p = if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im := rfl

theorem psi_rat {S : HSpace E} (M : Model S) (r : ℚ) (x : S.V) : psi M ((r : E) • x) = (r : ℝ) • psi M x := by
  ext p
  rw [PiLp.smul_apply, psi_apply, psi_apply, vec_rat]
  have : ((r : ℂ)) = ((r : ℝ) : ℂ) := by simp
  rw [this]
  split_ifs <;> simp [smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem norm_psi_sq {S : HSpace E} (M : Model S) (x : S.V) : ‖psi M x‖ ^ 2 = trR (S.hT x x) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, trR, Complex.re_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Fintype.sum_prod_type, ← M.hY σ x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_bool, psi_apply, psi_apply]
  simp only [if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [vec]
  ring

theorem inner_psi {S : HSpace E} (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (M : Model S) (x y : S.V) :
    ⟪psi M x, psi M y⟫_ℝ = trR (S.hT x y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add]
  have h1 := norm_psi_sq M (x + y)
  have h2 := norm_psi_sq M x
  have h3 := norm_psi_sq M y
  rw [sq] at h1 h2 h3
  rw [h1, h2, h3]
  have hsym : S.hT y x = star (S.hT x y) := (S.herm.eq x y).symm
  simp only [map_add, LinearMap.add_apply, trR_add, hsym, trR_star hσ]
  ring

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def starO (w : 𝓞 E) : 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E) w

theorem starO_coe (w : 𝓞 E) : ((starO w : 𝓞 E) : E) = star (w : E) := rfl

theorem trace_star (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (a : E) :
    Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a := by
  apply (algebraMap ℚ ℂ).injective
  rw [trace_eq_sum_embeddings (E := ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ (star a) = star (∑ σ : E →ₐ[ℚ] ℂ, σ a) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ hσ σ.toRingHom a
  rw [h1, ← trace_eq_sum_embeddings (E := ℂ)]
  simp

theorem mem_dual_one_iff (x : E) :
    x ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ w : 𝓞 E, Algebra.trace ℚ E (x * w) ∈ (algebraMap ℤ ℚ).range := by
  rw [mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  constructor
  · intro h w
    exact h _ ((mem_one_iff _).2 ⟨w, rfl⟩)
  · intro h y hy
    obtain ⟨w, rfl⟩ := (mem_one_iff _).1 hy
    exact h w

def TrDual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Prop :=
  ∀ l ∈ L, Algebra.trace ℚ E (S.hT l z) ∈ (algebraMap ℤ ℚ).range

theorem hT_smul_left (S : HSpace E) (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

theorem hT_left_mem_dual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) : S.hT l z ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_dual_one_iff]
  intro w
  have hm : (starO w) • l ∈ L := L.smul_mem _ hl
  have := hz _ hm
  rw [← algebraMap_smul E (starO w) l, hT_smul_left] at this
  have e : star (algebraMap (𝓞 E) E (starO w)) * S.hT l z = S.hT l z * (w : E) := by
    rw [show algebraMap (𝓞 E) E (starO w) = star (w : E) from rfl, star_star, mul_comm]
  rwa [e] at this

theorem hT_right_mem_dual (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a))
    (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) : S.hT z l ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hx := hT_left_mem_dual S L z hz hl
  rw [mem_dual_one_iff] at hx ⊢
  intro w
  have h1 := hx (starO w)
  have hsym : S.hT z l = star (S.hT l z) := (S.herm.eq l z).symm
  rw [hsym, ← trace_star hσ, star_mul, star_star, mul_comm]
  rwa [starO_coe] at h1

theorem dual_mul_diff :
    dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) * ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
      = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact mul_inv_cancel₀ (dual_ne_zero ℤ ℚ one_ne_zero)

theorem diff_smul_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {δ : 𝓞 E} (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) : δ • z ∈ dualSub S L := by
  intro l hl
  have hx := hT_left_mem_dual S L z hz hl
  have hm : S.hT l z * (δ : E) ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    mul_mem_mul hx ((mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩)
  rw [dual_mul_diff, mem_one_iff] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨w, ?_⟩
  rw [← algebraMap_smul E δ z, map_smul, smul_eq_mul, hw, mul_comm]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def bIdeal (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Ideal (𝓞 E) :=
  L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z) ⊓ differentIdeal ℤ (𝓞 E)

theorem relIndex_bIdeal (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≤ q ∧
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≠ 0 := by
  set g : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V z).toAddMonoidHom with hg
  have hc : (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup = L.toAddSubgroup.comap g := by
    ext w; rfl
  have hb : (bIdeal S L z).toAddSubgroup =
      (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup ⊓ (differentIdeal ℤ (𝓞 E)).toAddSubgroup := by
    ext w; rfl
  rw [hb, AddSubgroup.inf_relIndex_right, hc, AddSubgroup.relIndex_comap]
  have hle : (differentIdeal ℤ (𝓞 E)).toAddSubgroup.map g ≤ dualSub S L := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact diff_smul_mem S L z hz hδ
  have hq' : L.toAddSubgroup.relIndex (dualSub S L) ≠ 0 := by rw [hL.2]; exact hq
  refine ⟨hL.2 ▸ AddSubgroup.relIndex_le_of_le_right hle hq', fun h ↦ hq' ?_⟩
  exact AddSubgroup.relIndex_eq_zero_of_le_right hle h

theorem absNorm_bIdeal (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    Ideal.absNorm (bIdeal S L z) ≤ q * (discr E).natAbs ∧ Ideal.absNorm (bIdeal S L z) ≠ 0 := by
  obtain ⟨h1, h2⟩ := relIndex_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hmul := AddSubgroup.relIndex_mul_index (H := (bIdeal S L z).toAddSubgroup)
    (K := (differentIdeal ℤ (𝓞 E)).toAddSubgroup) (fun x hx ↦ hx.2)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hd] at hmul
  rw [← hmul]
  exact ⟨Nat.mul_le_mul_right _ h1, mul_ne_zero h2 hd0⟩

theorem one_le_norm (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (q : ℕ)
    (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0) (z : S.V) (hz : TrDual S L z)
    (ha : S.hT z z ≠ 0) :
    1 ≤ |Algebra.norm ℚ (S.hT z z)| * ((q : ℚ) * ((discr E).natAbs : ℚ) ^ 2) := by
  set a := S.hT z z with ha_def
  set 𝔟 := bIdeal S L z with h𝔟
  set 𝔡 := differentIdeal ℤ (𝓞 E) with h𝔡
  obtain ⟨hbn, hb0⟩ := absNorm_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm 𝔡 = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hle1 : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) ≤ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨w, rfl⟩ := (mem_spanSingleton _).1 hi
    obtain ⟨b, hb, rfl⟩ := (mem_coeIdeal _).1 hj
    have hwb : w * b ∈ 𝔟 := 𝔟.mul_mem_left w hb
    have hL' : (w * b) • z ∈ L := hwb.1
    have hm := hT_right_mem_dual S hσ L z hz hL'
    have e : S.hT z ((w * b) • z) = w • a * algebraMap (𝓞 E) E b := by
      rw [← algebraMap_smul E (w * b) z, map_smul, smul_eq_mul, Algebra.smul_def, map_mul]
      ring
    rwa [e] at hm
  have hJ : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 :=
    (FractionalIdeal.mul_le.2 fun i hi j hj ↦ mul_mem_mul (hle1 hi) hj).trans dual_mul_diff.le
  have hJ0 : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rwa [Ne, spanSingleton_eq_zero_iff]
    · rw [Ne, coeIdeal_eq_zero]
      intro h; apply hb0; change Ideal.absNorm 𝔟 = 0; rw [h, Ideal.absNorm_bot]
    · rw [Ne, coeIdeal_eq_zero]
      intro h; apply hd0; rw [← hd, h, Ideal.absNorm_bot]
  obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.1 hJ
  have hI0 : I ≠ ⊥ := by
    intro h; apply hJ0; rw [← hI, h, coeIdeal_bot]
  have hnI : (1 : ℚ) ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h ↦ hI0 (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hval : FractionalIdeal.absNorm (spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) *
      (𝔡 : FractionalIdeal (𝓞 E)⁰ E)) = |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * Ideal.absNorm 𝔡 := by
    rw [map_mul, map_mul, absNorm_span_singleton, coeIdeal_absNorm, coeIdeal_absNorm]
  rw [← hI, coeIdeal_absNorm] at hval
  rw [hval, hd] at hnI
  have hbq : (Ideal.absNorm 𝔟 : ℚ) ≤ q * (discr E).natAbs := by exact_mod_cast hbn
  have hN : 0 ≤ |Algebra.norm ℚ a| := abs_nonneg _
  have hD : (0 : ℚ) ≤ (discr E).natAbs := by positivity
  calc (1 : ℚ) ≤ |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * (discr E).natAbs := hnI
    _ ≤ |Algebra.norm ℚ a| * (q * (discr E).natAbs) * (discr E).natAbs := by gcongr
    _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

theorem span_short_of_cover {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) (μ : ℝ) (hμ : 0 < μ) (hcov : ∀ x : W, ∃ l ∈ Λ, ‖x - l‖ ≤ μ) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} = ⊤ := by
  set K := Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} with hK
  by_contra hne
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    exact hne (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set x : W := (2 * μ / ‖u‖) • u with hx
  have hxn : ‖x‖ = 2 * μ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hxK : x ∈ Kᗮ := Submodule.smul_mem _ _ hu
  obtain ⟨l, hl, hd⟩ := hcov x
  have hln : ‖l‖ ≤ 3 * μ := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    linarith
  have hlK : l ∈ K := Submodule.subset_span ⟨hl, hln⟩
  have horth : ⟪l, x⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hlK hxK
  have hsq : ‖x - l‖ ^ 2 = ‖x‖ ^ 2 + ‖l‖ ^ 2 := by
    rw [@norm_sub_sq_real, real_inner_comm, horth]
    ring
  have h1 : ‖x - l‖ ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [sq_nonneg ‖l‖]

theorem span_short_of_dual {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (hlam : 0 < lam)
    (hd : ∀ y : W, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) → lam ≤ ‖y‖) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * ((finrank ℝ W : ℝ) / 2 / lam + 1)} = ⊤ := by
  have hμ : 0 < (finrank ℝ W : ℝ) / 2 / lam + 1 := by positivity
  refine span_short_of_cover Λ _ hμ fun x ↦ ?_
  obtain ⟨l, hl, hle⟩ := transference_covering W Λ lam hlam hd x
  refine ⟨l, hl, ?_⟩
  rw [← le_div_iff₀ hlam] at hle
  have : (finrank ℝ W : ℝ) / 2 / lam = (finrank ℝ W : ℝ) / 2 / lam := rfl
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Pos

variable (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK) (hpos : S.IsPosDef)
include hσ hsig hpos

theorem form_pos' (σ : E →+* ℂ) (x : S.V) (hx : x ≠ 0) : ∃ c : ℝ, 0 < c ∧ σ (S.hT x x) = c :=
  S.form_pos hsig σ (fun a ↦ hσ σ a) (hpos σ) x hx

theorem norm_eq_re (σ : E →+* ℂ) (x : S.V) : ‖σ (S.hT x x)‖ = (σ (S.hT x x)).re := by
  by_cases hx : x = 0
  · subst hx; simp
  · obtain ⟨c, hc, he⟩ := form_pos' S hσ hsig hpos σ x hx
    rw [he, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.ofReal_re]

theorem trR_pos (x : S.V) (hx : x ≠ 0) : 0 < trR (S.hT x x) := by
  unfold trR
  rw [Complex.re_sum]
  have hne : (Finset.univ : Finset (E →+* ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, Embeddings.card]
    exact Module.finrank_pos
  refine Finset.sum_pos (fun σ _ ↦ ?_) hne
  obtain ⟨c, hc, he⟩ := form_pos' S hσ hsig hpos σ x hx
  rw [he, Complex.ofReal_re]; exact hc

theorem eq_zero_of_psi (M : Model S) (x : S.V) (h : psi M x = 0) : x = 0 := by
  by_contra hx
  have := trR_pos S hσ hsig hpos x hx
  rw [← norm_psi_sq M x, h, norm_zero] at this
  simp at this

theorem trR_dual_ge (q : ℕ) (hq : q ≠ 0) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (z : S.V) (hz : TrDual S L z)
    (hz0 : z ≠ 0) :
    (finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))) ≤ trR (S.hT z z) := by
  have ha : S.hT z z ≠ 0 := by
    intro h0
    have := trR_pos S hσ hsig hpos z hz0
    rw [h0] at this
    simp [trR] at this
  have h1 := one_le_norm S hσ q L hL hq z hz ha
  have hX : (0 : ℝ) < (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have h1' : (1 : ℝ) ≤ |((Algebra.norm ℚ (S.hT z z) : ℚ) : ℝ)| * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  have := sum_re_ge (S.hT z z) (fun σ ↦ form_pos' S hσ hsig hpos σ z hz0) _ hX h1'
  unfold trR
  rw [Complex.re_sum]
  exact this

end Pos

section Basis

def GQ (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℚ :=
  fun i j ↦ Algebra.trace ℚ E (S.hT (e i : S.V) (e j : S.V))

theorem inner_e {S : HSpace E} (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (M : Model S)
    (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    ⟪psi M (e i : S.V), psi M (e j : S.V)⟫_ℝ = (GQ S L e i j : ℝ) := by
  rw [inner_psi hσ, trR_eq]; rfl

theorem psi_sum_rat {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι]
    (e : Basis ι ℤ L) (c : ι → ℚ) :
    psi M (∑ i, (c i : E) • (e i : S.V)) = ∑ i, (c i : ℝ) • psi M (e i : S.V) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ psi_rat M (c i) _

theorem psi_sum_int {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι]
    (e : Basis ι ℤ L) (c : ι → ℤ) :
    psi M (∑ i, c i • (e i : S.V)) = ∑ i, c i • psi M (e i : S.V) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_zsmul _ _ _

theorem GQ_det (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : (GQ S L e).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set x : S.V := ∑ i, (c i : E) • (e i : S.V) with hx
  have hnorm : ⟪psi M x, psi M x⟫_ℝ = 0 := by
    rw [hx, psi_sum_rat M L e, sum_inner]
    have : ∀ i, ⟪(c i : ℝ) • psi M (e i : S.V), ∑ j, (c j : ℝ) • psi M (e j : S.V)⟫_ℝ =
        (c i : ℝ) * (((GQ S L e) *ᵥ c) i : ℝ) := by
      intro i
      rw [real_inner_smul_left, inner_sum]
      congr 1
      simp only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct]
      push_cast
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp only [this, hc, Pi.zero_apply, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
  have hx0 : x = 0 := by
    apply eq_zero_of_psi S hσ hsig hpos M
    exact inner_self_eq_zero.1 hnorm
  apply hc0
  set m : ℕ := ∏ i, (c i).den with hm
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ (c i).den_nz
  have hdvd : ∀ i, (c i).den ∣ m := fun i ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set k : ι → ℤ := fun i ↦ ((m / (c i).den : ℕ) : ℤ) * (c i).num with hk
  have hkq : ∀ i, (k i : ℚ) = (m : ℚ) * c i := by
    intro i
    obtain ⟨t, ht⟩ := hdvd i
    have h1 : m / (c i).den = t := by
      rw [ht, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (c i).den_nz)]
    simp only [hk, h1]
    rw [ht]
    have h2 := Rat.mul_den_eq_num (c i)
    push_cast
    rw [← h2]
    ring
  have hsum : ∑ i, k i • e i = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_zero]
    have : ∀ i, ((k i • e i : L) : S.V) = (m : E) • ((c i : E) • (e i : S.V)) := by
      intro i
      have hz : ((k i • e i : L) : S.V) = k i • (e i : S.V) := by simp
      rw [hz, ← Int.cast_smul_eq_zsmul E, smul_smul]
      congr 1
      have := congrArg (fun t : ℚ ↦ (t : E)) (hkq i)
      push_cast at this
      exact this
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Finset.smul_sum, ← hx, hx0, smul_zero]
  have hk0 := (Fintype.linearIndependent_iff.1 e.linearIndependent) k hsum
  ext i
  have := hkq i
  rw [hk0 i] at this
  simp only [Int.cast_zero, Pi.zero_apply] at this ⊢
  rcases mul_eq_zero.1 this.symm with h | h
  · exact absurd (by exact_mod_cast h) hm0
  · exact h

def GR (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℝ :=
  (GQ S L e).map (Rat.castHom ℝ)

theorem GR_det (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : (GR S L e).det ≠ 0 := by
  have h := RingHom.map_det (Rat.castHom ℝ) (GQ S L e)
  rw [RingHom.mapMatrix_apply] at h
  unfold GR
  rw [← h]
  simpa using GQ_det S hσ hsig hpos M L e

theorem GR_apply (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    GR S L e i j = (GQ S L e i j : ℝ) := rfl

theorem psi_e_linInd (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ fun i ↦ psi M (e i : S.V) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hG : (GR S L e) *ᵥ g = 0 := by
    ext j
    have := congrArg (fun w ↦ ⟪psi M (e j : S.V), w⟫_ℝ) hg
    simp only [inner_sum, real_inner_smul_right, inner_e hσ M L e, inner_zero_right] at this
    simp only [Matrix.mulVec, dotProduct, GR_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  exact fun i ↦ congrFun (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) hG) i

end Basis

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

abbrev UU {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) :
    Submodule ℝ (EuclideanSpace ℝ (Idx S)) :=
  Submodule.span ℝ (Set.range fun i ↦ psi M (e i : S.V))

section U

variable (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L)

def bU : Basis ι ℝ (UU M L e) := Basis.span (psi_e_linInd S hσ hsig hpos M L e)

theorem bU_coe (i : ι) : ((bU S hσ hsig hpos M L e i : UU M L e) : EuclideanSpace ℝ (Idx S)) = psi M (e i : S.V) :=
  by simp [bU, Basis.span_apply]

abbrev abelian₂ : Submodule ℤ (UU M L e) := Submodule.span ℤ (Set.range (bU S hσ hsig hpos M L e))

theorem psi_eq_sum (l : S.V) (hl : l ∈ L) :
    psi M l = ∑ i, (e.repr ⟨l, hl⟩ i) • psi M (e i : S.V) := by
  have h := congrArg (fun t : L ↦ (t : S.V)) (e.sum_repr ⟨l, hl⟩)
  simp only [Submodule.coe_sum] at h
  have h' : ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = l :=
    calc ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = ∑ i, ((e.repr ⟨l, hl⟩ i • e i : L) : S.V) :=
          Finset.sum_congr rfl fun i _ ↦ by simp
      _ = l := h
  conv_lhs => rw [← h']
  exact psi_sum_int M L e _

theorem psi_mem_U (l : S.V) (hl : l ∈ L) : psi M l ∈ UU M L e := by
  rw [psi_eq_sum S M L e l hl]
  exact Submodule.sum_mem _ fun i _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

theorem mem_Lam_of (l : S.V) (hl : l ∈ L) :
    (⟨psi M l, psi_mem_U S M L e l hl⟩ : UU M L e) ∈ abelian₂ S hσ hsig hpos M L e := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i ↦ e.repr ⟨l, hl⟩ i, Subtype.ext ?_⟩
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]
  rw [psi_eq_sum S M L e l hl]

theorem exists_of_mem_Lam (u : UU M L e) (hu : u ∈ abelian₂ S hσ hsig hpos M L e) :
    ∃ l ∈ L, (u : EuclideanSpace ℝ (Idx S)) = psi M l := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hu
  refine ⟨∑ i, c i • (e i : S.V), Submodule.sum_mem _ fun i _ ↦ zsmul_mem (e i).2 _, ?_⟩
  rw [psi_sum_int M L e, ← hc]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]

theorem dual_vector_of_integral_pairing (y : UU M L e) (hy0 : y ≠ 0)
    (hy : ∀ x ∈ abelian₂ S hσ hsig hpos M L e, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) :
    ∃ z : S.V, TrDual S L z ∧ z ≠ 0 ∧ (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
  set b := bU S hσ hsig hpos M L e with hb
  have hbmem : ∀ j, b j ∈ abelian₂ S hσ hsig hpos M L e := fun j ↦ Submodule.subset_span ⟨j, rfl⟩
  choose n hn using fun j ↦ hy (b j) (hbmem j)
  set c : ι → ℝ := fun i ↦ b.repr y i with hc
  have hyc : (y : EuclideanSpace ℝ (Idx S)) = ∑ i, c i • psi M (e i : S.V) := by
    have := congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hb, bU_coe] at this
    rw [← this]
  have hGc : (GR S L e) *ᵥ c = fun j ↦ (n j : ℝ) := by
    ext j
    rw [← hn j]
    change _ = ⟪(b j : EuclideanSpace ℝ (Idx S)), (y : EuclideanSpace ℝ (Idx S))⟫_ℝ
    rw [hyc, inner_sum, hb, bU_coe]
    simp only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct, GR_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  set c' : ι → ℚ := (GQ S L e)⁻¹ *ᵥ fun j ↦ (n j : ℚ) with hc'
  have hdet := GQ_det S hσ hsig hpos M L e
  have hGc' : (GQ S L e) *ᵥ c' = fun j ↦ (n j : ℚ) := by
    rw [hc', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have hGR' : (GR S L e) *ᵥ (fun i ↦ (c' i : ℝ)) = fun j ↦ (n j : ℝ) := by
    ext j
    have := RingHom.map_mulVec (Rat.castHom ℝ) (GQ S L e) c' j
    rw [hGc'] at this
    simpa [GR, Function.comp_def] using this.symm
  have hcc : c = fun i ↦ (c' i : ℝ) := by
    have h0 : (GR S L e) *ᵥ (c - fun i ↦ (c' i : ℝ)) = 0 := by
      rw [Matrix.mulVec_sub, hGc, hGR', sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) h0)
  set z : S.V := ∑ i, (c' i : E) • (e i : S.V) with hz
  have hyz : (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
    rw [hyc, hz, psi_sum_rat M L e, hcc]
  refine ⟨z, ?_, ?_, hyz⟩
  · intro l hl
    obtain ⟨m, hm⟩ := hy _ (mem_Lam_of S hσ hsig hpos M L e l hl)
    have h1 : ⟪psi M l, psi M z⟫_ℝ = (m : ℝ) := by
      rw [← hyz]; exact hm
    rw [inner_psi hσ, trR_eq] at h1
    refine ⟨m, ?_⟩
    have : ((Algebra.trace ℚ E (S.hT l z) : ℚ) : ℝ) = ((m : ℚ) : ℝ) := by rw [h1]; simp
    rw [eq_intCast]
    exact_mod_cast this.symm
  · intro h0
    apply hy0
    apply Subtype.ext
    rw [hyz, h0, map_zero]
    rfl

end U

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem psi_mem_U_all (S : HSpace E) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) (hL : Submodule.IsLattice E L) (v : S.V) : psi M v ∈ UU M L e := by
  have key : ∀ v ∈ Submodule.span E (L : Set S.V), ∀ c : E, psi M (c • v) ∈ UU M L e := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        intro c
        have halg : IsAlgebraic ℤ c :=
          (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
        obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
        set w : 𝓞 E := ⟨y • c, hyi⟩ with hw
        have hwx : w • x ∈ L := L.smul_mem w hx
        have h1 := psi_mem_U S M L e _ hwx
        have hwE : (w : E) = (y : E) * c := by
          rw [hw]
          show y • c = (y : E) * c
          rw [zsmul_eq_mul]
        have h2 : c • x = (((1 / (y : ℚ)) : ℚ) : E) • ((w : E) • x) := by
          rw [smul_smul, hwE]
          congr 1
          have : (y : E) ≠ 0 := by exact_mod_cast hy0
          push_cast
          field_simp
        rw [h2, psi_rat, algebraMap_smul]
        exact Submodule.smul_mem _ _ h1
    | zero =>
        intro c
        rw [smul_zero, map_zero]
        exact zero_mem _
    | add x y _ _ hx hy =>
        intro c
        rw [smul_add, map_add]
        exact add_mem (hx c) (hy c)
    | smul a x _ hx =>
        intro c
        rw [smul_smul]
        exact hx (c * a)
  have := key v (by rw [hL.span_eq_top]; exact Submodule.mem_top) 1
  rwa [one_smul] at this

theorem span_E_of_real (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) (hL : Submodule.IsLattice E L) (R : ℝ)
    (hspan : Submodule.span ℝ {u : UU M L e | u ∈ abelian₂ S hσ hsig hpos M L e ∧ ‖u‖ ≤ R} = ⊤) :
    Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ R ^ 2} = ⊤ := by
  set P := Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ R ^ 2} with hPdef
  by_contra hP
  have hlt : finrank E P < finrank E S.V := Submodule.finrank_lt hP
  set p := Module.finBasis E P with hp
  set Φ : S.V →ₗ[E] (Fin (finrank E P) → E) := LinearMap.pi fun j ↦ S.hT (p j : S.V) with hΦ
  have hker : LinearMap.ker Φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_fin_fun]; exact hlt)
  obtain ⟨z, hzk, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzj : ∀ j, S.hT (p j : S.V) z = 0 := fun j ↦ congrFun (LinearMap.mem_ker.1 hzk) j
  have hPz : ∀ x ∈ P, S.hT x z = 0 := by
    intro x hx
    have hx' := congrArg (fun t : P ↦ (t : S.V)) (p.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    calc S.hT x z = S.hT (∑ j, (p.repr ⟨x, hx⟩ j) • (p j : S.V)) z := by rw [hx']
      _ = 0 := by
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [hT_smul_left, hzj, mul_zero]
  have hw : psi M z ∈ UU M L e := psi_mem_U_all S M L e hL z
  set w : UU M L e := ⟨psi M z, hw⟩ with hwdef
  have hsub : {u : UU M L e | u ∈ abelian₂ S hσ hsig hpos M L e ∧ ‖u‖ ≤ R} ⊆
      ((Submodule.span ℝ {w})ᗮ : Submodule ℝ (UU M L e)) := by
    rintro u ⟨hu, hnu⟩
    obtain ⟨l, hl, hul⟩ := exists_of_mem_Lam S hσ hsig hpos M L e u hu
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hlP : l ∈ P := by
      refine Submodule.subset_span ⟨hl, ?_⟩
      rw [← norm_psi_sq M l, ← hul]
      have : ‖(u : EuclideanSpace ℝ (Idx S))‖ = ‖u‖ := rfl
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hnu 2
    change ⟪(u : EuclideanSpace ℝ (Idx S)), psi M z⟫_ℝ = 0
    rw [hul, inner_psi hσ, hPz l hlP]
    simp [trR]
  have htop := Submodule.span_le.2 hsub
  rw [hspan] at htop
  have hww : w ∈ (Submodule.span ℝ {w})ᗮ := htop Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hww
  have hw0 : w = 0 := inner_self_eq_zero.1 hww
  have : psi M z = 0 := by
    have := congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) hw0
    simpa [hwdef] using this
  exact hz0 (eq_zero_of_psi S hσ hsig hpos M z this)

theorem span_trR_short (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (q : ℕ) (hq : q ≠ 0) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (hLT : LatT S q L) :
    ∃ r : ℕ, r ≤ 2 * finrank ℚ E * S.rank ∧
      Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ (3 * ((r : ℝ) / 2 /
        Real.sqrt ((finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))))
          + 1)) ^ 2} = ⊤ := by
  classical
  obtain ⟨M⟩ := model_exists S hσ hsig hpos
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.fg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : Module.IsTorsionFree ℤ L := Module.IsTorsionFree.of_smul_eq_zero fun n x h ↦ by
    have h' := congrArg (fun t : L ↦ (t : S.V)) h
    simp only [Submodule.coe_zero] at h'
    have h'' : (n : E) • (x : S.V) = 0 := by rw [Int.cast_smul_eq_zsmul]; simpa using h'
    rcases smul_eq_zero.1 h'' with h1 | h1
    · left; exact_mod_cast h1
    · right; exact Subtype.ext h1
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set e := Module.Free.chooseBasis ℤ L with he
  set lam := Real.sqrt ((finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))))
    with hlamdef
  have hX : (0 : ℝ) < (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have hdpos : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hd : ∀ y : UU M L e, y ≠ 0 → (∀ x ∈ abelian₂ S hσ hsig hpos M L e, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) →
      lam ≤ ‖y‖ := by
    intro y hy0 hy
    obtain ⟨z, hz, hz0, hyz⟩ := dual_vector_of_integral_pairing S hσ hsig hpos M L e y hy0 hy
    have h1 := trR_dual_ge S hσ hsig hpos q hq L hLT z hz hz0
    have h2 : ‖y‖ ^ 2 = trR (S.hT z z) := by
      rw [← norm_psi_sq M z, ← hyz]; rfl
    rw [← Real.sqrt_sq (norm_nonneg y), h2]
    exact Real.sqrt_le_sqrt h1
  have hsp := span_short_of_dual (abelian₂ S hσ hsig hpos M L e) lam hlam hd
  refine ⟨finrank ℝ (UU M L e), ?_, span_E_of_real S hσ hsig hpos M L e hL _ hsp⟩
  have h1 := Submodule.finrank_le (UU M L e)
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Embeddings.card] at h1
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
end
end

section
noncomputable section

open NumberField Module

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem shortSpan_mono (S : HSpace E) (q : ℕ) {ρ ρ' : ℝ} (h : ShortSpan S q ρ) (hle : ρ ≤ ρ') :
    ShortSpan S q ρ' := by
  intro L hL hq
  rw [eq_top_iff, ← h L hL hq]
  exact Submodule.span_mono fun x hx ↦ ⟨hx.1, hx.2.trans hle⟩

theorem shortSpan_of_pos (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (q : ℕ) (hq : q ≠ 0) :
    ShortSpan S q (18 * (S.rank : ℝ) ^ 2 *
      ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (1 / (finrank ℚ E : ℝ)) + 18) := by
  intro L hL hLT
  obtain ⟨r, hr, hspan⟩ := LT.span_trR_short S hσ hsig hpos q hq L hL hLT
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_mono fun x hx ↦ ⟨hx.1, ?_⟩
  set d : ℝ := (finrank ℚ E : ℝ) with hd
  set X : ℝ := (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 with hXdef
  have hX : 0 < X := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have hd1 : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set Y : ℝ := X ^ (1 / d) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hX _
  have hneg : X ^ (-(1 / d)) = Y⁻¹ := Real.rpow_neg hX.le _
  set lam := Real.sqrt (d * X ^ (-(1 / d))) with hlam
  have hlam2 : lam ^ 2 = d / Y := by
    rw [hlam, Real.sq_sqrt (by positivity), hneg, div_eq_mul_inv]
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hmean : meanAbs (S.hT x x) = LT.trR (S.hT x x) / d := by
    unfold meanAbs LT.trR
    rw [Complex.re_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ ↦ LT.norm_eq_re S hσ hsig hpos σ x
  rw [hmean, div_le_iff₀ (by linarith)]
  refine hx.2.trans ?_
  set t : ℝ := (r : ℝ) / 2 / lam with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t * lam = (r : ℝ) / 2 := by rw [ht]; field_simp
  have ht2 : t ^ 2 * (d / Y) = (r : ℝ) ^ 2 / 4 := by
    rw [← hlam2, ← mul_pow, htl]; ring
  have hr' : (r : ℝ) ≤ 2 * d * S.rank := by
    have := (Nat.cast_le (α := ℝ)).2 hr
    push_cast at this
    linarith
  have hr2 : (r : ℝ) ^ 2 ≤ 4 * d ^ 2 * (S.rank : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have ht2' : t ^ 2 ≤ d * (S.rank : ℝ) ^ 2 * Y := by
    have e1 : t ^ 2 = (r : ℝ) ^ 2 * Y / (4 * d) := by
      field_simp at ht2 ⊢
      linarith
    rw [e1, div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : (3 * (t + 1)) ^ 2 ≤ 18 * t ^ 2 + 18 := by nlinarith [sq_nonneg (t - 1)]
  have hn : (0 : ℝ) ≤ (S.rank : ℝ) ^ 2 * Y := by positivity
  calc (3 * ((r : ℝ) / 2 / lam + 1)) ^ 2 = (3 * (t + 1)) ^ 2 := rfl
    _ ≤ 18 * t ^ 2 + 18 := hsq
    _ ≤ 18 * (d * (S.rank : ℝ) ^ 2 * Y) + 18 := by linarith
    _ ≤ (18 * (S.rank : ℝ) ^ 2 * Y + 18) * d := by nlinarith

end Gen

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem disc_rpow (D : D7) :
    (((discr D.host.E).natAbs : ℝ) ^ 2) ^ (1 / (finrank ℚ D.host.E : ℝ)) = (2 * D.host.v) ^ 2 := by
  have h2v : 2 * D.host.v = D.host.rdE := by
    show 2 * (D.host.rdE / 2) = D.host.rdE
    ring
  rw [h2v]
  unfold Formalism.BasicNotions.Host.rdE
  have habs : |(discr D.host.E : ℝ)| = ((discr D.host.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem T_rpow (D : D7) (u : D.what₂.Word) :
    (((Tu D u ^ (2 * D.R.f) : ℕ) : ℝ)) ^ (1 / (finrank ℚ D.host.E : ℝ)) = (Tu D u : ℝ) := by
  rw [Formalism.MainNotions.flipTwoThree.b_finrank_host]
  push_cast
  have hf : (2 * D.R.f : ℕ) ≠ 0 := by
    have := one_le_f D
    omega
  have := Real.pow_rpow_inv_natCast (x := (Tu D u : ℝ)) (by positivity) hf
  rw [one_div]
  push_cast at this
  exact this

theorem rho_le (D : D7) (u : D.what₂.Word) (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ (Tu D u : ℝ)) :
    18 * (n : ℝ) ^ 2 * (q * (2 * D.host.v) ^ 2) + 18 ≤ msRho D u 90 n := by
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold msRho radiusSq
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hv2 : (1 : ℝ) ≤ D.host.v ^ 2 := one_le_pow₀ hv
  have hT2 : (Tu D u : ℝ) ≤ (Tu D u : ℝ) ^ 2 := by nlinarith
  have hA : 0 ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 := by positivity
  have h1 : 18 * (n : ℝ) ^ 2 * (q * (2 * D.host.v) ^ 2) ≤ 72 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 := by
    have : q ≤ (Tu D u : ℝ) ^ 2 := hq.trans hT2
    nlinarith
  have h2 : (18 : ℝ) ≤ 18 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 := one_le_mul_of_one_le_of_one_le hn2 hv2
    have : (1 : ℝ) ≤ (Tu D u : ℝ) ^ 2 := one_le_pow₀ hT
    nlinarith
  have h3 : 90 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 ≤ 90 * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 := by
    have : 0 ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 := by positivity
    nlinarith
  linarith

theorem shortFrame_record (D : D7) (u : D.what₂.Word) :
    (∀ i ≤ D.R.m, ShortFrame (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msRho D u 90 (D.R.N i))) ∧
    ShortFrame D.sp.X' 1 (msRho D u 90 (D.R.N D.R.m - 1)) := by
  have hT0 : Tu D u ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · refine shortFrame_of_span _ _ _ (shortSpan_mono _ _ (shortSpan_of_pos (D.sp.X i) (host_star D) (D.sp.X_sig i)
      (D7.X_posDef D i hi) (Tu D u ^ (2 * D.R.f)) (pow_ne_zero _ hT0)) ?_)
    have hn : 1 ≤ D.R.N i := by
      have := D.R.k_ge
      unfold Ranks.N
      omega
    rw [D.sp.X_rank i hi, Real.mul_rpow (by positivity) (by positivity), T_rpow, disc_rpow]
    exact rho_le D u _ hn _ (by positivity) le_rfl
  · refine shortFrame_of_span _ _ _ (shortSpan_mono _ _ (shortSpan_of_pos D.sp.X' (host_star D) D.sp.X'_sig
      (D7.X'_posDef D) 1 one_ne_zero) ?_)
    have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    have hn : 1 ≤ D.R.N D.R.m - 1 := by
      rw [hN]
      unfold Ranks.rankX' Ranks.r
      have := D.R.k_ge
      omega
    rw [D.sp.X'_rank, ← hN, Real.mul_rpow (by positivity) (by positivity), disc_rpow]
    simp only [Nat.cast_one, Real.one_rpow]
    exact rho_le D u _ hn 1 zero_le_one hT1

end Record

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
