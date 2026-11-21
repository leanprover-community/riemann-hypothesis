import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
import GroundTheory.GlobalFields.ComplexMultiplication.VariableChangePoints
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint

variable {F : Type*} [Field F]

structure IsShortForm (W : WeierstrassCurve F) : Prop where
  a₁_eq : W.a₁ = 0
  a₂_eq : W.a₂ = 0
  a₃_eq : W.a₃ = 0

namespace ShortWeierstrass

def g₂ (W : WeierstrassCurve F) : F := -4 * W.a₄

def g₃ (W : WeierstrassCurve F) : F := -4 * W.a₆

end ShortWeierstrass

open ShortWeierstrass

theorem IsShortForm.Δ_eq {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]
  ring

theorem IsShortForm.Δ_eq_g {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = g₂ W ^ 3 - 27 * g₃ W ^ 2 := by
  rw [hW.Δ_eq, g₂, g₃]
  ring

theorem IsShortForm.a₄_ne_zero_or_a₆_ne_zero {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  have := W.isUnit_Δ.ne_zero
  rw [hW.Δ_eq, h.1, h.2] at this
  simp at this

open scoped Classical in

noncomputable def weberValue (W : WeierstrassCurve F) (x : F) : F :=
  if W.a₆ = 0 then g₂ W ^ 2 / W.Δ * x ^ 2
  else if W.a₄ = 0 then g₃ W / W.Δ * x ^ 3
  else g₂ W * g₃ W / W.Δ * x

noncomputable def weberFunction (W : WeierstrassCurve F) : W.toAffine.Point → OnePoint F
  | .zero => ∞
  | .some x _ _ => OnePoint.some (weberValue W x)

@[simp]
theorem weberFunction_zero (W : WeierstrassCurve F) : weberFunction W .zero = ∞ := rfl

@[simp]
theorem weberFunction_some (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    weberFunction W (.some x y h) = OnePoint.some (weberValue W x) := rfl

theorem weberValue_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by
  simp [weberValue, hb]

theorem weberValue_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by
  simp [weberValue, ha, hb]

theorem weberValue_of_ne_zero {W : WeierstrassCurve F} (ha : W.a₄ ≠ 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₂ W * g₃ W / W.Δ * x := by
  simp [weberValue, ha, hb]

section Isomorphism

variable [CharZero F]

theorem variableChange_rst_eq_zero {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have h1 := hCW.a₁_eq
  have h2 := hCW.a₂_eq
  have h3 := hCW.a₃_eq
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁_eq, hW.a₂_eq,
    hW.a₃_eq] at h1 h2 h3
  have hs : C.s = 0 := by simpa [hv] using h1
  have ht : C.t = 0 := by simpa [hv] using h3
  have hr : C.r = 0 := by simpa [hv, hs] using h2
  exact ⟨hr, hs, ht⟩

theorem variableChange_a₄_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₄, hr, hs, ht]

theorem variableChange_a₆_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₆, hr, ht]

theorem weberFunction_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    [W.IsElliptic] (hC : C • W = W') (hW : IsShortForm W) (hW' : IsShortForm W')
    (P : W.toAffine.Point) :
    weberFunction W' (variableChangePoint C hC P) = weberFunction W P := by
  subst hC
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hW'
  cases P with
  | zero => rfl
  | some x y h =>
    rw [variableChangePoint_some, weberFunction_some, weberFunction_some]
    congr 1
    have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have ha := variableChange_a₄_of_isShortForm hW hW'
    have hb := variableChange_a₆_of_isShortForm hW hW'
    have hb0 : (C • W).a₆ = 0 ↔ W.a₆ = 0 := by rw [hb]; simp
    have ha0 : (C • W).a₄ = 0 ↔ W.a₄ = 0 := by rw [ha]; simp
    by_cases h6 : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (hb0.mpr h6), weberValue_of_a₆_eq_zero h6]
      simp only [g₂, ha, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    by_cases h4 : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (ha0.mpr h4) (mt hb0.mp h6), weberValue_of_a₄_eq_zero h4 h6]
      simp only [g₃, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    · rw [weberValue_of_ne_zero (mt ha0.mp h4) (mt hb0.mp h6), weberValue_of_ne_zero h4 h6]
      simp only [g₂, g₃, ha, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp

end Isomorphism

section FieldOfDefinition

variable {L : Type*} [Field L]

def pointMapOfRingHom (φ : F →+* L) {W : WeierstrassCurve F} :
    W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((W.toAffine.map_nonsingular φ.injective x y).mpr h)

theorem weberFunction_pointMapOfRingHom (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    have h4 : (W.map φ).a₄ = φ W.a₄ := rfl
    have h6 : (W.map φ).a₆ = φ W.a₆ := rfl
    show OnePoint.some _ = OnePoint.some _
    congr 1
    by_cases hb : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (by rw [h6, hb, map_zero]), weberValue_of_a₆_eq_zero hb]
      simp [g₂, map_Δ, map_ofNat]
    have hb' : (W.map φ).a₆ ≠ 0 := by rw [h6]; exact (map_ne_zero φ).mpr hb
    by_cases ha : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (by rw [h4, ha, map_zero]) hb', weberValue_of_a₄_eq_zero ha hb]
      simp [g₃, map_Δ, map_ofNat]
    · have ha' : (W.map φ).a₄ ≠ 0 := by rw [h4]; exact (map_ne_zero φ).mpr ha
      rw [weberValue_of_ne_zero ha' hb', weberValue_of_ne_zero ha hb]
      simp [g₂, g₃, map_Δ, map_ofNat]

end FieldOfDefinition

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint ShortWeierstrass

variable {F : Type*} [Field F]

open scoped Classical in

noncomputable def automorphismOrder (W : WeierstrassCurve F) : ℕ :=
  if W.a₆ = 0 then 4 else if W.a₄ = 0 then 6 else 2

theorem automorphismOrder_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) : automorphismOrder W = 4 := by
  simp [automorphismOrder, hb]

theorem automorphismOrder_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0) :
    automorphismOrder W = 6 := by
  simp [automorphismOrder, ha, hb]

def automorphismScale (W : WeierstrassCurve F) :
    MulAction.stabilizer (VariableChange F) W →* Fˣ where
  toFun ξ := ξ.1.u
  map_one' := rfl
  map_mul' _ _ := rfl

def automorphismPoint {W : WeierstrassCurve F} (ξ : MulAction.stabilizer (VariableChange F) W) :
    W.toAffine.Point → W.toAffine.Point :=
  variableChangePoint ξ.1 (MulAction.mem_stabilizer_iff.mp ξ.2)

section CharZero

variable [CharZero F] {W : WeierstrassCurve F}

theorem automorphism_rst_eq_zero (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) : ξ.1.r = 0 ∧ ξ.1.s = 0 ∧ ξ.1.t = 0 :=
  variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)

theorem automorphismScale_injective (hW : IsShortForm W) :
    Function.Injective (automorphismScale W) := by
  intro ξ η h
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  obtain ⟨hr', hs', ht'⟩ := automorphism_rst_eq_zero hW η
  apply Subtype.ext
  exact VariableChange.ext h (hr.trans hr'.symm) (hs.trans hs'.symm) (ht.trans ht'.symm)

theorem mem_range_automorphismScale (hW : IsShortForm W) (u : Fˣ) :
    u ∈ (automorphismScale W).range ↔
      (↑u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ ∧ (↑u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    have hξ : ξ.1 • W = W := MulAction.mem_stabilizer_iff.mp ξ.2
    have hCW : IsShortForm (ξ.1 • W) := hξ.symm ▸ hW
    have h4 := variableChange_a₄_of_isShortForm hW hCW
    have h6 := variableChange_a₆_of_isShortForm hW hCW
    rw [hξ] at h4 h6
    exact ⟨h4.symm, h6.symm⟩
  · rintro ⟨h4, h6⟩
    have hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
      ext
      · simp [variableChange_a₁, hW.a₁_eq]
      · simp [variableChange_a₂, hW.a₂_eq, hW.a₁_eq]
      · simp [variableChange_a₃, hW.a₃_eq, hW.a₁_eq]
      · simpa [variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h4
      · simpa [variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h6
    exact ⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩

variable [W.IsElliptic]

omit [CharZero F] in

theorem scale_conditions_iff (hW : IsShortForm W) (w : F) :
    (w⁻¹ ^ 4 * W.a₄ = W.a₄ ∧ w⁻¹ ^ 6 * W.a₆ = W.a₆) ↔ w ^ automorphismOrder W = 1 := by
  have key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1) := by
    intro k c hc
    rw [inv_pow]
    constructor
    · intro h
      exact inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))
    · intro h
      rw [h, inv_one, one_mul]
  unfold automorphismOrder
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    simp only [h6, mul_zero, and_true, if_true]
    exact key 4 _ h4
  by_cases h4 : W.a₄ = 0
  · simp only [h4, h6, mul_zero, true_and, if_false, if_true]
    exact key 6 _ h6
  · simp only [h4, h6, if_false, key 4 _ h4, key 6 _ h6]
    constructor
    · rintro ⟨a, b⟩
      have : w ^ 6 = w ^ 4 * w ^ 2 := by ring
      rw [this, a, one_mul] at b
      exact b
    · intro h
      refine ⟨?_, ?_⟩
      · rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]
      · rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]

theorem range_automorphismScale (hW : IsShortForm W) :
    (automorphismScale W).range = rootsOfUnity (automorphismOrder W) F := by
  ext u
  rw [mem_range_automorphismScale hW, mem_rootsOfUnity', Units.val_inv_eq_inv_val]
  exact scale_conditions_iff hW _

noncomputable def automorphismEquivRootsOfUnity (hW : IsShortForm W) :
    MulAction.stabilizer (VariableChange F) W ≃* rootsOfUnity (automorphismOrder W) F :=
  (MonoidHom.ofInjective (automorphismScale_injective hW)).trans
    (MulEquiv.subgroupCongr (range_automorphismScale hW))

@[simp]
theorem automorphismEquivRootsOfUnity_apply (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) :
    ((automorphismEquivRootsOfUnity hW ξ : Fˣ)) = ξ.1.u := rfl

theorem weberFunction_automorphismPoint (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) (P : W.toAffine.Point) :
    weberFunction W (automorphismPoint ξ P) = weberFunction W P :=
  weberFunction_variableChangePoint ξ.1 _ hW hW P

end CharZero

section Fibres

variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]

omit [CharZero F] [W.IsElliptic] in

theorem IsShortForm.sq_eq (hW : IsShortForm W) {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have := h.1
  rw [Affine.equation_iff] at this
  simpa [hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using this

theorem exists_scale_of_weberValue_eq [IsAlgClosed F] (hW : IsShortForm W) {x₁ x₂ : F}
    (hx : weberValue W x₁ = weberValue W x₂) :
    ∃ v : F, v ≠ 0 ∧ v ^ 4 * W.a₄ = W.a₄ ∧ v ^ 6 * W.a₆ = W.a₆ ∧ v ^ 2 * x₁ = x₂ := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    rw [weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6] at hx
    have hc : g₂ W ^ 2 / W.Δ ≠ 0 := by simp [g₂, h4, hΔ]
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hc hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : F)
      have hi4 : i ^ 4 = 1 := by linear_combination (1 - i * i) * hi
      refine ⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩
      · rintro rfl
        simp at hi
      · linear_combination (-x₁) * hi - h
  by_cases h4 : W.a₄ = 0
  · rw [weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6] at hx
    have hc : g₃ W / W.Δ ≠ 0 := by simp [g₃, h6, hΔ]
    have hcube : x₁ ^ 3 = x₂ ^ 3 := mul_left_cancel₀ hc hx
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ = 0 := by
        rw [hx1, zero_pow (by norm_num)] at hcube
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm
      exact ⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩
    · obtain ⟨w, hw⟩ : ∃ w, w = x₂ / x₁ := ⟨_, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        rw [hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw3
      refine ⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩
      · rw [show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]
      · rw [show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]
  · rw [weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6] at hx
    have hc : g₂ W * g₃ W / W.Δ ≠ 0 := by simp [g₂, g₃, h4, h6, hΔ]
    have h : x₁ = x₂ := mul_left_cancel₀ hc hx
    exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩

omit [W.IsElliptic] in

theorem exists_automorphismPoint_of_scale (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  obtain ⟨ξ, hξ⟩ := (mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr
    ⟨by simpa using h4, by simpa using h6⟩
  refine ⟨ξ, ?_⟩
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  have hu : (↑ξ.1.u⁻¹ : F) = v := by
    have : ξ.1.u = (Units.mk0 v hv)⁻¹ := hξ
    rw [this, inv_inv, Units.val_mk0]
  simp only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul,
    Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

theorem weberFunction_eq_iff [IsAlgClosed F] (hW : IsShortForm W) (P Q : W.toAffine.Point) :
    weberFunction W P = weberFunction W Q ↔
      ∃ ξ : MulAction.stabilizer (VariableChange F) W, automorphismPoint ξ P = Q := by
  constructor
  · intro hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => exact ⟨1, rfl⟩
      | some x y h => simp at hPQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp at hPQ
      | some x₂ y₂ h₂ =>
        simp only [weberFunction_some] at hPQ
        have hx : weberValue W x₁ = weberValue W x₂ := Option.some_injective _ hPQ
        obtain ⟨v, hv, h4, h6, hx2⟩ := exists_scale_of_weberValue_eq hW hx
        have hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2 := by
          rw [hW.sq_eq h₂, ← hx2]
          linear_combination (-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
        · exact exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂
        · refine exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_
            h₁ h₂
          · rw [show (-v) ^ 4 = v ^ 4 by ring, h4]
          · rw [show (-v) ^ 6 = v ^ 6 by ring, h6]
          · rw [show (-v) ^ 2 = v ^ 2 by ring, hx2]
          · rw [hy]
            ring
  · rintro ⟨ξ, rfl⟩
    exact (weberFunction_automorphismPoint hW ξ P).symm

end Fibres

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
  GroundTheory.Arith.Abelian

universe u

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem exists_coeffs_of_degree_eq_one_of_isAlgClosed (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α β γ δ ε : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A +
        algebraMap F A.toAffine.FunctionField β ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A +
        algebraMap F A.toAffine.FunctionField δ * genX A +
        algebraMap F A.toAffine.FunctionField ε ∧
      γ ^ 2 = α ^ 3 ∧
      γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2 = 0 ∧
      γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
        2 * B.a₂ * α * β - B.a₄ * α = 0 ∧
      γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β -
        B.a₆ = 0 ∧
      2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁ = 0 ∧
      2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃ = 0 := by
  have hmul := ψ.ramIdx_mul_card_ker
  rw [h] at hmul
  have hram : ψ.ramIdx = 1 := (mul_eq_one.mp hmul).1
  have hbot : ψ.pointHom.ker = ⊥ := AddSubgroup.card_eq_one.mp (mul_eq_one.mp hmul).2
  have hne : ∀ R : A.toAffine.Point, R ≠ 0 → ψ.pointMap R ≠ 0 := by
    intro R hR h0
    have hR' : R ∈ ψ.pointHom.ker := by
      rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]; exact h0
    rw [hbot, AddSubgroup.mem_bot] at hR'
    exact hR hR'
  have hval : ∀ (R : A.toAffine.Point) (f : B.toAffine.FunctionField),
      valuationPoint A R (ψ.comap f) = valuationPoint B (ψ.pointMap R) f := by
    intro R f
    rw [ψ.valuationPoint_comap, hram, pow_one]
  have h0 : ψ.pointMap 0 = 0 := map_zero ψ.pointHom
  have hinf : ∀ f : B.toAffine.FunctionField, valuationInfty A (ψ.comap f) = valuationInfty B f := by
    intro f
    rw [← valuationPoint_zero_eq, hval, h0, valuationPoint_zero_eq]
  obtain ⟨α, β, hα, hf⟩ := exists_eq_linear_of_valuation (W := A) (f := ψ.comap (genX B))
    (fun R hR => by rw [hval]; exact valuationPoint_genX_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genX B])
  obtain ⟨γ, δ, ε, hγ, hg⟩ := exists_eq_genY_form_of_valuation (W := A) (g := ψ.comap (genY B))
    (fun R hR => by rw [hval]; exact valuationPoint_genY_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genY B])
  set ι := algebraMap F A.toAffine.FunctionField with hι
  have hx : ψ.x = ι α * genX A + ι β := by rw [← ψ.comap_genX]; exact hf
  have hy : ψ.y = ι γ * genY A + ι δ * genX A + ι ε := by rw [← ψ.comap_genY]; exact hg
  have hN := ψ.nonsingular
  have eB := (equation_iff _ _).mp hN.1
  rw [hx, hy] at eB
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eB
  have eA := genY_sq_add A
  set P : F[X] := C (γ ^ 2 - α ^ 3) * X ^ 3 +
    C (γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2) * X ^ 2 +
    C (γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
      2 * B.a₂ * α * β - B.a₄ * α) * X +
    C (γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β - B.a₆)
    with hP
  set Q : F[X] := C (2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁) * X +
    C (2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃) with hQ
  have key : algebraMap F[X] A.toAffine.FunctionField P +
      algebraMap F[X] A.toAffine.FunctionField Q * genY A = 0 := by
    simp only [hP, hQ, map_add, map_mul, map_pow, algebraMap_C_functionField, ← genX_eq, map_sub,
      map_ofNat]
    linear_combination eB - ι γ ^ 2 * eA
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_algebraMap_add_mul_genY A key
  have c3 := congrArg (Polynomial.coeff · 3) hP0
  have c2 := congrArg (Polynomial.coeff · 2) hP0
  have c1 := congrArg (Polynomial.coeff · 1) hP0
  have c0 := congrArg (Polynomial.coeff · 0) hP0
  have d1 := congrArg (Polynomial.coeff · 1) hQ0
  have d0 := congrArg (Polynomial.coeff · 0) hQ0
  simp only [hP, hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c3 c2 c1 c0 d1 d0
  norm_num at c3 c2 c1 c0 d1 d0
  refine ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, by linear_combination c3, by linear_combination c2,
    by linear_combination c1, by linear_combination c0, by linear_combination d1,
    by linear_combination d0⟩

theorem exists_scale_of_degree_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α γ : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A ∧
      γ ^ 2 = α ^ 3 ∧ γ ^ 2 * A.a₄ = B.a₄ * α ∧ γ ^ 2 * A.a₆ = B.a₆ := by
  obtain ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, c3, c2, c1, c0, d1, d0⟩ :=
    exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h
  rw [hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, hB.a₁_eq, hB.a₂_eq, hB.a₃_eq] at *
  have hδ : δ = 0 := by
    have : (2 * γ) * δ = 0 := by linear_combination d1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  have hε : ε = 0 := by
    have : (2 * γ) * ε = 0 := by linear_combination d0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  subst hδ hε
  have hβ : β = 0 := by
    have : (3 * α ^ 2) * β = 0 := by linear_combination -c2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h3 (pow_ne_zero 2 hα))
  subst hβ
  refine ⟨α, γ, hα, hγ, by simpa using hx, by simpa using hy, c3, by linear_combination c1,
    by linear_combination c0⟩

end AlgClosed

section General

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]

omit [A.IsElliptic] in
theorem IsShortForm.baseChange {W : WeierstrassCurve F} (hW : IsShortForm W) (L : Type*) [Field L]
    [Algebra F L] : IsShortForm (W.baseChange L) :=
  ⟨by simp [WeierstrassCurve.baseChange, hW.a₁_eq], by simp [WeierstrassCurve.baseChange, hW.a₂_eq],
    by simp [WeierstrassCurve.baseChange, hW.a₃_eq]⟩

theorem exists_scale_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hA : IsShortForm A)
    (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A ∧
      B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ := by
  classical
  let Ω := AlgebraicClosure F
  have hd : (isogBaseChange (F' := Ω) ψ).degree = 1 := by rw [degree_isogBaseChange, h]
  have inj := (algebraMap F Ω).injective
  have h2' : (2 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h2
    rwa [map_ofNat] at this
  have h3' : (3 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h3
    rwa [map_ofNat] at this
  obtain ⟨α, γ, hα, hγ, hx, hy, hc, h4, h6⟩ := exists_scale_of_degree_eq_one_of_isAlgClosed h2' h3'
    (hA.baseChange Ω) (hB.baseChange Ω) _ hd
  rw [isogBaseChange_alt, ← bcEmb_genX] at hx
  rw [isogBaseChange_y, ← bcEmb_genY] at hy
  have hX0 : genX A ≠ 0 := fun h => transcendental_genX A (h ▸ isAlgebraic_zero)
  have hY0 : genY A ≠ 0 := genY_ne_zero A
  set K' := (A.baseChange Ω).toAffine.FunctionField
  have hXb : bcEmb (F' := Ω) A (genX A) ≠ 0 := (_root_.map_ne_zero _).mpr hX0
  have hYb : bcEmb (F' := Ω) A (genY A) ≠ 0 := (_root_.map_ne_zero _).mpr hY0
  have ex : bcEmb (F' := Ω) A (ψ.x / genX A) = algebraMap Ω K' α := by
    rw [map_div₀, hx, mul_div_cancel_right₀ _ hXb]
  have ey : bcEmb (F' := Ω) A (ψ.y / genY A) = algebraMap Ω K' γ := by
    rw [map_div₀, hy, mul_div_cancel_right₀ _ hYb]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_bcEmb A ex
  obtain ⟨c, hc'⟩ := exists_algebraMap_eq_of_bcEmb A ey
  have key : ∀ (b : F) (f : A.toAffine.FunctionField) (β : Ω),
      algebraMap F A.toAffine.FunctionField b = f → bcEmb (F' := Ω) A f = algebraMap Ω K' β →
        algebraMap F Ω b = β := by
    intro b f β hb hf
    apply (algebraMap Ω K').injective
    rw [← hf, ← hb, AlgHom.commutes, IsScalarTower.algebraMap_apply F Ω K']
  have haα := key a _ α ha ex
  have hcγ := key c _ γ hc' ey
  have ha0 : a ≠ 0 := by rintro rfl; exact hα (by rw [← haα, map_zero])
  have hc0 : c ≠ 0 := by rintro rfl; exact hγ (by rw [← hcγ, map_zero])
  have hca : c ^ 2 = a ^ 3 := inj (by rw [map_pow, map_pow, haα, hcγ, hc])
  have h4' : c ^ 2 * A.a₄ = B.a₄ * a := inj (by
    rw [map_mul, map_mul, map_pow, haα, hcγ]; exact h4)
  have h6' : c ^ 2 * A.a₆ = B.a₆ := inj (by
    rw [map_mul, map_pow, hcγ]; exact h6)
  let v : Fˣ := Units.mk0 (c / a) (div_ne_zero hc0 ha0)
  have hv2 : (v : F) ^ 2 = a := by
    show (c / a) ^ 2 = a
    field_simp
    linear_combination hca
  have hv3 : (v : F) ^ 3 = c := by
    show (c / a) ^ 3 = c
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
    rw [div_pow, ← hca, div_eq_iff hc2]
    ring
  have hv0 : (v : F) ^ 2 ≠ 0 := pow_ne_zero 2 v.ne_zero
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv2, ha, div_mul_cancel₀ _ hX0]
  · rw [hv3, hc', div_mul_cancel₀ _ hY0]
  · apply mul_right_cancel₀ hv0
    rw [hv2, ← h4', ← hv3, ← hv2]
    ring
  · rw [← h6', ← hv3]
    ring

end General

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

theorem pow_eq_one_of_scale {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic]
    (hE : IsShortForm E) {u : F} (h4 : E.a₄ = u ^ 4 * E.a₄) (h6 : E.a₆ = u ^ 6 * E.a₆) :
    u ^ automorphismOrder E = 1 ∧ u ^ 12 = 1 := by
  by_cases hu : u = 0
  · subst hu
    rcases hE.a₄_ne_zero_or_a₆_ne_zero with h | h
    · exact absurd (by simpa using h4) h
    · exact absurd (by simpa using h6) h
  have hn : u ^ automorphismOrder E = 1 := by
    have := (scale_conditions_iff hE u⁻¹).mp ⟨by rw [inv_inv]; exact h4.symm,
      by rw [inv_inv]; exact h6.symm⟩
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨hn, ?_⟩
  unfold automorphismOrder at hn
  split_ifs at hn
  · rw [show 12 = 4 * 3 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 6 * 2 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 2 * 6 by rfl, pow_mul, hn, one_pow]

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

omit [IsAlgClosed F] [A.IsElliptic] [B.IsElliptic] in

theorem vcPoint_constPoint (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    vcPoint (C.baseChange A.toAffine.FunctionField) (Elliptic.baseChange_smul_eq C _ hC)
        (constPoint A R) = constMap B A.toAffine.FunctionField (vcPoint C hC R) := by
  cases R with
  | zero => rfl
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some A h
    rw [e, vcPoint_some, vcPoint_some]
    show Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact ⟨(map_vcX C (algebraMap F _) x).symm, (map_vcY C (algebraMap F _) x y).symm⟩

theorem pointMap_eq_vcPoint (C : VariableChange F) (hC : C • A = B) (ψ : Isogeny A B)
    (hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A)) (R : A.toAffine.Point) :
    ψ.pointMap R = vcPoint C hC R := by
  apply Isogeny.pointMap_eq_of_map_translate
  rw [hψ, Elliptic.map_vcPoint C (translate A R) hC, map_translate_genericPoint, vcPoint_add,
    vcPoint_constPoint]

theorem pointMap_some_of_scale (hA : IsShortForm A) (hB : IsShortForm B) (u : Fˣ)
    (h4 : B.a₄ = (u : F) ^ 4 * A.a₄) (h6 : B.a₆ = (u : F) ^ 6 * A.a₆) (ψ : Isogeny A B)
    (hx : ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A)
    (hy : ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A)
    {x y : F} (h : A.toAffine.Nonsingular x y) :
    ∃ h' : B.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y),
      ψ.pointMap (.some x y h) = .some _ _ h' := by
  let C : VariableChange F := ⟨u⁻¹, 0, 0, 0⟩
  have hC : C • A = B := by
    ext
    · simp [C, variableChange_a₁, hA.a₁_eq, hB.a₁_eq]
    · simp [C, variableChange_a₂, hA.a₁_eq, hA.a₂_eq, hB.a₂_eq]
    · simp [C, variableChange_a₃, hA.a₁_eq, hA.a₃_eq, hB.a₃_eq]
    · simp [C, variableChange_a₄, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h4]
    · simp [C, variableChange_a₆, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h6]
  have hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A) := by
    rw [ψ.val_eq_some_x_y]
    simp only [GroundTheory.Arith.Abelian.genericPoint, vcPoint_some, Point.some.injEq]
    constructor
    · rw [hx]
      simp [C, vcX, VariableChange.baseChange, VariableChange.map]
    · rw [hy]
      simp [C, vcY, VariableChange.baseChange, VariableChange.map]
  have ex : vcX C x = (u : F) ^ 2 * x := by simp [C, vcX]
  have ey : vcY C x y = (u : F) ^ 3 * y := by simp [C, vcY]
  have hN : B.toAffine.Nonsingular (vcX C x) (vcY C x y) := hC ▸ (nonsingular_vc C A x y).2 h
  rw [ex, ey] at hN
  refine ⟨hN, ?_⟩
  rw [pointMap_eq_vcPoint C hC ψ hψ, vcPoint_some, Point.some.injEq]
  exact ⟨ex, ey⟩

end AlgClosed

section BaseChange

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [DecidableEq Ω]

theorem pointMap_isogBaseChange_some_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ ∧
      ∀ (x y : Ω) (hxy : (A.baseChange Ω).toAffine.Nonsingular x y),
        ∃ h' : (B.baseChange Ω).toAffine.Nonsingular
            (algebraMap F Ω (u : F) ^ 2 * x) (algebraMap F Ω (u : F) ^ 3 * y),
          (isogBaseChange (F' := Ω) ψ).pointMap (.some x y hxy) = .some _ _ h' := by
  obtain ⟨u, hx, hy, h4, h6⟩ := exists_scale_of_degree_eq_one h2 h3 hA hB ψ h
  refine ⟨u, h4, h6, fun x y hxy => ?_⟩
  let v : Ωˣ := Units.map (algebraMap F Ω) u
  have hv : (v : Ω) = algebraMap F Ω (u : F) := rfl
  have h4' : (B.baseChange Ω).a₄ = (v : Ω) ^ 4 * (A.baseChange Ω).a₄ := by
    show algebraMap F Ω B.a₄ = _ * algebraMap F Ω A.a₄
    rw [h4, hv, map_mul, map_pow]
  have h6' : (B.baseChange Ω).a₆ = (v : Ω) ^ 6 * (A.baseChange Ω).a₆ := by
    show algebraMap F Ω B.a₆ = _ * algebraMap F Ω A.a₆
    rw [h6, hv, map_mul, map_pow]
  have hx' : (isogBaseChange (F' := Ω) ψ).x =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 2) *
        genX (A.baseChange Ω) := by
    rw [isogBaseChange_alt, hx, map_mul, AlgHom.commutes, bcEmb_genX, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hy' : (isogBaseChange (F' := Ω) ψ).y =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 3) *
        genY (A.baseChange Ω) := by
    rw [isogBaseChange_y, hy, map_mul, AlgHom.commutes, bcEmb_genY, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  exact pointMap_some_of_scale (hA.baseChange Ω) (hB.baseChange Ω) v h4' h6' _ hx' hy' hxy

end BaseChange

end GroundTheory.Global
end
