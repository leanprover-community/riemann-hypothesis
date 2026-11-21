import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnDensNonneg
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnKappaBoundAbs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma




def cn_wt {a : ℕ} (j : Fin a → ℕ) (f : ℕ) (t : Fin a → ℝ) : ℝ := ∏ x, (2 * (f : ℝ) * j x / t x)

namespace CSize

variable {X : CData} (S : CSize X)

def Density : Prop :=
  ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq → ∀ Ψ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Ψ →
    ∫⁻ x in S.str J c, Ψ (S.tau J c x) ∂X.μ ≤
      ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) *
        ∫⁻ t in cn_Reg c.length, Ψ t * ENNReal.ofReal
          (cn_dens c.blocksFun (X.I.n - 2 * J) X.I.f t * cn_wt c.blocksFun X.I.f t)

def NearCount (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, ∀ T : Finset X.I.GFset,
      (∀ γ ∈ T, (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) →
      (T.card : ℝ) ≤ cn_cnt c.blocksFun (X.I.n - 2 * J) X.I.f δ (S.tau J c x)

end CSize

theorem cn_norm_φ_le (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (y : X.I.GA) :
    ‖X.φ y‖ ≤ fdegAll X.I X.σ X.w * (X.e 1).re := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  have he : ‖X.e y.2‖ ≤ (X.e 1).re := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y.2
  have hm : ∀ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ ≤ 1 := by
    intro v
    have hU : IsURepOn (UJset (X.I.ε v)) (X.σ v) := (hX.2.1.1 v).2.2.1
    have hw : ‖X.w v‖ = 1 := (hX.2.1.2.1 v).1
    unfold coefOn
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hU.2.1 _ (y.1 v).2, hw]
    norm_num
  unfold CData.φ phe phOf
  rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.fdegAll_nonneg]
  have h1 : ∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ ≤ 1 :=
    Finset.prod_le_one (fun v _ => norm_nonneg _) fun v _ => hm v
  have h2 := X.fdegAll_nonneg
  have h3 : 0 ≤ ∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖ := Finset.prod_nonneg fun v _ => norm_nonneg _
  calc fdegAll X.I X.σ X.w * (∏ v, ‖coefOn (X.σ v) (X.w v) (X.w v) (y.1 v)‖) * ‖X.e y.2‖
      ≤ fdegAll X.I X.σ X.w * 1 * (X.e 1).re := by gcongr
    _ = _ := by ring

open Classical in

theorem cn_nearS_le (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (εN : ℝ) (x : X.I.GA) (N : ℝ)
    (hN : ∀ T : Finset X.I.GFset,
      (∀ γ ∈ T, (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) → (T.card : ℝ) ≤ N) :
    X.nearS εN x ≤ ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) * ENNReal.ofReal N := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  unfold CData.nearS
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set T := s.filter (fun γ => (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hT
  have hterm : ∀ γ ∈ s, (if γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN then ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ else 0) ≤
      (if (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then
        ENNReal.ofReal k0 else 0) := by
    intro γ _
    by_cases hP : γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN
    · by_cases h0 : X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
      · simp [h0]
      · rw [if_pos hP, if_pos ⟨hP, h0⟩, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (cn_norm_φ_le X hX _)
    · rw [if_neg hP]
      exact zero_le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_right ?_ _
  have := hN T fun γ hγ => (Finset.mem_filter.1 hγ).2
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal this

end Formalism.MainNotions.LeviCoordinates

end
