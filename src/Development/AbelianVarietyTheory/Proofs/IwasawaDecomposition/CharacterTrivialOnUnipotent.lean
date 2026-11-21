import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecomposition

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_herm_mulVec_self_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ →
    κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  intro E _ _ _ N G κ _ hdet hκ hκ0 n _ hn
  by_contra hcon
  push_neg at hcon
  have pol : ∀ x y, herm G (n.mulVec x) y + herm G (n.mulVec y) x = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [Matrix.mulVec_add, herm_add_left, herm_add_right, herm_add_right, hcon x, hcon y] at h
    linear_combination h
  have key : ∀ x y, herm G (n.mulVec x) y = 0 := by
    intro x y
    have h1 := pol (κ • x) y
    rw [Matrix.mulVec_smul, herm_smul_left, herm_smul_right, hκ] at h1
    have h2 := pol x y
    have h3 : (2 * κ) * herm G (n.mulVec x) y = 0 := by linear_combination h1 + κ * h2
    have h4 : (2 * κ : E) ≠ 0 := mul_ne_zero two_ne_zero hκ0
    exact (mul_eq_zero.1 h3).resolve_left h4
  apply hn
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [Matrix.zero_mulVec]
  exact eq_zero_of_herm G hdet _ (key x)

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_herm_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  atlas_forward_decl GlobalTheory.UnipKill.exists_herm_mulVec_self_ne_zero
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem skew_eq_sum_rk1_of_finrank (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E) (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0)
    (hκ : cc κ = -κ) (hκ0 : κ ≠ 0) :
    ∀ r, ∀ (W : Submodule E (Fin N → E)), Module.finrank E W = r →
      (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n →
      (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E),
        (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro W hr hW n hn hnW
  by_cases h0 : n = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp [h0]⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_nonzero_herm_of_skew E N G κ hG hdet hκ hκ0 n hn h0
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = n.mulVec x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = herm G ξ x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := by rw [hβ, hξ]; exact hx
  have hβcc : cc β = -β := by
    rw [hβ, cc_herm G hG, hξ]
    have := hn x x
    linear_combination this
  obtain ⟨c, hc⟩ : ∃ c : E, c = -β⁻¹ := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : E, t0 = -(κ * β)⁻¹ := ⟨_, rfl⟩
  have hct : c = t0 * κ := by rw [hc, ht0]; field_simp
  have ht0cc : cc t0 = t0 := by rw [ht0, cc_neg, cc_inv, cc_mul, hκ, hβcc, neg_mul_neg]
  have hcc : cc c = -c := by rw [hc, cc_neg, cc_inv, hβcc, inv_neg]
  have hcβ : c * β = -1 := by rw [hc]; field_simp
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = n - c • rk1 G ξ ξ := ⟨_, rfl⟩
  have h1 : ∀ y, n1.mulVec y = n.mulVec y - (c * herm G y ξ) • ξ := by
    intro y
    rw [hn1, Matrix.sub_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]
  have hsk : IsSkew G n1 := by
    intro y z
    rw [h1 y, h1 z, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hn y z, cc_mul,
      hcc, cc_herm G hG]
    ring
  let f : (Fin N → E) →ₗ[E] E :=
    { toFun := fun v => herm G v x
      map_add' := fun a b => herm_add_left G a b x
      map_smul' := fun a v => by simp only [herm_smul_left, RingHom.id_apply, smul_eq_mul] }
  let W' : Submodule E (Fin N → E) := W ⊓ LinearMap.ker f
  have hξW : ξ ∈ W := hξ ▸ hnW x
  have hn1W : ∀ y, n1.mulVec y ∈ W' := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [h1]; exact W.sub_mem (hnW y) (W.smul_mem _ hξW)
    · show herm G (n1.mulVec y) x = 0
      rw [h1, herm_sub_left, herm_smul_left, ← hβ]
      have := hn y x
      rw [← hξ] at this
      linear_combination this - herm G y ξ * hcβ
  have hlt : W' < W := by
    refine SetLike.lt_iff_le_and_exists.2 ⟨inf_le_left, ξ, hξW, fun h => hβ0 ?_⟩
    have : herm G ξ x = 0 := h.2
    rw [hβ, this]
  have hrk : Module.finrank E W' < r := hr ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨d, ξ', t', hmem, hreal, heq⟩ := ih _ hrk W' rfl
    (fun u hu v hv => hW u hu.1 v hv.1) n1 hsk hn1W
  refine ⟨d + 1, Fin.cons ξ ξ', Fin.cons t0 t', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hξW
    · simpa using (hmem j).1
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using ht0cc
    · simpa using hreal j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← heq, ← hct, hn1]
    abel

theorem skew_eq_sum_rk1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) →
    ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) →
    ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧
      n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  intro E _ _ _ N G κ hG hdet hκ hκ0 W hW n hn hnW
  exact skew_eq_sum_rk1_of_finrank E N G κ hG hdet hκ hκ0 _ W rfl hW n hn hnW

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_eq_sum_rank_one_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  atlas_forward_decl GlobalTheory.UnipKill.skew_eq_sum_rk1
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E), ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  atlas_forward_decl GlobalTheory.exists_common_denominator
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem scaleDecomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N)
    (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) →
    ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧
      (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧
      (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) =
        ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  intro E _ _ _ N X d ξ t ht
  choose a ha hmem using fun j => GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (ξ j)
  obtain ⟨b, hb, hint⟩ := GlobalTheory.T.exists_common_denominator_isIntegral E d (fun j => t j / ((a j : ℕ) : E) ^ 2)
  have ha0 : ∀ j, ((a j : ℕ) : E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (ha j).ne'
  refine ⟨X.m * b, fun j => ((a j : ℕ) : E) • ξ j, fun j => (b : E) * (t j / ((a j : ℕ) : E) ^ 2),
    Nat.mul_pos X.m_pos hb, hmem, fun j => ⟨_, rfl⟩, ?_, hint, ?_⟩
  · intro j
    rw [cc_mul, div_eq_mul_inv, cc_mul, cc_inv, cc_pow, cc_natCast, cc_natCast, ht, ← div_eq_mul_inv]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rk1_smul_left, rk1_smul_right, cc_natCast, smul_smul, smul_smul, smul_smul]
    congr 1
    have := ha0 j
    push_cast
    field_simp

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_rank_one_integral_rescaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) → ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧ (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧ (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) = ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  atlas_forward_decl GlobalTheory.UnipKill.scaleDecomp
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

theorem algInt_dvd_nonzero_intCast : ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E), u ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ u ∣ (c : 𝓞 E) := by
  intro E _ _ u hu
  refine ⟨Algebra.intNorm ℤ (𝓞 E) u, Algebra.intNorm_ne_zero.2 hu, ?_⟩
  have := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) u
  simpa using this

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_multiple_of_integer : ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E), u ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ u ∣ (c : 𝓞 E) := by
  atlas_forward_decl GlobalTheory.algInt_dvd_nonzero_intCast
end

section
section
namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem mul_rk1_self_of_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E) (hg : IsIsom G g)
    (hξ : g.mulVec ξ = ε • ξ) (hc : cc ε = ε) (h0 : ε ≠ 0) :
    g * rk1 G ξ ξ = ε ^ 2 • (rk1 G ξ ξ * g) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  have h1 : g.mulVec (ε⁻¹ • ξ) = ξ := by
    rw [Matrix.mulVec_smul, hξ, smul_smul, inv_mul_cancel₀ h0, one_smul]
  have h2 : herm G (g.mulVec x) ξ = ε⁻¹ * herm G x ξ := by
    have h3 := hg x (ε⁻¹ • ξ)
    rw [h1, herm_smul_right, cc_inv, hc] at h3
    exact h3
  rw [← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, Matrix.mulVec_smul, hξ, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, h2, smul_smul, smul_smul]
  congr 1
  field_simp

theorem mul_transvMat_of_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ →
    cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  intro E _ _ _ N G g ξ ε hg hξ hc h0 α
  rw [transvMat_eq, transvMat_eq, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, mul_rk1_self_of_scale G g ξ ε hg hξ hc h0, smul_smul, mul_comm α]

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_conj_transvection_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ → cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  atlas_forward_decl GlobalTheory.UnipKill.mul_transvMat_of_scale
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_isotropic_partner (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (ξ : Fin N → E) (hξΛ : ξ ∈ X.Λ) (hξ : ξ ≠ 0) (hξξ : herm X.Gm ξ ξ = 0) :
    ∃ (η : Fin N → E) (d : ℕ), 0 < d ∧ η ∈ X.Λ ∧ herm X.Gm ξ η = d ∧ herm X.Gm η η = 0 := by
  have hG := X.Gm_herm
  obtain ⟨y, hy⟩ : ∃ y, herm X.Gm ξ y ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (eq_zero_of_herm X.Gm X.Gm_det ξ hno)
  have h1 : herm X.Gm ξ ((cc (herm X.Gm ξ y))⁻¹ • y) = 1 := by
    rw [herm_smul_right, cc_inv, cc_cc]; exact inv_mul_cancel₀ hy
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = (cc (herm X.Gm ξ y))⁻¹ • y := ⟨_, rfl⟩
  rw [← hy1] at h1
  have h1' : herm X.Gm y1 ξ = 1 := by
    rw [← cc_herm X.Gm hG, h1, cc_one]
  have hhc : cc (herm X.Gm y1 y1) = herm X.Gm y1 y1 := cc_herm X.Gm hG y1 y1
  have hhalf : cc (herm X.Gm y1 y1 / 2) = herm X.Gm y1 y1 / 2 := by
    rw [div_eq_mul_inv, cc_mul, cc_inv, cc_two, hhc]
  have e1 : herm X.Gm ξ (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 1 := by
    rw [herm_sub_right, herm_smul_right, h1, hξξ]; ring
  have e2 : herm X.Gm (y1 - (herm X.Gm y1 y1 / 2) • ξ) (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 0 := by
    rw [herm_sub_left, herm_sub_right, herm_sub_right, herm_smul_right, herm_smul_right,
      herm_smul_left, herm_smul_left, h1, h1', hξξ, hhalf]
    ring
  obtain ⟨d, hd, hdΛ⟩ := GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (y1 - (herm X.Gm y1 y1 / 2) • ξ)
  refine ⟨(d : E) • (y1 - (herm X.Gm y1 y1 / 2) • ξ), d, hd, hdΛ, ?_, ?_⟩
  · rw [herm_smul_right, cc_natCast, e1, mul_one]
  · rw [herm_smul_left, herm_smul_right, e2]; ring

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_lattice_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ (η : Fin N → E) (d : ℕ), 0 < d ∧ η ∈ X.Λ ∧ herm X.Gm ξ η = d ∧ herm X.Gm η η = 0 := by
  atlas_forward_decl GlobalTheory.UnipKill.exists_isotropic_partner
end

section
section
namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem isUStab_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {G : Matrix (Fin N) (Fin N) E} {Λ : Submodule (𝓞 E) (Fin N → E)} {g g' : GL (Fin N) E}
    (hg : IsUStab G Λ g) (hg' : IsUStab G Λ g') : IsUStab G Λ (g * g') := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hg.1, hg'.1]
  · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg'.2, hg.2]

theorem isUStab_one {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (G : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    IsUStab G Λ (1 : GL (Fin N) E) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩ <;> simp

theorem isUStab_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {G : Matrix (Fin N) (Fin N) E} {Λ : Submodule (𝓞 E) (Fin N → E)} {g : GL (Fin N) E}
    (hg : IsUStab G Λ g) (n : ℕ) : IsUStab G Λ (g ^ n) := by
  induction n with
  | zero => simpa using isUStab_one G Λ
  | succ n ih => rw [pow_succ]; exact isUStab_mul ih hg

theorem pow_mem_of_isUStab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (g : GL (Fin N) E), IsUStab X.Gm X.Λ g → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
  intro E _ _ _ N X g hg
  obtain ⟨S, hS⟩ := X.Γ_index
  have h : ∀ n : ℕ, ∃ s : S, (s : GL (Fin N) E)⁻¹ * g ^ n ∈ X.Γ := fun n => by
    obtain ⟨s, hs, hmem⟩ := hS _ (isUStab_pow hg n)
    exact ⟨⟨s, hs⟩, hmem⟩
  choose f hf using h
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
    intro a b hlt hf'
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have h1 := X.Γ.mul_mem (X.Γ.inv_mem (hf a)) (hf b)
    rw [hf'] at h1
    have : ((f b : GL (Fin N) E)⁻¹ * g ^ a)⁻¹ * ((f b : GL (Fin N) E)⁻¹ * g ^ b) = g ^ (b - a) := by
      rw [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc (f b : GL (Fin N) E), mul_inv_cancel,
        one_mul, ← Nat.add_sub_cancel' hlt.le, pow_add, ← mul_assoc, inv_mul_cancel, one_mul,
        Nat.add_sub_cancel_left]
    rwa [this] at h1
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hfab
  · exact key b a h hfab.symm

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (g : GL (Fin N) E), IsUStab X.Gm X.Λ g → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
  atlas_forward_decl GlobalTheory.UnipKill.pow_mem_of_isUStab
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

open NumberField.Units IsCMField in

theorem exists_real_unit_infinite_order (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hE : 1 < Module.finrank ℚ E / 2) :
    ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  have hrank : 0 < rank E := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
    unfold rank
    omega
  let i : Fin (rank E) := ⟨0, hrank⟩
  refine ⟨realFundSystem E i, ?_, ?_⟩
  · simp only [realFundSystem, cc]
    exact complexConj_apply_eq_self E _
  · intro n hn hpow
    set v := fundSystem (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    have hv : v ^ n = 1 := by
      have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) E) :=
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) E)
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E]
      exact hpow
    have htor : v ∈ torsion (maximalRealSubfield E) := (CommGroup.mem_torsion _).mpr
      ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hv⟩)
    have hmk := fundSystem_mk (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    rw [(QuotientGroup.eq_one_iff _).mpr htor] at hmk
    exact (basisModTorsion (maximalRealSubfield E)).ne_zero _ hmk.symm

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_unit_not_root_of_unity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], 1 < Module.finrank ℚ E / 2 → ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.exists_real_unit_infinite_order
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem hypRot_smul_mem (X : Data E N) {s : E} (hs : IsIntegral ℤ s) {v : Fin N → E}
    (hv : v ∈ X.Λ) : s • v ∈ X.Λ := by
  have : s • v = (⟨s, hs⟩ : 𝓞 E) • v := by
    rw [← algebraMap_smul E (⟨s, hs⟩ : 𝓞 E) v]; rfl
  rw [this]; exact X.Λ.smul_mem _ hv

theorem hypRot_mulVec (X : Data E N) (ξ η : Fin N → E) (a b : E) (x : Fin N → E) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x =
      x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]

theorem hypRot_mul_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (key : a + b + a * b * d = 0) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ) * (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ) = 1 := by
  have hPP : rk1 X.Gm ξ η * rk1 X.Gm ξ η = (d : E) • rk1 X.Gm ξ η := by rw [one_add_smul_vecMulVec_mul, hξη]
  have hPQ : rk1 X.Gm ξ η * rk1 X.Gm η ξ = 0 := by rw [one_add_smul_vecMulVec_mul, hηη, zero_smul]
  have hQP : rk1 X.Gm η ξ * rk1 X.Gm ξ η = 0 := by rw [one_add_smul_vecMulVec_mul, hξξ, zero_smul]
  have hQQ : rk1 X.Gm η ξ * rk1 X.Gm η ξ = (d : E) • rk1 X.Gm η ξ := by rw [one_add_smul_vecMulVec_mul, hηξ]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPQ, hQP, hQQ,
    smul_zero, smul_smul]
  calc _ = 1 + (a + b + a * b * d) • rk1 X.Gm ξ η + (a + b + a * b * d) • rk1 X.Gm η ξ := by module
    _ = 1 := by rw [key, zero_smul, zero_smul, add_zero, add_zero]

theorem herm_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (ha : cc a = a) (hb : cc b = b) (key : a + b + a * b * d = 0)
    (x y : Fin N → E) :
    herm X.Gm (x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η)
      (y + (a * herm X.Gm y η) • ξ + (b * herm X.Gm y ξ) • η) = herm X.Gm x y := by
  have hc := cc_herm X.Gm X.Gm_herm
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, cc_mul, ha, hb, hc,
    hξξ, hηη, hξη, hηξ]
  linear_combination (herm X.Gm x ξ * herm X.Gm η y + herm X.Gm x η * herm X.Gm ξ y) * key

theorem exists_isUStab_hypRot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  intro E _ _ _ N X ξ η d ε c hd hξ hη hξξ hηη hξη hεr hε0 hεi hεii hεc
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hηξ : herm X.Gm η ξ = d := by rw [← cc_herm X.Gm X.Gm_herm ξ η, hξη, cc_natCast]
  obtain ⟨a, ha_def⟩ : ∃ a : E, a = (ε - 1) / d := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : E, b = (ε⁻¹ - 1) / d := ⟨_, rfl⟩
  have ha : cc a = a := by
    rw [ha_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, hεr]
  have hb : cc b = b := by
    rw [hb_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, cc_inv, hεr]
  have key : a + b + a * b * d = 0 := by
    rw [ha_def, hb_def]; field_simp; ring
  have key' : b + a + b * a * d = 0 := by linear_combination key
  have ha' : a = (X.den : E) * c := by
    rw [ha_def, div_eq_iff hdE, hεc]; ring
  have hinv : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
  have hb' : b = -(ε⁻¹ * ((X.den : E) * c)) := by
    rw [hb_def, div_eq_iff hdE]; linear_combination (-ε⁻¹) * hεc + hinv
  have hA : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (a * herm X.Gm x y) := by
    intro x hx y hy
    rw [ha', show (X.den : E) * c * herm X.Gm x y = c * (X.den * herm X.Gm x y) by ring]
    exact (RingOfIntegers.isIntegral_coe c).mul (X.Λ_int x hx y hy)
  have hB : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (b * herm X.Gm x y) := by
    intro x hx y hy
    rw [hb', show -(ε⁻¹ * ((X.den : E) * c)) * herm X.Gm x y =
      -(ε⁻¹ * c * (X.den * herm X.Gm x y)) by ring]
    exact ((hεii.mul (RingOfIntegers.isIntegral_coe c)).mul (X.Λ_int x hx y hy)).neg
  have h01 := hypRot_mul_hypRot X ξ η d a b hξξ hηη hξη hηξ key
  have h10 := hypRot_mul_hypRot X ξ η d b a hξξ hηη hξη hηξ key'
  have hm0 : ∀ x ∈ X.Λ, (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hA x hx η hη) hξ))
      (hypRot_smul_mem X (hB x hx ξ hξ) hη)
  have hm1 : ∀ x ∈ X.Λ, (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hB x hx η hη) hξ))
      (hypRot_smul_mem X (hA x hx ξ hξ) hη)
  refine ⟨⟨_, _, h01, h10⟩, ⟨fun x y => ?_, fun x => ⟨hm0 x, fun h => ?_⟩⟩, ?_⟩
  · show herm X.Gm ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x)
      ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec y) = herm X.Gm x y
    rw [hypRot_mulVec, hypRot_mulVec]
    exact herm_hypRot X ξ η d a b hξξ hηη hξη hηξ ha hb key x y
  · have := hm1 _ h
    rwa [Matrix.mulVec_mulVec, h10, Matrix.one_mulVec] at this
  · show (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec ξ = ε • ξ
    rw [hypRot_mulVec, hξη, hξξ, mul_zero, zero_smul, add_zero]
    have : a * d = ε - 1 := by rw [ha_def]; field_simp
    rw [this]; module

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  atlas_forward_decl GlobalTheory.UnipKill.exists_isUStab_hypRot
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem unit_pow_congr_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E),
    M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  intro E _ _ u M hM
  set I : Ideal (𝓞 E) := Ideal.span {M} with hI
  have hIb : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hM
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hIb
  haveI : Finite (𝓞 E ⧸ I)ˣ := Finite.of_injective (fun x : (𝓞 E ⧸ I)ˣ => (x : 𝓞 E ⧸ I)) (fun a b h => Units.ext h)
  set v : (𝓞 E ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝓞 E →* 𝓞 E ⧸ I) u with hv
  refine ⟨orderOf v, (isOfFinOrder_of_finite v).orderOf_pos, ?_⟩
  have h1 : v ^ orderOf v = 1 := pow_orderOf_eq_one v
  have h2 : Ideal.Quotient.mk I ((u ^ orderOf v : (𝓞 E)ˣ) : 𝓞 E) = Ideal.Quotient.mk I 1 := by
    have := congrArg (fun w : (𝓞 E ⧸ I)ˣ => (w : 𝓞 E ⧸ I)) h1
    simp only [hv, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at this
    simpa [Units.val_pow_eq_pow_val, map_pow] using this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h2)

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_unit_pow_sub_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E), M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.unit_pow_congr_one
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem gl_pow_mulVec {E : Type} [Field E] {N : ℕ} (g : GL (Fin N) E) (ξ : Fin N → E) (ε : E)
    (h : (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ) (k : ℕ) :
    ((g ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).mulVec ξ = ε ^ k • ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ']

theorem killsScaled : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 →
    herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t →
    ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  intro E _ _ _ N X hdeg φ ξ hξ hξ0 hiso
  obtain ⟨η, d, hd, hη, hξη, hηη⟩ := GlobalTheory.T.exists_isotropic_dual_lattice_vector E N X ξ hξ hξ0 hiso
  obtain ⟨u0, hu0c, hu0⟩ := GlobalTheory.T.exists_real_unit_not_root_of_unity E hdeg
  have hM : ((d : 𝓞 E) * X.den) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hd.ne') X.den_ne
  obtain ⟨k1, hk1, c, hc⟩ := GlobalTheory.T.dvd_unit_pow_sub_one E u0 _ hM

  obtain ⟨v, hv⟩ : ∃ v : (𝓞 E)ˣ, v = u0 ^ k1 := ⟨_, rfl⟩
  rw [← hv] at hc
  obtain ⟨ε, hε⟩ : ∃ ε : E, ε = ((v : 𝓞 E) : E) := ⟨_, rfl⟩
  have hεpow : ε = ((u0 : 𝓞 E) : E) ^ k1 := by
    rw [hε, hv, Units.val_pow_eq_pow_val]; exact map_pow (algebraMap (𝓞 E) E) _ _
  have hεc : cc ε = ε := by rw [hεpow, cc_pow, hu0c]
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact (v.isUnit.map (algebraMap (𝓞 E) E)).ne_zero
  have hεint : IsIntegral ℤ ε := by rw [hε]; exact RingOfIntegers.isIntegral_coe _
  have hεinv : IsIntegral ℤ ε⁻¹ := by
    have h1 : (((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * ε = 1 := by
      have := congrArg (algebraMap (𝓞 E) E) (Units.inv_mul v)
      rw [map_mul, map_one] at this
      rw [hε]; exact this
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact RingOfIntegers.isIntegral_coe _
  have hε1 : ε - 1 = d * X.den * c := by
    have := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_sub, map_one, map_mul, map_mul, map_natCast] at this
    rw [hε]; exact this
  obtain ⟨g, hgU, hgξ⟩ :=
    GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic E N X ξ η d ε c hd hξ hη hiso hηη hξη hεc hε0 hεint hεinv hε1
  obtain ⟨k2, hk2, hmem⟩ := GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer E N X g hgU
  have hgmξ := gl_pow_mulVec g ξ ε hgξ k2
  have hgiso : IsIsom X.Gm ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) :=
    (X.Γ_stab _ hmem).1
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ = ε ^ k2 := ⟨_, rfl⟩
  rw [← hθ] at hgmξ
  have hθc : cc θ = θ := by rw [hθ, cc_pow, hεc]
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact pow_ne_zero _ hε0
  have hθint : IsIntegral ℤ (θ ^ 2) := by rw [hθ]; exact (hεint.pow _).pow _
  have hθ2 : θ ^ 2 ≠ 1 := by
    have := hu0 (k1 * k2 * 2) (by positivity)
    rwa [pow_mul, pow_mul, ← hεpow, ← hθ] at this

  have hucoe : ((((v : 𝓞 E) ^ k2) ^ 2 - 1 : 𝓞 E) : E) = θ ^ 2 - 1 := by
    rw [hθ, hε]
    simp only [map_sub, map_pow, map_one]
  refine ⟨((v : 𝓞 E) ^ k2) ^ 2 - 1, ?_, ?_, ?_⟩
  · intro h0
    apply hθ2
    have : θ ^ 2 - 1 = 0 := by rw [← hucoe, h0]; exact map_zero (algebraMap (𝓞 E) E)
    exact sub_eq_zero.1 this
  · rw [hucoe, cc_sub, cc_pow, hθc, cc_one]
  intro t ht hti γ hγ
  rw [hucoe] at hγ
  obtain ⟨a, ha, hav⟩ := X.transv ξ hξ hiso t ht hti
  have hθt : cc (θ ^ 2 * t) = θ ^ 2 * t := by rw [cc_mul, cc_pow, hθc, ht]
  obtain ⟨b, hb, hbv⟩ := X.transv ξ hξ hiso (θ ^ 2 * t) hθt (hθint.mul hti)
  have eq1 : (⟨g ^ k2, hmem⟩ : X.Γ) * ⟨a, ha⟩ = ⟨b, hb⟩ * ⟨g ^ k2, hmem⟩ := by
    apply Subtype.ext
    apply Units.ext
    show ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (a : Matrix (Fin N) (Fin N) E) =
      (b : Matrix (Fin N) (Fin N) E) * ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hav, hbv, GlobalTheory.T.isometry_conj_transvection_scale E N X.Gm _ ξ θ hgiso hgmξ hθc hθ0]
    congr 2
    ring
  have eq2 : φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by
    have := congrArg φ eq1
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel this
  have eq3 : (⟨b, hb⟩ : X.Γ) = ⟨a, ha⟩ * γ := by
    apply Subtype.ext
    apply Units.ext
    show (b : Matrix (Fin N) (Fin N) E) =
      (a : Matrix (Fin N) (Fin N) E) * ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hbv, hav, hγ, transvMat_mul_self X.Gm ξ hiso]
    congr 1
    ring
  have eq4 : φ ⟨a, ha⟩ * φ γ = φ ⟨a, ha⟩ := by rw [← map_mul, ← eq3, ← eq2]
  exact mul_eq_left.1 eq4

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unit_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.killsScaled
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem killsTransv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E),
    ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ,
    ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) →
    φ γ = 1 := by
  intro E _ _ _ N X hE φ ξ s hξ hiso hs hsint γ hγ
  by_cases h0 : ξ = 0
  · subst h0
    have h1 : ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := by
      rw [hγ]; ext a b; simp [transvMat, Matrix.one_apply]
    have : γ = 1 := by
      apply Subtype.ext; apply Units.ext; simpa using h1
    rw [this, map_one]
  obtain ⟨u, hu0, hureal, hkill⟩ := GlobalTheory.T.character_trivial_on_unit_transvections E N X hE φ ξ hξ h0 hiso
  obtain ⟨c, hc0, u', hu'⟩ := GlobalTheory.T.exists_int_multiple_of_integer E u hu0
  have hcE : (c : E) = (u : E) * (u' : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) hu'
    simpa using this
  have huE : (u : E) ≠ 0 := by
    intro h; exact hu0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have hu'real : cc (u' : E) = u' := by
    have e : (u' : E) = (c : E) * (u : E)⁻¹ := by
      rw [hcE]; field_simp
    rw [e, cc_mul, cc_inv, cc_intCast, hureal]
  have hu'int : IsIntegral ℤ (u' : E) := RingOfIntegers.isIntegral_coe u'
  set n := c.natAbs with hn
  have hnpos : n ≠ 0 := Int.natAbs_ne_zero.mpr hc0
  obtain ⟨t, ht, htint, hut⟩ : ∃ t : E, cc t = t ∧ IsIntegral ℤ t ∧
      (u : E) * t = (n : E) * s := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨(u' : E) * s, by rw [cc_mul, hu'real, hs], hu'int.mul hsint, ?_⟩
      have : ((n : ℤ) : E) = (c : E) := by rw [← h]
      rw [← Int.cast_natCast, this, hcE]; ring
    · refine ⟨-((u' : E) * s), by rw [cc_neg, cc_mul, hu'real, hs], (hu'int.mul hsint).neg, ?_⟩
      have : ((n : ℤ) : E) = -(c : E) := by rw [h, Int.cast_neg, neg_neg]
      rw [← Int.cast_natCast, this, hcE]; ring
  have hmat : ((γ ^ n : X.Γ) : GL (Fin N) E) = (γ : GL (Fin N) E) ^ n := Subgroup.coe_pow _ _ _
  have hγn : (((γ ^ n : X.Γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) := by
    rw [hmat, Units.val_pow_eq_pow_val, hγ, transvMat_pow X.Gm ξ hiso, hut]
    congr 1; ring
  have hk := hkill t ht htint (γ ^ n) hγn
  rw [map_pow] at hk
  have h2 : n • Multiplicative.toAdd (φ γ) = 0 := by
    rw [← toAdd_pow, hk, toAdd_one]
  rw [nsmul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd (by exact_mod_cast h2) hnpos
  · exact Multiplicative.toAdd.injective (by rw [h2, toAdd_one])

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_integral_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E), ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) → φ γ = 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.killsTransv
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_mem_sum_transv_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (φ : X.Γ →* Multiplicative ℝ) (d : ℕ) (ξ : Fin d → Fin N → E) (α : Fin d → E), (∀ i j, herm X.Gm (ξ i) (ξ j) = 0) → (∀ j, ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ j) (α j) ∧ φ γ = 1) → ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 + ∑ j, α j • rk1 X.Gm (ξ j) (ξ j) ∧ φ γ = 1 := by
  intro E _ _ _ N X φ d
  induction d with
  | zero =>
    intro ξ α _ _
    refine ⟨1, ?_, map_one φ⟩
    simp
  | succ d ih =>
    intro ξ α horth hγ
    obtain ⟨γ0, h0, hφ0⟩ := ih (ξ ∘ Fin.castSucc) (α ∘ Fin.castSucc)
      (fun i j => horth _ _) (fun j => hγ _)
    obtain ⟨γl, hl, hφl⟩ := hγ (Fin.last d)
    refine ⟨γ0 * γl, ?_, by rw [map_mul, hφ0, hφl, one_mul]⟩
    have hmat : ((γ0 * γl : X.Γ) : GL (Fin N) E) = (γ0 : GL (Fin N) E) * (γl : GL (Fin N) E) := rfl
    rw [hmat, Matrix.GeneralLinearGroup.coe_mul, h0, hl, transvMat_eq, Fin.sum_univ_castSucc]
    have hz : (∑ j : Fin d, (α ∘ Fin.castSucc) j • rk1 X.Gm ((ξ ∘ Fin.castSucc) j) ((ξ ∘ Fin.castSucc) j))
        * (α (Fin.last d) • rk1 X.Gm (ξ (Fin.last d)) (ξ (Fin.last d))) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, one_add_smul_vecMulVec_mul]
      simp only [Function.comp_apply, horth, zero_smul, smul_zero]
    rw [add_mul, one_mul, mul_add, mul_one, hz, add_zero]
    simp only [Function.comp]
    abel

end GlobalTheory.UnipKill
end

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_sum_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (φ : X.Γ →* Multiplicative ℝ) (d : ℕ) (ξ : Fin d → Fin N → E) (α : Fin d → E), (∀ i j, herm X.Gm (ξ i) (ξ j) = 0) → (∀ j, ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ j) (α j) ∧ φ γ = 1) → ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 + ∑ j, α j • rk1 X.Gm (ξ j) (ξ j) ∧ φ γ = 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.exists_mem_sum_transv_killed
end

section
section
namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem char_eq_one_of_sq_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  intro E _ _ _ N X hE φ γ hγ
  set A : Matrix (Fin N) (Fin N) E := ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) with hA
  set n : Matrix (Fin N) (Fin N) E := A - 1 with hn
  have h2 : n * n = 0 := by rw [← pow_two]; exact hγ
  have hiso : IsIsom X.Gm A := fun x y => (X.Γ_stab _ γ.2).1 x y
  have hsk : IsSkew X.Gm n := isSkew_sub_one X.Gm hiso h2
  set W : Submodule E (Fin N → E) := LinearMap.range (Matrix.mulVecLin n) with hW
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, herm X.Gm u v = 0 := by
    rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
    exact herm_mulVec_mulVec_eq_zero X.Gm hsk h2 x y
  have hκ : cc X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc_mul, cc_neg, X.ξ0_im, cc_two]
  have hκ0 : X.κ0 ≠ 0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  obtain ⟨d, ξ, t, hξW, ht, hnd⟩ := GlobalTheory.T.skew_eq_sum_rank_one_isotropic E N X.Gm X.κ0 X.Gm_herm X.Gm_det hκ hκ0 W hWiso n hsk
    (fun y => ⟨y, rfl⟩)
  obtain ⟨k, ξ', s, hk, hξ'Λ, hξ'a, hs, hsint, hsum⟩ := GlobalTheory.T.sum_rank_one_integral_rescaling E N X d ξ t ht
  have horth : ∀ i j, herm X.Gm (ξ' i) (ξ' j) = 0 := by
    intro i j
    obtain ⟨a, ha⟩ := hξ'a i; obtain ⟨b, hb⟩ := hξ'a j
    rw [ha, hb, herm_smul_left, herm_smul_right, hWiso _ (hξW i) _ (hξW j)]; ring
  have hkill : ∀ j, ∃ γ' : X.Γ, ((γ' : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ' j) (X.m * s j * X.κ0) ∧ φ γ' = 1 := by
    intro j
    obtain ⟨γ', hγ'Γ, hγ'⟩ := X.transv (ξ' j) (hξ'Λ j) (horth j j) (s j) (hs j) (hsint j)
    exact ⟨⟨γ', hγ'Γ⟩, hγ', GlobalTheory.T.character_trivial_on_integral_transvections E N X hE φ (ξ' j) (s j) (hξ'Λ j) (horth j j) (hs j) (hsint j) ⟨γ', hγ'Γ⟩ hγ'⟩
  obtain ⟨γ', hγ'eq, hφγ'⟩ := GlobalTheory.T.character_trivial_on_sum_transvections E N X φ d ξ' (fun j => X.m * s j * X.κ0) horth hkill
  have hpow : γ ^ k = γ' := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hγ'eq, ← hsum, ← hnd]
    have : (γ : GL (Fin N) E).val = 1 + n := by rw [hn]; abel
    rw [this, one_add_pow_of_sq_eq_zero h2]
  have hφ : φ γ ^ k = 1 := by rw [← map_pow, hpow, hφγ']
  have : k • Multiplicative.toAdd (φ γ) = 0 := by
    have := congrArg Multiplicative.toAdd hφ
    rwa [toAdd_pow, toAdd_one] at this
  have h0 := (smul_eq_zero.1 this).resolve_left hk.ne'
  exact Multiplicative.toAdd.injective (by simpa using h0)
end GlobalTheory.UnipKill
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  atlas_forward_decl GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero
end
