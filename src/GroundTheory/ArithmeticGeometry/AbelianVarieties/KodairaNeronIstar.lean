import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronStar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

def StageY {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (j : ℕ) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ (∃ A₂, W.a₂ = π * A₂ ∧ ¬π ∣ A₂) ∧ π ^ j ∣ W.a₃ ∧ π ^ (j + 1) ∣ W.a₄ ∧
    π ^ (2 * j) ∣ W.a₆

def StageX {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (j : ℕ) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ (∃ A₂, W.a₂ = π * A₂ ∧ ¬π ∣ A₂) ∧ π ^ (j + 1) ∣ W.a₃ ∧ π ^ (j + 1) ∣ W.a₄ ∧
    π ^ (2 * j + 1) ∣ W.a₆

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪) {π : 𝒪} (hπ : Irreducible π)
include hπ

theorem StageX.stageY {j : ℕ} (h : StageX π j W) : StageY π j W :=
  ⟨h.1, h.2.1, (pow_dvd_pow π (by omega)).trans h.2.2.1, h.2.2.2.1,
    (pow_dvd_pow π (by omega)).trans h.2.2.2.2⟩








theorem stageY_dvd_Δ {i : ℕ} (hS : StageY π (i + 2) W) : π ^ (2 * i + 7) ∣ W.Δ := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, -⟩, ⟨B₃, hB₃⟩, ⟨B₄, hB₄⟩, ⟨B₆, hB₆⟩⟩ := hS
  set c₂ := π * A₁ ^ 2 + 4 * A₂
  set c₄ := 2 * B₄ + A₁ * B₃
  set c₆ := B₃ ^ 2 + 4 * B₆
  set c₈ := π * A₁ ^ 2 * B₆ + 4 * A₂ * B₆ - π * A₁ * B₃ * B₄ + A₂ * B₃ ^ 2 - π * B₄ ^ 2
  have e2 : W.b₂ = π * c₂ := by
    rw [WeierstrassCurve.b₂, hA₁, hA₂]; ring
  have e4 : W.b₄ = π ^ (i + 3) * c₄ := by
    rw [WeierstrassCurve.b₄, hA₁, hB₃, hB₄]; ring
  have e6 : W.b₆ = π ^ (2 * i + 4) * c₆ := by
    rw [WeierstrassCurve.b₆, hB₃, hB₆]; ring
  have e8 : W.b₈ = π ^ (2 * i + 5) * c₈ := by
    rw [WeierstrassCurve.b₈, hA₁, hA₂, hB₃, hB₄, hB₆]; ring
  rw [WeierstrassCurve.Δ, e2, e4, e6, e8]
  exact ⟨-c₂ ^ 2 * c₈ - 8 * π ^ (i + 2) * c₄ ^ 3 - 27 * π ^ (2 * i + 1) * c₆ ^ 2 +
    9 * π ^ (i + 1) * c₂ * c₄ * c₆, by ring⟩

end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

local notation "ι" => algebraMap 𝒪 K


omit [IsDiscreteValuationRing 𝒪] in
theorem not_dvd_of_not_sq_dvd {X : 𝒪} (h : ¬π ^ 2 ∣ π * X) : ¬π ∣ X := by
  rintro ⟨c, rfl⟩; exact h ⟨c, by ring⟩




omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] hπ in
theorem vc_Δ_one (r s t : 𝒪) : ((⟨1, r, s, t⟩ : VariableChange 𝒪) • W).Δ = W.Δ := by
  simp [variableChange_Δ]

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem exists_not_pow_dvd {a : 𝒪} (ha : a ≠ 0) : ∃ n, ¬π ^ n ∣ a := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n + 1, fun ⟨c, hc⟩ => hπ.not_isUnit ?_⟩
  have : (u : 𝒪) = π * c := by
    apply mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero)
    rw [hc]; ring
  exact isUnit_of_dvd_unit ⟨c, this⟩ u.isUnit



end Bound

end

end GroundTheory.Arith.Abelian
