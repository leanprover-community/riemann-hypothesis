import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.ShiftPowerSumMul
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLinearFunctionals
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansion
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBound
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LieTermFlagBound
import Development.WeilBound.CoreStatements.FlagImmersions.TwoMulThreePowLeFactorial
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousPowerSumDecomposition
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPower
import Development.WeilBound.CoreStatements.FlagImmersions.PartialSumOrderedBounds

section
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sh_tot_pk_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ σ : Ψ) (k : ℕ) (Q : RP Ψ N), 1 ≤ k → Sh j σ (pk τ k * Q) = (if σ = τ then k * degFl (pkLow j τ (k - 1) * Q) else 0) ∧ Tot σ (pk τ k * Q) = (if σ = τ ∧ k = 1 then N * degFl Q else 0) :=
  RootFieldNumerics.shift_power_sum_mul

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_shift_total_power_sum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ σ : Ψ) (k : ℕ) (Q : RP Ψ N), 1 ≤ k → Sh j σ (pk τ k * Q) = (if σ = τ then k * degFl (pkLow j τ (k - 1) * Q) else 0) ∧ Tot σ (pk τ k * Q) = (if σ = τ ∧ k = 1 then N * degFl Q else 0) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

def lieRank {Ψ : Type} (N j : ℕ) (s : Ψ ⊕ Ψ) : ℝ := if s.isLeft then (j : ℝ) else ((N - j : ℕ) : ℝ)

theorem delta_card_filter_lt {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := by
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).map Fin.valEmbedding = Finset.range j := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro ha
      exact ⟨⟨a, lt_of_lt_of_le ha hj⟩, ha, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_range]

theorem delta_card_filter_ge {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  rw [delta_card_filter_lt hj] at h
  omega

theorem pLie_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) :
    (pLie j 0 s : RP Ψ N) = C (lieRank N j s) := by
  cases s with
  | inl τ =>
    simp only [pLie, pkLow, pow_zero, Finset.sum_const, delta_card_filter_lt hj, lieRank, Sum.isLeft_inl, if_true,
      nsmul_eq_mul, mul_one, map_natCast]
  | inr τ =>
    simp only [pLie, pow_zero, Finset.sum_const, delta_card_filter_ge hj, lieRank, Sum.isLeft_inr,
      Bool.false_eq_true, if_false, nsmul_eq_mul, mul_one, map_natCast]

theorem degFl_C_mul {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (c : ℝ) (Q : RP Ψ N) :
    degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul]
  have h : ∀ f g : (Ψ → Equiv.Perm (Fin N)) → ℝ, ∑ σ, f σ * (c * g σ) = c * ∑ σ, f σ * g σ := by
    intro f g
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h]
  ring

theorem deltaTerm_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  intro Ψ _ _ N j frob hj hN hF
  rcases isEmpty_or_nonempty Ψ with hE | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun _ τ => isEmptyElim τ⟩
  refine ⟨fun p => Real.log p / N * ∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n), ?_⟩
  intro p τ k Q hp hk
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hSh : ∑ σ, Sh j σ (pk τ k * Q) = k * degFl (pkLow j τ (k - 1) * Q) := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).1)]
    simp
  have hTot : ∑ σ, Tot σ (pk τ k * Q) = if k = 1 then N * degFl Q else 0 := by
    rw [Finset.sum_congr rfl (fun σ _ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N j τ σ k Q hk).2)]
    by_cases h1 : k = 1 <;> simp [h1]
  rw [hSh, hTot]
  by_cases h1 : k = 1
  · subst h1
    have hrank : ∀ n, degFl (pLie j (1 - 1) (frob p τ n) * Q) =
        lieRank N j (frob p τ₀ n) * degFl Q := by
      intro n
      have : lieRank N j (frob p τ n) = lieRank N j (frob p τ₀ n) := by
        simp only [lieRank, hF p n τ τ₀]
      rw [Nat.sub_self, pLie_zero hj, degFl_C_mul, this]
    have hsum : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl (pLie j (1 - 1) (frob p τ n) * Q)) =
        (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n)) * degFl Q := by
      rw [← tsum_mul_right]
      exact tsum_congr (fun n => by rw [hrank]; ring)
    simp only [deltaTerm, restTerm, hsum]
    simp only [if_true, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, if_false]
    field_simp
    ring
  · have h2 : 2 ≤ k := by omega
    simp only [deltaTerm, restTerm, h1, if_false, h2, if_true]
    ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sum_delta_decomposition : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.deltaTerm_eq
end

section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_degree_one_polys : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | exact GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot <;> assumption)
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem abs_apply_le_of_monomial_bound {σ : Type} (G : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (F : MvPolynomial σ ℝ) {d : ℕ}
    (hF : F.IsHomogeneous d) {e : ℝ} (he : ∀ m : σ →₀ ℕ, m.degree = d → |G (monomial m 1)| ≤ e) :
    |G F| ≤ (∑ m ∈ F.support, |coeff m F|) * e := by
  have h1 : G F = ∑ m ∈ F.support, coeff m F * G (monomial m 1) := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : monomial m (coeff m F) = coeff m F • monomial m (1 : ℝ) := by
      rw [smul_monomial]; simp
    rw [this, map_smul, smul_eq_mul]
  rw [h1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left (he m ?_) (abs_nonneg _)
  by_contra hne
  exact (mem_support_iff.mp hm) (hF.coeff_eq_zero hne)

theorem tendsto_coeffs_of_tests {a b R₁ R₂ E₁ E₂ : ℕ → ℝ} {v H₁ H₂ L₁ L₂ r₁ r₂ s₁ n s₂ t₂ : ℝ}
    (hv : v ≠ 0) (hn : n ≠ 0) (hs₂ : s₂ ≠ 0) (ht₂ : t₂ = 0)
    (hR₁ : Tendsto R₁ atTop (𝓝 r₁)) (hR₂ : Tendsto R₂ atTop (𝓝 r₂))
    (hE₁ : Tendsto E₁ atTop (𝓝 0)) (hE₂ : Tendsto E₂ atTop (𝓝 0))
    (h₁ : ∀ᶠ B in atTop, L₁ = v * (H₁ - a B * s₁ - b B * n + R₁ B) + E₁ B)
    (h₂ : ∀ᶠ B in atTop, L₂ = v * (H₂ - a B * s₂ - b B * t₂ + R₂ B) + E₂ B) :
    ∃ A b₀ : ℝ, Tendsto a atTop (𝓝 A) ∧ Tendsto b atTop (𝓝 b₀) := by
  subst ht₂
  have ha : Tendsto a atTop (𝓝 ((H₂ + r₂ + 0 / v - L₂ / v) / s₂)) := by
    have h := (((hR₂.const_add H₂).add (hE₂.div_const v)).sub_const (L₂ / v)).div_const s₂
    refine h.congr' ?_
    filter_upwards [h₂] with B hB
    rw [hB]
    field_simp
    ring
  have hb : Tendsto b atTop (𝓝 ((H₁ - (H₂ + r₂ + 0 / v - L₂ / v) / s₂ * s₁ + r₁ + 0 / v - L₁ / v) / n)) := by
    have h := (((((ha.mul_const s₁).const_sub H₁).add hR₁).add (hE₁.div_const v)).sub_const (L₁ / v)).div_const n
    refine h.congr' ?_
    filter_upwards [h₁] with B hB
    rw [hB]
    field_simp
    ring
  exact ⟨_, _, ha, hb⟩

theorem eq_of_tendsto_coeffs {a b R E : ℕ → ℝ} {v H L s t A b₀ r : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 b₀)) (hR : Tendsto R atTop (𝓝 r))
    (hE : Tendsto E atTop (𝓝 0))
    (h : ∀ᶠ B in atTop, L = v * (H - a B * s - b B * t + R B) + E B) :
    L = v * (H - A * s - b₀ * t + r) := by
  have h1 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop
      (𝓝 (v * (H - A * s - b₀ * t + r) + 0)) :=
    ((((((ha.mul_const s).const_sub H).sub (hb.mul_const t)).add hR).const_mul v)).add hE
  have h2 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop (𝓝 L) :=
    tendsto_const_nhds.congr' (h.mono fun B hB => hB)
  simpa using tendsto_nhds_unique h2 h1

theorem tendsto_const_mul_log_div (c C : ℝ) :
    Tendsto (fun B : ℕ => c * (C * Real.log B / B)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h2 := (h.const_mul C).const_mul c
  simp only [mul_zero] at h2
  refine h2.congr fun B => ?_
  simp [mul_div_assoc]

section

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem pk_mul_isHomogeneous (hN : 2 ≤ N) (τ : Ψ) {k : ℕ} (hk : k ≤ N) {Q : RP Ψ N}
    (hQ : Q.IsHomogeneous (dimFl Ψ N + 1 - k)) : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  have h1 : N - 1 ≤ N * (N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm N]
    exact Nat.mul_le_mul_left _ hN
  have h2 : N * (N - 1) / 2 ≤ dimFl Ψ N :=
    Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.mpr ⟨τ⟩)
  have h3 : k + (dimFl Ψ N + 1 - k) = dimFl Ψ N + 1 := by omega
  simpa [h3] using hpk.mul hQ

theorem exists_finite_identity (II : IntersectionSystem) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (hshape : FrobShape frob) (h6 : T.Prop6 II frob) (hBA : T.ThmBA II hh)
    (B₀ : ℕ) (hB₀ : 2 ≤ B₀) :
    ∃ a b : ℕ → ℝ, ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        T.PPt II B₀ (pk τ k * Q) = T.volT * (hh (pk τ k * Q) - a B * ∑ σ, Sh T.j σ (pk τ k * Q) -
          b B * ∑ σ, Tot σ (pk τ k * Q) +
          ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), restTerm T.j p (frob p τ) k Q) + E B := by
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.power_sum_delta_decomposition Ψ N T.j frob T.j_lt.le (by omega) hshape
  obtain ⟨-, hSh, hTot, -⟩ := GlobalTheory.T.flag_degree_linear_functionals Ψ N
  choose ΦS hΦS using hSh
  choose ΦT hΦT using hTot
  obtain ⟨C, B₁, hC⟩ := hBA
  choose! α β hαβ using hC
  let PL : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B => ∑ c, ((T.M B c).PP II).comp (rename some).toLinearMap
  have hPL : ∀ B F, PL B F = T.PPt II B F := by
    intro B F
    simp [PL, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  let G : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B =>
    PL B - T.volT • (hh - (α B - β B) • (∑ σ, ΦS T.j σ) - β B • (∑ σ, ΦT σ))
  have hG : ∀ B F, G B F = T.PPt II B F - T.volT * (hh F - (α B - β B) * ∑ σ, Sh T.j σ F -
      β B * ∑ σ, Tot σ F) := by
    intro B F
    simp [G, hPL, LinearMap.sum_apply, hΦS, hΦT]
  let S : ℕ → Finset ℕ := fun B => (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B => α B - β B + ∑ p ∈ S B, Real.log p / ((p : ℝ) - 1), fun B => β B - ∑ p ∈ S B, κ p,
    fun τ k hk1 hkN Q hQ => ?_⟩
  have hF := pk_mul_isHomogeneous hN τ hkN hQ
  refine ⟨fun B => G B (pk τ k * Q), ?_, ?_⟩
  · refine squeeze_zero_norm' ?_ (tendsto_const_mul_log_div (∑ m ∈ (pk τ k * Q : RP Ψ N).support,
      |coeff m (pk τ k * Q : RP Ψ N)|) C)
    filter_upwards [eventually_ge_atTop B₁] with B hB
    rw [Real.norm_eq_abs]
    refine abs_apply_le_of_monomial_bound (G B) _ hF fun m hm => ?_
    rw [hG]
    exact hαβ B hB m hm
  · filter_upwards [eventually_ge_atTop B₀] with B hB
    have hsum : T.PPt II B₀ (pk τ k * Q) = T.PPt II B (pk τ k * Q) +
        T.volT * ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q := by
      simp only [RootTower.PPt, RootTower.volT, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => h6 B₀ B hB₀ hB c τ k hk1 hkN Q hQ
    have hdelta : ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q =
        -(∑ p ∈ S B, Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh T.j σ (pk τ k * Q) +
          (∑ p ∈ S B, κ p) * ∑ σ, Tot σ (pk τ k * Q) + ∑ p ∈ S B, restTerm T.j p (frob p τ) k Q := by
      rw [Finset.sum_congr rfl fun p hp => hκ p τ k Q
        (Finset.mem_filter.mp hp).2.1.two_le hk1]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        Finset.sum_neg_distrib]
    show T.PPt II B₀ (pk τ k * Q) = _
    rw [hG, hsum, hdelta]
    ring

end

end GlobalTheory.CompanionTheory.Ar.Top

theorem GlobalTheory.CompanionTheory.Ar.Top.exists_identAt : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), T.Proportional → FrobShape frob →
    T.Prop6 II frob → T.ThmBA II hh → ∀ B₀ : ℕ, 2 ≤ B₀ → ∃ A₀ b₀ : ℝ, T.IdentAt II hh frob B₀ A₀ b₀ := by
  intro II Ψ _ _ N T hh frob hprop hshape h6 hBA B₀ hB₀
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨a, b, hid⟩ := exists_finite_identity II T hh frob hshape h6 hBA B₀ hB₀
  have hrest : ∀ (τ : Ψ) (k : ℕ) (Q : RP Ψ N), _ := fun τ k Q =>
    (GlobalTheory.T.remainder_term_summable Ψ N T.j T.bad frob τ k Q).2 B₀
  by_cases hΨ : Nonempty Ψ
  · obtain ⟨τ₀⟩ := hΨ
    obtain ⟨⟨Q₁, hQ₁, hd₁⟩, Q₂, hQ₂, hd₂⟩ := GlobalTheory.T.exists_flag_degree_one_polys Ψ N T.j τ₀ T.j_pos T.j_lt
    have hQ₁' : Q₁.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ₁
    have hQ₂' : Q₂.IsHomogeneous (dimFl Ψ N + 1 - 2) := by
      have : dimFl Ψ N + 1 - 2 = dimFl Ψ N - 1 := by omega
      rwa [this]
    obtain ⟨E₁, hE₁, h₁⟩ := hid τ₀ 1 le_rfl (by omega) Q₁ hQ₁'
    obtain ⟨E₂, hE₂, h₂⟩ := hid τ₀ 2 (by omega) hN Q₂ hQ₂'
    have hn : ∑ σ, Tot σ (pk τ₀ 1 * Q₁) ≠ 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 1 Q₁ le_rfl).2
      simp only [h5, hd₁]
      simp
      omega
    have hs₂ : ∑ σ, Sh T.j σ (pk τ₀ 2 * Q₂) ≠ 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 2 Q₂ (by omega)).1
      simp only [h5]
      simp [hd₂]
    have ht₂ : ∑ σ, Tot σ (pk τ₀ 2 * Q₂) = 0 := by
      have h5 := fun σ => (GlobalTheory.T.flag_shift_total_power_sum Ψ N T.j τ₀ σ 2 Q₂ (by omega)).2
      simp [h5]
    obtain ⟨A₀, b₀, ha, hb⟩ := tendsto_coeffs_of_tests hvol.ne' hn hs₂ ht₂
      (hrest τ₀ 1 Q₁) (hrest τ₀ 2 Q₂) hE₁ hE₂ h₁ h₂
    refine ⟨A₀, b₀, fun τ k hk1 hkN Q hQ => ?_⟩
    obtain ⟨E, hE, h⟩ := hid τ k hk1 hkN Q hQ
    exact eq_of_tendsto_coeffs ha hb (hrest τ k Q) hE h
  · exact ⟨0, 0, fun τ => (hΨ ⟨τ⟩).elim⟩
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_identity_at_cutoff : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), T.Proportional → FrobShape frob → T.Prop6 II frob → T.ThmBA II hh → ∀ B₀ : ℕ, 2 ≤ B₀ → ∃ A₀ b₀ : ℝ, T.IdentAt II hh frob B₀ A₀ b₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.exists_identAt
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem restSum_total_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) :=
  RootFieldNumerics.rest_sum_total_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lin_root_remainder_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.restSum_total_bound
end

section
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem partialSum_sub_mean_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| :=
  RootFieldNumerics.partial_sum_ordered_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_partial_sum_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.partialSum_sub_mean_bounds
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem label_term_lower {A b K C' abelian₂ n j s t a : ℝ} (hn : 0 < n) (hK : 0 ≤ K) (hC : 0 ≤ C') (hL : 0 ≤ abelian₂)
    (hA : -(K * abelian₂) ≤ A) (hflat : |j * A + n * b| ≤ C' * n * abelian₂)
    (hc0 : 0 ≤ s - j * (t / n)) (hc1 : s - j * (t / n) ≤ a) (ht : |t| ≤ a) :
    -((K + C') * abelian₂ * a) ≤ A * s + b * t := by
  have hid : A * s + b * t = A * (s - j * (t / n)) + (j * A + n * b) * (t / n) := by
    field_simp
    ring
  have hKL : 0 ≤ K * abelian₂ := mul_nonneg hK hL
  have h1 : -(K * abelian₂ * a) ≤ A * (s - j * (t / n)) := by
    have e1 : -(K * abelian₂) * (s - j * (t / n)) ≤ A * (s - j * (t / n)) :=
      mul_le_mul_of_nonneg_right hA hc0
    have e2 : K * abelian₂ * (s - j * (t / n)) ≤ K * abelian₂ * a := mul_le_mul_of_nonneg_left hc1 hKL
    linarith
  have h2 : -(C' * abelian₂ * a) ≤ (j * A + n * b) * (t / n) := by
    have e0 : |(j * A + n * b) * (t / n)| ≤ C' * abelian₂ * a := by
      rw [abs_mul, abs_div, abs_of_pos hn]
      have e3 : |j * A + n * b| * (|t| / n) ≤ C' * n * abelian₂ * (|t| / n) :=
        mul_le_mul_of_nonneg_right hflat (div_nonneg (abs_nonneg _) hn.le)
      have e4 : C' * n * abelian₂ * (|t| / n) = C' * abelian₂ * |t| := by
        field_simp
      have e5 : C' * abelian₂ * |t| ≤ C' * abelian₂ * a := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hL)
      linarith
    exact (abs_le.mp e0).1
  rw [hid]
  nlinarith [h1, h2]

theorem linRoot_isHomogeneous {Ψ : Type} [Fintype Ψ] {N : ℕ} (u : Wt Ψ N) :
    (linRoot u : RP Ψ N).IsHomogeneous 1 := by
  unfold linRoot
  refine IsHomogeneous.neg ?_
  exact IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _

theorem spread_nonneg {Ψ : Type} [Fintype Ψ] {N : ℕ} (hN : 0 < N) (u : Wt Ψ N) : 0 ≤ spread u := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine Finset.sum_nonneg fun τ _ => ?_
  have i₀ : Fin N := ⟨0, hN⟩
  have h1 : u τ i₀ ≤ ⨆ i, u τ i := le_ciSup (Set.finite_range _).bddAbove i₀
  have h2 : (⨅ i, u τ i) ≤ u τ i₀ := ciInf_le (Set.finite_range _).bddBelow i₀
  linarith

theorem RegDominant.dominant' {Ψ : Type} {N : ℕ} {u : Wt Ψ N} (h : RegDominant u) : Dominant u := by
  intro τ a b hab
  rcases hab.lt_or_eq with h1 | h1
  · exact (h τ a b h1).le
  · rw [h1]

theorem tower_T2_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N)
    (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (K C' rd Lval : ℝ), 0 ≤ K → 0 ≤ C' → 1 ≤ rd →
    T.Proportional → FrobShape frob → I9 (Ψ := Ψ) (N := N) hh → T.Prop6 II frob → T.ThmBA II hh →
    T.PropF II C' rd Lval → T.LowerBoundAtBase II hh frob K rd Lval → T.T2 II (K + C' + 2) rd Lval := by
  intro II Ψ _ _ N T hh frob K C' rd Lval hK hC hrd hprop hshape hI9 hP6 hBA hF hA0 u g hW B hB128 hB0 hbad
  have hN2 : 2 ≤ N := by
    have := T.j_pos; have := T.j_lt; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have h0 : (linRoot u : RP Ψ N) = 0 := by simp [linRoot]
    have hPB : T.PB II B u = 0 := by
      simp [RootTower.PB, RootTower.PPt, RootTower.PPc, h0, toA]
    have hbr : T.bracket rd Lval B u = 0 := by
      simp [RootTower.bracket, l1, spread]
    rw [hPB, hbr]
    simp
  obtain ⟨hg, hreg, -, -⟩ := id hW
  have hdom : Dominant u := RegDominant.dominant' hreg

  have hfpos : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hBig : 4 * Fintype.card Ψ * N ^ 2 ≤ B := by
    have h1 : (4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2) ≤ bigB0 u g := by
      unfold bigB0
      have h2 : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hg.le
      have h3 : 0 ≤ 4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by positivity
      nlinarith
    have h4 : (4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2) < (B : ℝ) + 1 := lt_of_le_of_lt h1 hB0
    have h5 : 4 * Fintype.card Ψ * N ^ 2 < B + 1 := by exact_mod_cast h4
    omega
  obtain ⟨A₀, b₀, hId⟩ := GlobalTheory.T.tower_identity_at_cutoff II Ψ N T hh frob hprop hshape hP6 hBA B (by omega)
  have hAl := hA0 B A₀ b₀ hB128 hBig hbad hId
  have hfl := GlobalTheory.T.cutoff_coefficients_bound II Ψ N T hh frob C' rd Lval B A₀ b₀ hprop hI9 hF hB128 hbad hId
  have hHom : (linRoot u ^ (dimFl Ψ N + 1) : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
    simpa using (linRoot_isHomogeneous u).pow (dimFl Ψ N + 1)
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.homogeneous_power_sum_decomposition Ψ N _ hN2 hHom
  have hDec : IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q := ⟨hQ1, hQ2⟩
  have hEq := GlobalTheory.T.tower_height_identity_expansion II Ψ N T hh frob B A₀ b₀ _ Q hId hDec
  have hRest := GlobalTheory.T.lin_root_remainder_bound Ψ N T.j T.bad frob u g B Q T.j_pos T.j_lt hW hB0 hDec
  have hhF : 0 ≤ hh (linRoot u ^ (dimFl Ψ N + 1)) := hI9.2.1 u hdom
  have hdeg : 0 < flagDeg u := (GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl Ψ N u).2.1 hreg
  have hV : 0 < T.volT := Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hLam : 0 ≤ bigLam B rd Lval := by
    unfold bigLam
    have h1 : (1 : ℝ) ≤ (B : ℝ) * rd := by
      have : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      nlinarith
    have := Real.log_nonneg h1
    have := abs_nonneg Lval
    linarith
  set E : ℝ := ((dimFl Ψ N : ℝ) + 1) * flagDeg u with hE
  have hEpos : 0 < E := by positivity
  set abelian₂ := bigLam B rd Lval with hLamDef
  have hsum : -((K + C') * abelian₂ * l1 u) ≤
      ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) := by
    have : ∀ σ ∈ (Finset.univ : Finset Ψ), -((K + C') * abelian₂ * ∑ i, |u σ i|) ≤
        A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i := by
      intro σ _
      obtain ⟨l1', l2', l3'⟩ := GlobalTheory.T.dominant_partial_sum_bounds N T.j (u σ) T.j_lt.le (by omega) (fun a b h => hdom σ a b h)
      exact label_term_lower hNpos hK hC hLam hAl hfl l1' l2' l3'
    have h2 := Finset.sum_le_sum this
    have h3 : ∑ σ, -((K + C') * abelian₂ * ∑ i, |u σ i|) = -((K + C') * abelian₂ * l1 u) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rfl
    rwa [h3] at h2
  have hShTot : -(A₀ * ∑ σ, Sh T.j σ (linRoot u ^ (dimFl Ψ N + 1))) -
      b₀ * ∑ σ, Tot σ (linRoot u ^ (dimFl Ψ N + 1)) =
      E * ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) := by
    simp only [fun σ => (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N T.j σ u).1, fun σ => (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N T.j σ u).2]
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have hSpread : 0 ≤ ((min T.j (N - T.j) : ℕ) : ℝ) * spread u :=
    mul_nonneg (Nat.cast_nonneg _) (spread_nonneg (by omega) u)
  have hl1 : 0 ≤ l1 u := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hLl : 0 ≤ abelian₂ * l1 u := mul_nonneg hLam hl1
  set R := ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B τ k (Q τ k) with hR
  set Sp := ((min T.j (N - T.j) : ℕ) : ℝ) * spread u with hSp
  have hRl : -(2 * E * Sp) ≤ R := (abs_le.mp hRest).1
  have hinner : -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) ≤
      hh (linRoot u ^ (dimFl Ψ N + 1)) - A₀ * ∑ σ, Sh T.j σ (linRoot u ^ (dimFl Ψ N + 1)) -
        b₀ * ∑ σ, Tot σ (linRoot u ^ (dimFl Ψ N + 1)) + R := by
    have e1 : E * -((K + C') * abelian₂ * l1 u) ≤ E * ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) :=
      mul_le_mul_of_nonneg_left hsum hEpos.le
    rw [← hShTot] at e1
    have e2 : 0 ≤ E * (2 * (abelian₂ * l1 u)) := by positivity
    have e3 : 0 ≤ E * ((K + C') * Sp) := mul_nonneg hEpos.le (mul_nonneg (add_nonneg hK hC) hSpread)
    nlinarith [e1, e2, e3, hRl, hhF]
  have hfin : T.volT * -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) ≤ T.PB II B u := by
    have : T.PB II B u = T.PPt II B (linRoot u ^ (dimFl Ψ N + 1)) := rfl
    rw [this, hEq]
    exact mul_le_mul_of_nonneg_left hinner hV.le
  have hgoal : -((K + C' + 2) * ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) * T.bracket rd Lval B u) =
      T.volT * -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) := by
    simp only [RootTower.bracket, hE, hSp, hLamDef]
    ring
  rw [hgoal]
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T2 : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (K C' rd Lval : ℝ), 0 ≤ K → 0 ≤ C' → 1 ≤ rd → T.Proportional → FrobShape frob → I9 (Ψ := Ψ) (N := N) hh → T.Prop6 II frob → T.ThmBA II hh → T.PropF II C' rd Lval → T.LowerBoundAtBase II hh frob K rd Lval → T.T2 II (K + C' + 2) rd Lval := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs
end
