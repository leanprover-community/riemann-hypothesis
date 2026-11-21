import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.BrExistsSqInv
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_lamConj_eq (hU : UniqInv) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (Λ Λ₀ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : discr Λ = 1)
    (h0 : discr Λ₀ ≠ 0) (hjM : jL Λ ∈ M) (hj : ρ ⟨jL Λ, hjM⟩ = jL Λ₀) :
    ∃ c : ℂ, c ≠ 0 ∧ lamConj M ρ Λ = c • Λ₀ ∧ discr (c • Λ₀) = 1 := by
  set a : ℂ := ρ ⟨g2 Λ, h2⟩ with ha
  set b : ℂ := ρ ⟨g3 Λ, h3⟩ with hb
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab1 : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [ha, hb, ← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  have hjL : (⟨jL Λ, hjM⟩ : M) = 1728 * (⟨g2 Λ, h2⟩ : M) ^ 3 := by
    apply M.val.injective
    rw [map_mul, map_pow, map_ofNat]
    show jL Λ = 1728 * g2 Λ ^ 3
    rw [br_jL_eq, h1, div_one]
  have hj' : 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) = jL Λ₀ := by
    rw [hab1, div_one, ← hj, hjL, map_mul, map_pow, map_ofNat]
  obtain ⟨c, hc0, hc2, hc3⟩ := br_exists_scale Λ₀ h0 a b (by rw [hab1]; exact one_ne_zero) hj'
  have hd1 : discr (c • Λ₀) = 1 := by
    show g2 (c • Λ₀) ^ 3 - 27 * g3 (c • Λ₀) ^ 2 = 1
    rw [hc2, hc3, hab1]
  have hl2 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hex : ∃ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ)) ∧
      Formalism.MainNotions.TaylorLogMetric.g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ)) :=
    ⟨c • Λ₀, by rw [hl2]; exact hc2, by rw [hl3]; exact hc3⟩
  have hspec := Classical.epsilon_spec hex
  have hs2 : Formalism.MainNotions.TaylorLogMetric.g2 (lamConj M ρ Λ) = a := by
    exact hspec.1.trans (by rw [hl2])
  have hs3 : Formalism.MainNotions.TaylorLogMetric.g3 (lamConj M ρ Λ) = b := by
    exact hspec.2.trans (by rw [hl3])
  refine ⟨c, hc0, ?_, hd1⟩
  symm
  apply hU
  · show discr (c • Λ₀) ≠ 0
    rw [hd1]; exact one_ne_zero
  · rw [hs2]; exact hc2
  · rw [hs3]; exact hc3

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem brcc_discr_one_ne (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    discr (lamOf D cc 1) ≠ 0 :=
  discr_latI_ne_zero D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc hcc

theorem brcc_delta_ne (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  intro h0
  have hcc' := hcc
  obtain ⟨hcc0, -⟩ := hcc'
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  apply brcc_discr_one_ne D cc hcc0
  rw [← h12, h0]
  norm_num

private lemma lamOf_eq_map_mulLeft (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    lamOf D cc δ = (lamOf D cc 1).map (AddMonoidHom.mulLeft δ) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, by simp⟩
  · rintro ⟨v, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, by simp⟩

private lemma eisG_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    Formalism.MainNotions.TaylorLogMetric.eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * Formalism.MainNotions.TaylorLogMetric.eisG Λ k := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    (Equiv.mulLeft₀ δ hδ).subtypeEquiv (fun w => by
      show (w ∈ Λ ∧ w ≠ 0) ↔ (δ * w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ δ * w ≠ 0)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨AddSubgroup.mem_map.2 ⟨w, h1, rfl⟩, mul_ne_zero hδ h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨v, hv, hvw⟩ := AddSubgroup.mem_map.1 h1
        have hvw' : δ * v = δ * w := hvw
        have hv' : v = w := mul_left_cancel₀ hδ hvw'
        rw [hv'] at hv
        exact ⟨hv, right_ne_zero_of_mul h2⟩)
  unfold Formalism.MainNotions.TaylorLogMetric.eisG
  refine (e.tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm.trans ?_
  rw [← tsum_mul_left]
  congr 1
  funext w
  show 1 / (δ * (w : ℂ)) ^ (2 * k) = (δ ^ (2 * k))⁻¹ * (1 / (w : ℂ) ^ (2 * k))
  rw [mul_pow, one_div, one_div, mul_inv]

private lemma g2_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.g2 (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 4)⁻¹ * Formalism.MainNotions.TaylorLogMetric.g2 Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.g2
  rw [eisG_map_mulLeft Λ δ hδ]
  ring

private lemma g3_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.g3 (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 6)⁻¹ * Formalism.MainNotions.TaylorLogMetric.g3 Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.g3
  rw [eisG_map_mulLeft Λ δ hδ]
  ring

private lemma discr_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * Formalism.MainNotions.TaylorLogMetric.discr Λ := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr
  rw [g2_map_mulLeft Λ δ hδ, g3_map_mulLeft Λ δ hδ]
  ring

theorem br_discr_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : discr (lamOf D cc δ) = 1 := by
  have hne : δ ≠ 0 := brcc_delta_ne D cc hcc δ hδ
  have h12 : δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc 1) := hδ
  show Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1
  rw [lamOf_eq_map_mulLeft D cc δ, discr_map_mulLeft _ δ hne, ← h12]
  exact inv_mul_cancel₀ (pow_ne_zero _ hne)

private lemma jL_map_mulLeft (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    jL (Λ.map (AddMonoidHom.mulLeft δ)) = jL Λ := by
  unfold jL
  rw [g2_map_mulLeft Λ δ hδ, discr_map_mulLeft Λ δ hδ]
  have h : (δ ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hδ)
  rw [show (1728 : ℂ) * ((δ ^ 4)⁻¹ * Formalism.MainNotions.TaylorLogMetric.g2 Λ) ^ 3
      = (δ ^ 12)⁻¹ * (1728 * Formalism.MainNotions.TaylorLogMetric.g2 Λ ^ 3) by ring]
  exact mul_div_mul_left _ _ h

theorem brcc_jL_delta (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : jL (lamOf D cc 1) = jL (lamOf D cc δ) := by
  have hne : δ ≠ 0 := brcc_delta_ne D cc hcc δ hδ
  rw [lamOf_eq_map_mulLeft D cc δ, jL_map_mulLeft _ δ hne]

theorem br_jL_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (M : IntermediateField ℚ ℂ) (hM : DataIn D (tor0 D cc δ) M) :
    jL (lamOf D cc 1) ∈ M := by
  rw [brcc_jL_delta D cc hcc δ hδ]
  have hd : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := br_discr_lamOf D cc hcc δ hδ
  obtain ⟨-, hg, -⟩ := hM
  have hg' : Formalism.MainNotions.TaylorLogMetric.g2 (lamOf D cc δ) ∈ M := hg
  have hj : jL (lamOf D cc δ) = 1728 * Formalism.MainNotions.TaylorLogMetric.g2 (lamOf D cc δ) ^ 3 := by
    unfold jL
    rw [hd, div_one]
  rw [hj]
  exact mul_mem (by simpa using natCast_mem M 1728) (pow_mem hg' 3)

private lemma discr_eq_zero_of_trivial (Λ : AddSubgroup ℂ) (h : ∀ w ∈ Λ, w = 0) :
    Formalism.MainNotions.TaylorLogMetric.discr Λ = 0 := by
  have he : ∀ k, Formalism.MainNotions.TaylorLogMetric.eisG Λ k = 0 := by
    intro k
    unfold Formalism.MainNotions.TaylorLogMetric.eisG
    haveI : IsEmpty {w : ℂ // w ∈ Λ ∧ w ≠ 0} := ⟨fun x => x.2.2 (h x.1 x.2.1)⟩
    exact tsum_empty
  simp [Formalism.MainNotions.TaylorLogMetric.discr, Formalism.MainNotions.TaylorLogMetric.g2, Formalism.MainNotions.TaylorLogMetric.g3, he]

theorem brcc_discr_delta_ne (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (𝔟 : Ideal (𝓞 K))
    (δ : ℂ) (h : discr (latI φ 𝔟 δ) = 1) : δ ≠ 0 := by
  intro h0
  subst h0
  have hS : {w : ℂ | ∃ c ∈ 𝔟, w = 0 * φ (c : K)} ⊆ ((⊥ : AddSubgroup ℂ) : Set ℂ) := by
    rintro w ⟨c, hc, rfl⟩
    simp
  have hz : Formalism.MainNotions.TaylorLogMetric.discr (latI φ 𝔟 0) = 0 :=
    discr_eq_zero_of_trivial _ (fun w hw => AddSubgroup.mem_bot.1 ((AddSubgroup.closure_le _).2 hS hw))
  have h' : Formalism.MainNotions.TaylorLogMetric.discr (latI φ 𝔟 0) = 1 := h
  rw [hz] at h'
  exact zero_ne_one h'

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end
