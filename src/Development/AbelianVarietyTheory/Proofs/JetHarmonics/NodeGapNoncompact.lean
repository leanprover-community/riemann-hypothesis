import Mathlib
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps

namespace GlobalTheory.Proof.NodeGapNoncompact

open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem lam_eq (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    lam48 k r v b = param r k hk v b := by
  funext s
  unfold lam48
  by_cases h : s.val < k - 1
  · rw [dif_pos h]
    exact (param_cloud r k hk v b ⟨s.val, h⟩).symm
  · rw [dif_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, param_node]

theorem sign_eq (k r : ℕ) (hk : 1 ≤ k) : eps48 k r = sign r k hk := by
  funext s
  unfold eps48
  by_cases h : s.val < k - 1
  · rw [if_pos h]
    exact (sign_cloud r k hk ⟨s.val, h⟩).symm
  · rw [if_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, sign_node]
    simp only [Nat.even_iff]

theorem interlace_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by
  have hc : ∀ (i : ℕ) (hi : i < k - 1) (hi' : i < 2 * r + k + 1),
      param r k hk v b ⟨i, hi'⟩ = v ⟨i, hi⟩ := fun i hi _ => param_cloud r k hk v b ⟨i, hi⟩
  have hn : ∀ (hi' : k - 1 < 2 * r + k + 1),
      param r k hk v b ⟨k - 1, hi'⟩ = -b ⟨0, by omega⟩ :=
    fun _ => param_node r k hk v b ⟨0, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i.val < k - 1
      · rw [hc i.val h]
        exact (h1 ⟨i.val, h⟩).1
      · obtain ⟨i, hi⟩ := i
        obtain rfl : i = k - 1 := by simp only at h; omega
        rw [hn]
        exact h2 hk
    · rw [hc i (by omega)]
      exact (h1 ⟨i, by omega⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
    · have := h1 ⟨i.val, by have := i.isLt; omega⟩
      rwa [hc i.val i.isLt] at this
    · have := h2 i.val (by have := i.isLt; omega)
      rwa [hc i.val i.isLt] at this
    · have := h1 ⟨k - 1, by omega⟩
      rwa [hn] at this


theorem gap_iff (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) :
    LowGapGe h r b ↔ NodeGapGe r b h := by
  constructor
  · intro H i hi
    have := H ⟨i, by omega⟩ hi
    simp only at this
    linarith
  · intro H j hj
    have := H j.val hj
    simp only [Fin.eta] at this
    linarith



theorem isHCParam_iff (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ↔
      IsDecreasing r k hk v b ∧ IsShiftedIntegral (param r k hk v b) := by
  unfold Formalism.QuantumDeterminants.IsHCParam IsDecreasing IsShiftedIntegral
  rw [lam_eq k r hk]
  refine and_congr Iff.rfl (forall_congr' fun s => exists_congr fun z => ?_)
  constructor <;> intro h <;> linarith



end GlobalTheory.Proof.NodeGapNoncompact
