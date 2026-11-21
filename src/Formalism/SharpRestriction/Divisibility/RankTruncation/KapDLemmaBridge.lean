import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal

section
noncomputable section

namespace ConditionalKappaBounds.KapD

def sigParC (k m : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (i : ℕ) : ℚ :=
  if h : i < k - 1 then v ⟨i, h⟩
  else if hb : i - (k - 1) < m then -b ⟨i - (k - 1), hb⟩ else 0

def aPlusC (k m t j : ℕ) (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (i : ℕ) : ℚ :=
  sigParC k m v b i + e - (((k + m - 1 + t : ℕ) : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((k : ℚ) + j - 1) - ((m : ℚ) - j)) / 2

def aMinusC (m t j : ℕ) (b : Fin m → ℚ) (e : ℚ) (c : ℕ) : ℚ :=
  (if h : j + c < m then b ⟨j + c, h⟩ else 0) - e - ((t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def DProp : Prop := ∃ C : ℝ, ∀ (k m t j : ℕ), m + 3 ≤ k → 1 ≤ j → j ≤ m →
  ∀ (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) (e : ℚ) (S η : ℝ),
    (∀ i, 0 ≤ ((v i : ℚ) : ℝ) ∧ ((v i : ℚ) : ℝ) ≤ S) → (∀ i, |((b i - e : ℚ) : ℝ)| ≤ η) →
    |((((∑ i : Fin (k + j - 1), aPlusC k m t j v b e i) + ∑ c : Fin (m - j), aMinusC m t j b e c : ℚ)) : ℝ) -
        ((k : ℝ) - 1) * ((e : ℚ) : ℝ)| ≤
      C * ((k : ℝ) * S + (m : ℝ) * η + (k : ℝ) * (((k + m * (t + 1) : ℕ) : ℝ) + t))

end ConditionalKappaBounds.KapD
end
end

section
namespace ConditionalKappaBounds.KapD

open Formalism.BasicNotions Formalism.MainNotions

theorem kappa_bound_of_prop (hc : DProp) : ∃ C : ℝ, ∀ (D : D7) (L : SizeData₂ D), LiftErrorLocal.ThetaAdjointPositiveScalar D L C := by
  obtain ⟨C, hC⟩ := hc
  refine ⟨C, fun D L hK j hj => ?_⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  have hjm : j - 1 < D.R.m := by omega
  have key : ∀ τ : D.what₂.Tau,
      |((((∑ a, D.what₂.kaBig j τ a) - ∑ a, D.what₂.kaSmall j τ a : ℤ)) : ℝ) - ((D.R.k : ℝ) - 1) * wj D j τ| ≤
        C * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz +
          (D.R.k : ℝ) * (((D.R.k + D.R.m * (D.R.t + 1) : ℕ) : ℝ) + D.R.t)) := by
    intro τ
    have h := hC D.R.k D.R.m D.R.t j D.R.m_add_three_le_k hj1 hj2 (D.hc τ).v (D.hc τ).b
      ((D.hc τ).e ⟨j - 1, hjm⟩) L.Sc L.etaSz (fun i => L.cloud_v τ i) (fun i => L.be_close τ i ⟨j - 1, hjm⟩)
    have hK' := hK j hj1 hj2 τ
    have e1 : (((∑ a, D.what₂.kaBig j τ a : ℤ)) : ℚ) =
        ∑ i : Fin (D.R.k + j - 1), aPlusC D.R.k D.R.m D.R.t j (D.hc τ).v (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) i := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hK'.1 i]
      unfold DV.aPlusQ DV.eQ aPlusC
      rw [dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨hj1, hj2⟩)]
      rfl
    have e2 : (((∑ a, D.what₂.kaSmall j τ a : ℤ)) : ℚ) =
        -∑ c : Fin (D.R.m - j), aMinusC D.R.m D.R.t j (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) c := by
      push_cast
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hK'.2 c]
      unfold DV.aMinusQ DV.eQ aMinusC
      rw [dif_pos (show 1 ≤ j ∧ j ≤ D.R.m from ⟨hj1, hj2⟩)]
    have ew : wj D j τ = (((D.hc τ).e ⟨j - 1, hjm⟩ : ℚ) : ℝ) := by
      unfold wj
      rw [dif_pos hjm]
    have eZ : (((((∑ a, D.what₂.kaBig j τ a) - ∑ a, D.what₂.kaSmall j τ a : ℤ)) : ℝ)) =
        ((((∑ i : Fin (D.R.k + j - 1), aPlusC D.R.k D.R.m D.R.t j (D.hc τ).v (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) i) +
          ∑ c : Fin (D.R.m - j), aMinusC D.R.m D.R.t j (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) c : ℚ)) : ℝ) := by
      have : ((((∑ a, D.what₂.kaBig j τ a) - ∑ a, D.what₂.kaSmall j τ a : ℤ)) : ℚ) =
          (∑ i : Fin (D.R.k + j - 1), aPlusC D.R.k D.R.m D.R.t j (D.hc τ).v (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) i) +
          ∑ c : Fin (D.R.m - j), aMinusC D.R.m D.R.t j (D.hc τ).b ((D.hc τ).e ⟨j - 1, hjm⟩) c := by
        push_cast at e1 e2 ⊢
        rw [e1, e2]; ring
      rw [← this]; push_cast; rfl
    rw [eZ, ew]
    exact h
  have hsum := Finset.abs_sum_le_sum_abs
    (fun τ : D.what₂.Tau => ((((∑ a, D.what₂.kaBig j τ a) - ∑ a, D.what₂.kaSmall j τ a : ℤ)) : ℝ) -
      ((D.R.k : ℝ) - 1) * wj D j τ) Finset.univ
  have hle := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.univ) => key τ)
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hle
  unfold LiftErrorLocal.Dpm
  rw [Int.cast_sum, ← Finset.sum_sub_distrib]
  refine (hsum.trans hle).trans (le_of_eq ?_)
  simp only [Ranks.N]
  push_cast
  ring

end ConditionalKappaBounds.KapD
end
