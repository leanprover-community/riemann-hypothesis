import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

section
namespace Formalism.LatticeBaseChangeAlt


theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith





end Formalism.LatticeBaseChangeAlt
end

section
namespace Formalism.LatticeBaseChangeAlt

open Finset

theorem levelsSum : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring

noncomputable def slackEquiv (D k : ℕ) :
    {α : Fin D → ℕ // ∑ i, α i ≤ k} ≃ {β : Fin (D + 1) → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.1 i) α.1, by
    have := α.2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun β := ⟨Fin.tail β.1, by
    have := β.2
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    simp only [Fin.tail_cons]
  right_inv β := by
    apply Subtype.ext
    have h := β.2
    rw [Fin.sum_univ_succ] at h
    have h0 : k - ∑ i, Fin.tail β.1 i = β.1 0 := by
      simp only [Fin.tail]
      omega
    simp only [h0, Fin.cons_self_tail]

end Formalism.LatticeBaseChangeAlt
end

section
namespace Formalism.LatticeBaseChangeAlt

open Module


theorem levelsChain : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith

end Formalism.LatticeBaseChangeAlt
end
