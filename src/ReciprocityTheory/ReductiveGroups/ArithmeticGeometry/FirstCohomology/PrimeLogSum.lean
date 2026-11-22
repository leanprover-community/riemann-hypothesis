module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.H1

lemma primeLogSum_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
  have h : Finset.Iic N = Finset.range (N + 1) := by ext; simp [Nat.lt_succ_iff]
  rw [h]
  exact GlobalTheory.PrimeLogSum.sum_log_div_pred_le N

end ReciprocityTheory.ChartRestriction.G.H1
