import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
import BuildAid.ForwardExisting

section
namespace GlobalTheory

theorem qBinomial_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (X : ℂ),
    ∑ j ∈ Finset.range (Module.finrank k V + 1),
        (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) *
          (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j =
      ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  intro k V _ _ _ _ _ X
  simp only [GlobalTheory.GaussCount.card_codim]
  exact GlobalTheory.GaussCount.gauss_formula (Nat.card k) ℂ X (Module.finrank k V)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qBinomial_sum_card_quotient_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : ℂ), ∑ j ∈ Finset.range (Module.finrank k V + 1), (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j = ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  atlas_forward_decl GlobalTheory.qBinomial_subspaces
