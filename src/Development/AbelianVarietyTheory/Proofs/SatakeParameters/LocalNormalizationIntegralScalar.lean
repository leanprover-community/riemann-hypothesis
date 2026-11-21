import Mathlib
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
import BuildAid.ForwardExisting

section
namespace GlobalTheory

open Formalism.L2.AlgTh

theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  atlas_forward_decl GlobalTheory.locNormScale
