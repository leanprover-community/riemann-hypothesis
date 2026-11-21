import Formalism.HermitianCurvature.OrbitalIntegralDiagonalSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityLemmaOfReductions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdOfLargeConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitriangularEqOneOfMinorsNonzero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerDensityOfAveraging
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragingVanishes

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.FourierDecayAlt.DensityAveraging Formalism.FourierDecayAlt.OrbitalSlices

theorem norm_eq_of_pow_eq_same {s : ℕ} (hs : 0 < s) {a z z₀ : ℂ} (hz : z ^ s = a) (hz₀ : z₀ ^ s = a) : ‖z‖ = ‖z₀‖ := by
  have h : ‖z‖ ^ s = ‖z₀‖ ^ s := by rw [← norm_pow, ← norm_pow, hz, hz₀]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hs.ne').mp h

theorem mem_rootSet_iff_pow_eq {s : ℕ} (hs : 0 < s) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots hs]

theorem germ_leading_term_root_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Ψ : G.Mat (m + 1 + 1) → V) (t Dd z₀ : ℂ) (hz₀ : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd) :
    G.mainTerm β m (fun _ => 1) Ψ t Dd =
      (((m : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ)) •
        ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dd), G.psi β (((m : ℂ) + 2) * z / t) • G.OmLong β (m + 1) Ψ z := by
  unfold G.mainTerm
  rw [mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [mem_rootSet_iff_pow_eq (by omega)] at hz
  rw [norm_eq_of_pow_eq_same (by omega) hz hz₀, mul_one, mul_smul]

def germDecayRateAt (C₁ C₂ : ℕ) : Prop :=
  ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ Cst : ℝ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
      (Φ : G.Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ),
      (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A → C₂ * (m + 2) ^ 2 ≤ k →
      G.DerivBound k (G.detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc → ‖G.remainder β m (fun _ => 1) Φ t c‖ ≤ Cst * K * ‖t‖







def slicePointInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.OrbitalSlices.SlicePt D F' γ where
  m := 0
  β := 1
  β_ne := one_ne_zero
  Dd := -1
  Dd_ne := by norm_num
  z₀ := 1
  z₀_pow := by norm_num
  Ψ := fun _ => 0
  pt := fun _ _ => γ
  δ := 1
  δ_pos := one_pos

end Formalism.FourierDecayAlt.P
