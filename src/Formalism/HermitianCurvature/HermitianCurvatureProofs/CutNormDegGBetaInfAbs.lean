import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Formalism.FourierDecayAlt.B

section Gen

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def bxi (la la' : X → ℝ) (τ : ℝ × ℝ) (p : X) : ℂ :=
  Complex.exp (Complex.I * ((τ.1 * la p - τ.2 * la' p : ℝ) : ℂ))




def bg (μ : Measure X) (la la' : X → ℝ) (Φ : X → ℂ) (τ : ℝ × ℝ) : ℂ := ∫ p, bxi la la' τ p * Φ p ∂μ



theorem test_integrable {w : ℝ → ℝ} (h : IsTest w) : Integrable w :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1







end Gen

section HidaSetting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem inCC_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E}
    (hF : InCC A 5 F) : InCC A 4 F := by
  obtain ⟨c, hck, hb⟩ := hF
  exact ⟨c, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)) hck,
    fun u v hu hv hl g hg => hb u v hu hv (le_trans hl (by norm_num)) g hg⟩



end HidaSetting

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
