import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import BuildAid.ForwardExisting

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_of_asymptotic_bounds : ∀ (f : ℕ → ℝ) (G : ℝ) (D : ℕ), (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n) → (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) → Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds
