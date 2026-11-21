import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_analytic_data_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | exact GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists <;> assumption)
end

section
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ConjOf

theorem flagAn_exists_conj : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) :=
  fun hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM hA hd h1 h2 =>
    flagAn_conj K ι Φ y Ψ N j M n d BM (GlobalTheory.T.flag_model_analytic_data_exists hI K ι Φ y Ψ N j M n d BM hA hd) h1 h2

end GlobalTheory.CompanionTheory.Ar.PB.ConjOf
end

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_arith_dimension_boundary : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj
end
