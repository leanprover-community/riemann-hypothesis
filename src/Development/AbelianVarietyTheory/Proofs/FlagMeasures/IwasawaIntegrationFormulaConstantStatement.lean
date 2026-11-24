module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.iwasawa_integration_formula_constant : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∀ (c : ℝ) (κ : ENNReal), IsGauge ε c → (∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN) → ENNReal.ofReal c * κ = ENNReal.ofReal (cIw p q j) := by
  first | exact @GlobalTheory.IwConst.iwasawa_constant | exact GlobalTheory.IwConst.iwasawa_constant | (intros; apply GlobalTheory.IwConst.iwasawa_constant <;> assumption)
