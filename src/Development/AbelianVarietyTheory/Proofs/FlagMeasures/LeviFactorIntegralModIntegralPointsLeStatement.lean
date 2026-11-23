module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorIntegralModIntegralPointsLe
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.levi_factor_integral_mod_integral_points_le : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∀ F : (Fin a → ℝ) → ENNReal, Measurable F → covol (leviGroup I xf S) ((Measure.pi μM).withDensity fun m => F (sizesAt I xf S m)) {m | ∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)} ≤ (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i) := by
  first | exact @GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le | exact GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le | (intros; apply GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le <;> assumption)
