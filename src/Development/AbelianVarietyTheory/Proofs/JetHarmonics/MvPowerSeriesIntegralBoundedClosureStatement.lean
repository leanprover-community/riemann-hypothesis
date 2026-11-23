module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeries_integral_bounded_closure : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type), (∀ S T : MvPowerSeries σ K, Intg S → Intg T → Intg (S + T) ∧ Intg (S - T) ∧ Intg (S * T)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → Bdd (S + T) ∧ Bdd (S - T) ∧ Bdd (S * T)) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), (Intg S → Intg (S ^ n)) ∧ (Bdd S → Bdd (S ^ n)) ∧ (Intg S → Bdd S)) ∧ (∀ a : K, Bdd (MvPowerSeries.C a : MvPowerSeries σ K) ∧ (‖a‖ ≤ 1 → Intg (MvPowerSeries.C a : MvPowerSeries σ K)) ∧ (‖a‖ < 1 → Small (MvPowerSeries.C a : MvPowerSeries σ K))) ∧ (∀ i : σ, Small (MvPowerSeries.X i : MvPowerSeries σ K)) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), ((∀ i ∈ t, Intg (f i)) → Intg (∏ i ∈ t, f i) ∧ Intg (∑ i ∈ t, f i)) ∧ ((∀ i ∈ t, Bdd (f i)) → Bdd (∏ i ∈ t, f i) ∧ Bdd (∑ i ∈ t, f i))) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (Intg S → Intg (MvPowerSeries.subst a S)) ∧ (Bdd S → Bdd (MvPowerSeries.subst a S))) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → (Intg f → Intg (f.subst a)) ∧ (Bdd f → Bdd (f.subst a))) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A)) ∧ (∀ f : PowerSeries K, (Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) ∧ (Bdd f ↔ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)) := by
  first | exact @GlobalTheory.BddAlg.bdd_alg | exact GlobalTheory.BddAlg.bdd_alg | (intros; apply GlobalTheory.BddAlg.bdd_alg <;> assumption)
