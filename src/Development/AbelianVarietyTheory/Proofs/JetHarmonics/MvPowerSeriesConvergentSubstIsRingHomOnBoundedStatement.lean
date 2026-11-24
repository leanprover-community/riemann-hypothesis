module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstIsRingHomOnBounded
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  first | exact @GlobalTheory.ConvSer.csub_ring_map | exact GlobalTheory.ConvSer.csub_ring_map | (intros; apply GlobalTheory.ConvSer.csub_ring_map <;> assumption)
