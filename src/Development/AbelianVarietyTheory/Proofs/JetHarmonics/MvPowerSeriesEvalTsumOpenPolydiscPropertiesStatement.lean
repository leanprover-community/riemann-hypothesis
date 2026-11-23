module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscProperties
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

theorem _root_.GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  first | exact @GlobalTheory.ConvSer.ev_algebra | exact GlobalTheory.ConvSer.ev_algebra | (intros; apply GlobalTheory.ConvSer.ev_algebra <;> assumption)
