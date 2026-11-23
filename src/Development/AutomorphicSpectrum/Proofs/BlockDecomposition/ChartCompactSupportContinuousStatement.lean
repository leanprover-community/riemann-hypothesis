module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.chart_compact_support_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart <;> assumption)
