module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneVolumeBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

theorem _root_.GlobalTheory.T.archimedean_rank_one_volume_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → (∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U) → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ IsCompact {X : Fin 1 → Fin M → Ainf F ⊗[F] E | (fun w => xw e b X w) ∈ coreR δ R} ∧ ∀ A : Set (HermR (Ainf F) σ 1), MeasurableSet A → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) ∩ {X | (fun w => xw e b X w) ∈ coreR δ R}ᶜ, ENNReal.ofReal (φ X) ∂μ ≤ ENNReal.ofReal ε * ν A := by
  exact @GlobalTheory.CompanionTheory.SW.BB.InfTransport.smallDensity_transport
