module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolume
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.hyperbolic_rank_one_global_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsGramFibFree (Ainf F) σ (hypOne J) 1 (coordW (Ainf F) b laminf 1 (M + 2)) (coordHerm (Ainf F) σ b laminf 1) minf → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsEulerProd b I 1 (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) → Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v)).toReal - 1|) ∧ ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v.1)).toReal) := by
  exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne.prim_formula
