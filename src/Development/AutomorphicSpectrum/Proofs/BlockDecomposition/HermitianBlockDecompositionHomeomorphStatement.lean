module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.hermitian_block_decomposition_homeomorph : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit <;> assumption)
