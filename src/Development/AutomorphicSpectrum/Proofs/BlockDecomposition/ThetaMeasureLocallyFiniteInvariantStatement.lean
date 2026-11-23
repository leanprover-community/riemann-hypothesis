module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariant
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.theta_measure_locally_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero <;> assumption)
