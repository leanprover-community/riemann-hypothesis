module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrame
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem _root_.GlobalTheory.T.global_unitary_moves_isotropic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 <;> assumption)
