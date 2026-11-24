module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesForm
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.archimedean_matrix_preserves_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary | exact GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary <;> assumption)
