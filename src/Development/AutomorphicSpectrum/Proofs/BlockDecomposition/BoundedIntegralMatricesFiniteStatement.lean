module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFinite
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.bounded_integral_matrices_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | exact GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | (intros; apply GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite <;> assumption)
