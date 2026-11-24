module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
