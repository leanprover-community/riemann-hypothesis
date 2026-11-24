module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.skew_hermitian_unitary_flow : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y → ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | exact GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve <;> assumption)
