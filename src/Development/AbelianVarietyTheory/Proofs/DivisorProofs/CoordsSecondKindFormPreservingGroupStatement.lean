module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
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

@[expose] public section

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.coordsSecondKind_formPreservingGroup : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ) (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ), (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧ ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1, X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  first | exact @GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | exact GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | (intros; apply GlobalTheory.ClosedMatGroup.coords_second_kind_unitary <;> assumption)
