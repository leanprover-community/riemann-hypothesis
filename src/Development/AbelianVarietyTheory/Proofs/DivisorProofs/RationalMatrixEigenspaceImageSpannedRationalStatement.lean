module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRational
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

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  first | exact @GlobalTheory.rational_eigen_image_span | exact GlobalTheory.rational_eigen_image_span | (intros; apply GlobalTheory.rational_eigen_image_span <;> assumption)
