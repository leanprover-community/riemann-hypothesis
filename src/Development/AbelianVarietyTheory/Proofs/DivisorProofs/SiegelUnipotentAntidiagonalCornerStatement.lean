module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCorner
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open GlobalTheory.WeilM
open scoped Matrix

theorem _root_.GlobalTheory.T.siegelUnipotent_antidiagonal_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  first | exact @GlobalTheory.siegel_unip_corner | exact GlobalTheory.siegel_unip_corner | (intros; apply GlobalTheory.siegel_unip_corner <;> assumption)
