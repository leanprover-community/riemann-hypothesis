module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearMapOfTraceEq
public import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace GlobalTheory.TraceFormNondegenerate

theorem eq_zero_of_trace_mul {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ Y : Matrix (Fin n) (Fin n) K, Matrix.trace (X * Y) = 0) : X = 0 := by
  ext i j
  have hij := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at hij
  simpa using hij

theorem span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K)
    (htr : ∀ g : Γ, Matrix.trace (M g) = Matrix.trace (N g))
    (hN : Submodule.span K (Set.range (⇑N : Γ → Matrix (Fin n) (Fin n) K)) = ⊤) :
    Submodule.span K (Set.range (⇑M : Γ → Matrix (Fin n) (Fin n) K)) = ⊤ := by
  apply GlobalTheory.TraceConj.span_top_of_trace_eq <;> assumption

end GlobalTheory.TraceFormNondegenerate
