module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRowsLinearIndependent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace SplitLinear

open Matrix Module

universe u

variable {K : Type*} [Field K]

theorem exists_rows_linearIndependent {r : Type u} {c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ I : Fin k → r, LinearIndependent K (fun p => P (I p)) :=
  _root_.UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent P hk

theorem exists_minor_ne_zero {r c : Type*} [Fintype r] [Fintype c] (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ (I : Fin k → r) (J : Fin k → c), (P.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows_linearIndependent P hk
  set N : Matrix (Fin k) c K := P.submatrix I id with hNdef
  have hN : N.rank = k := by
    have := LinearIndependent.rank_matrix (M := N) hI
    simpa using this
  have hNt : k ≤ Nᵀ.rank := by rw [rank_transpose, hN]
  obtain ⟨J, hJ⟩ := exists_rows_linearIndependent Nᵀ hNt
  refine ⟨I, J, ?_⟩
  have hQ : IsUnit (Nᵀ.submatrix J id) := linearIndependent_rows_iff_isUnit.1 hJ
  have e : P.submatrix I J = (Nᵀ.submatrix J id)ᵀ := by ext p q; rfl
  rw [e, det_transpose]
  exact ((isUnit_iff_isUnit_det _).1 hQ).ne_zero

end SplitLinear

end GroundTheory.Heights₂.Theta
