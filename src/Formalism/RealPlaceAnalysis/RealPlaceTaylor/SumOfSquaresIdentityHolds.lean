module

public import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section WDA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}

lemma WDA_sgn_symm (ε : Fin n → Bool) (a b : Fin n) : sgn ε a b = sgn ε b a := by
  unfold sgn; simp only [eq_comm]

lemma WDA_norm (hU : IsUnitary ε E) (a b : Fin n) (x : V) :
    (((‖E a b x‖ ^ 2 : ℝ)) : ℂ) = (sgn ε a b : ℂ) * ⟪x, E b a (E a b x)⟫_ℂ := by
  rw [Complex.ofReal_pow, ← hU a b x (E a b x)]
  exact (inner_self_eq_norm_sq_to_K (E a b x)).symm

lemma WDA_op (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    (2 • CasK ε E - Cas E) = ∑ a, ∑ b, ((sgn ε a b : ℂ)) • (E a b * E b a) := by
  simp only [CasK, Cas, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  unfold sgn
  split_ifs with h
  · simp [two_smul]
  · simp

end WDA

section WDA2

theorem sumOfSquaresIdentity_holds : SumSq := by
  intro V _ _ n ε E w hU
  rw [WDA_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    inner_sum, inner_smul_right]
  simp only [Complex.ofReal_sum]
  simp only [WDA_norm hU]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [WDA_sgn_symm]

end WDA2

end Formalism.REAL
