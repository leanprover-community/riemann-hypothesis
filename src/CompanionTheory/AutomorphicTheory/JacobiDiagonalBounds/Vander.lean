module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

theorem vander' (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ,
      V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ) := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩
  beta_reduce
  have hrow : ∀ j : Fin (Q + 1),
      ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j := by
    intro j
    rw [← hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hV, Matrix.vandermonde_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end Formalism.FourierDecayAlt.P.NormalFormRelations
