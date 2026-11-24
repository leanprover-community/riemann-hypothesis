module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
