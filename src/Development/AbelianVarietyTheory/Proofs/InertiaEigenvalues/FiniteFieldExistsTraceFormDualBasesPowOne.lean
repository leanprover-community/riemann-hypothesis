module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.ZMod.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

namespace GlobalTheory

theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
