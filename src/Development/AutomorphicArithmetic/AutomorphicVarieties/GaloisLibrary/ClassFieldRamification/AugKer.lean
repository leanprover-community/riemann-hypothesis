module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.augKer :
    ∀ (R G : Type) [CommRing R] [CommGroup G], RingHom.ker (aug R G) = augIdeal R G ∧ Function.Surjective (aug R G) := by
  intro R G _ _
  have key : ∀ x : MonoidAlgebra R G,
      x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
    | single g r =>
      rw [aug_single]
      have h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r =
          MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1) := by
        rw [mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul,
          mul_one, MonoidAlgebra.coe_algebraMap]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have := key x
    rwa [RingHom.mem_ker.mp hx, map_zero, sub_zero] at this
  · rw [augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single,
      sub_self]
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩
