module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add (f := _), map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
