module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

noncomputable def twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.lift K (MonoidAlgebra K H) H
    { toFun := fun h => MonoidAlgebra.single h (((χ (h : Γ))⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := by
        intro a b
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twistAlg_single {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) (h : H) (c : K) :
    twistAlg H χ (MonoidAlgebra.single h c) = MonoidAlgebra.single h (c * (((χ (h : Γ))⁻¹ : Kˣ) : K)) := by
  simp [twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]

theorem twistAlg_inv_twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ)
    (x : MonoidAlgebra K H) : twistAlg H χ⁻¹ (twistAlg H χ x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    simp only [MonoidAlgebra.of_apply, twistAlg_single]
    congr 1
    simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | smul r x hx => simp [map_smul, hx]

theorem twistAlg_injective {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    Function.Injective (twistAlg H χ) := fun x y hxy => by
  rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]

theorem embReg_twist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V)
    (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩
  refine ⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩
  · intro v w hvw
    apply hj
    funext i
    have := congrFun hvw i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply] at this
    exact twistAlg_injective H χ this
  · intro h v i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply]
    rw [hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc,
      MonoidAlgebra.smul_single]
    congr 2
    simp

end GlobalTheory.BadCount
