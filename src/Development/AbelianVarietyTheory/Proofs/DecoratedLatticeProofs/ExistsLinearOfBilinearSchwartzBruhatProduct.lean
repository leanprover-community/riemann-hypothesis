module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodSBBil (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X →ₗ[ℂ] SB Y →ₗ[ℂ] SB (X × Y) :=
  LinearMap.mk₂ ℂ prodSB
    (fun f f' g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g g' => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp; ring)

def tensorToProd (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X ⊗[ℂ] SB Y →ₗ[ℂ] SB (X × Y) := TensorProduct.lift (prodSBBil X Y)

theorem tensorToProd_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) :
    tensorToProd X Y (f ⊗ₜ g) = prodSB f g := by
  simp [tensorToProd, prodSBBil]

theorem tensorToProd_injective (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB X)
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i n => b i ⊗ₜ n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ x y, ∑ i ∈ c.support, (b i).1 x * (c i).1 y = 0 := by
    intro x y
    have := congrArg (fun F : SB (X × Y) => F.1 (x, y)) ht

    simp only [ht', Finsupp.sum, map_sum, tensorToProd_tmul] at this
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hzero : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support (fun i => (c i).1 y)
        (by
          ext x
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
          rw [← hm x y]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
      simpa using hli
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat.CFac

theorem exists_linear_of_bilinear_prodSB : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  intro X Y _ _ M _ _ B
  let m := tensorToProd X Y
  let e := LinearEquiv.ofInjective m (tensorToProd_injective X Y)
  let l₀ : LinearMap.range m →ₗ[ℂ] M := (TensorProduct.lift B).comp e.symm.toLinearMap
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  refine ⟨l, fun f g => ?_⟩
  have hmem : prodSB f g = ((e (f ⊗ₜ g) : LinearMap.range m) : SB (X × Y)) := by
    simp [e, LinearEquiv.ofInjective_apply, m, tensorToProd_tmul]
  have := LinearMap.congr_fun hl (e (f ⊗ₜ g))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, l₀,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul] at this
  rw [hmem, this]

end GlobalTheory.LocFlat.CFac
