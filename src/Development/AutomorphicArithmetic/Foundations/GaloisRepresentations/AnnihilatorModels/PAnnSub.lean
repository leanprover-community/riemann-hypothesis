module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_right_comm_of_comm {F L U V B : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B]
    (i : U →ₗ[L] V) (f : U →ₗ[L] U) (f' : V →ₗ[L] V) (u : B →ₗ[F] B)
    (h : ∀ a, i (f a) = f' (i a)) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f' u (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) x) =
      AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


theorem UpperTheory.Gal.crystallineComparison.annSub_of :
    AnnSub := by
  intro F G B _ _ _ _ σ ψ L _ _ U V _ _ _ _ _ _ _ _ ρU ρ i hI hi q n TU T hT hAnn
  unfold Inter at hI
  unfold AnnD at hAnn ⊢
  let M : U ⊗[F] B →ₗ[L] V ⊗[F] B := AlgebraTensorModule.map i LinearMap.id
  have hM_inj : Function.Injective M := by
    have h1 : ⇑M = ⇑(LinearMap.rTensor B (i.restrictScalars F)) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [M]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.rTensor_preserves_injective_linearMap (i.restrictScalars F) hi
  have hpow : ∀ k, ∀ b, (LinearMap.id : B →ₗ[F] B) ((ψ ^ k) b) = (ψ ^ k) ((LinearMap.id : B →ₗ[F] B) b) :=
    fun _ _ => rfl
  intro x hx
  have hmx : M x ∈ Dinv σ ρ := by
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_right_comm_of_comm i (ρU g) (ρ g) (σ g) (hI g) x).trans (congrArg M (hx g))
  apply hM_inj

  rw [map_zero, ← hAnn (M x) hmx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower]
  congr 1
  exact (algebraTensorModule_map_map_id_right_comm_of_comm i (TU j) (T j) (ψ ^ (n - j)) (hT j) x).symm
