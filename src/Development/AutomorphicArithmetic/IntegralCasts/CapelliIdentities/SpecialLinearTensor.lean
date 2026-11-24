module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.SpecialLinearTensor.sl :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v :=
  fun {I} _ dI {W} _ _ v f => by
    have prod_update_self (m : (i : I) → W i) (x : W v) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m v x j) =
          ∏ j ∈ Finset.univ.erase v, f j (m j) := by
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have prod_update_ne {i : I} (h : i ≠ v) (m : (j : I) → W j) (x : W i) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m i x j) =
          f i x * ∏ j ∈ (Finset.univ.erase v).erase i, f j (m j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    exact PiTensorProduct.lift
      { toFun := fun m => (∏ j ∈ Finset.univ.erase v, f j (m j)) • m v
        map_update_add' := by
          intro d m i x y
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, smul_add]
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              map_add, add_mul, add_smul]
        map_update_smul' := by
          intro d m i c x
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, RingHom.id_apply]
            exact smul_comm _ _ _
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              RingHom.id_apply, map_smul, smul_eq_mul, mul_assoc, mul_smul] }

theorem UpperTheory.Reformulated.B.SpecialLinearTensor.sl_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.SpecialLinearTensor.sl v f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → W v)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        (∏ i ∈ Finset.univ.erase v, (f i : W i → ℂ) (m i)) • m v := by
  intro I _ _ W _ _ v f m
  rw [UpperTheory.Reformulated.B.SpecialLinearTensor.sl, PiTensorProduct.lift.tprod]
  rfl
