module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.CoordUnique

theorem coords_unique_of_field {K E A : Type*} [Field K] [Ring E] [Nontrivial E] [Algebra K E] [AddCommGroup A]
    [Module K A] (w : E) (hw : ∀ f : K, algebraMap K E f ≠ w) (a b : A)
    (h : a ⊗ₜ[K] (1 : E) + b ⊗ₜ[K] w = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (K × K) →ₗ[K] E, ∀ p, φ p = p.1 • (1 : E) + p.2 • w :=
    ⟨{ toFun := fun p => p.1 • (1 : E) + p.2 • w,
       map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel,
       map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply] },
      fun p => rfl⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ hst
    rw [hφ] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      simp [hst]
    · exfalso
      apply hw (-s / t)
      have h1 : t • w = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : w = t⁻¹ • (-(s • (1 : E))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, div_eq_mul_inv, neg_mul, neg_smul, mul_comm]
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := A) φ hinj
  have hx : φ.lTensor A (a ⊗ₜ[K] ((1 : K), (0 : K)) +
      b ⊗ₜ[K] ((0 : K), (1 : K))) = 0 := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hφ, hφ]
    simpa using h
  rw [← map_zero (φ.lTensor A)] at hx
  have hx0 := hinj' hx
  have ha : TensorProduct.rid K A
      ((LinearMap.fst K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = a := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.fst_apply, LinearMap.fst_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, add_zero]
  have hb : TensorProduct.rid K A
      ((LinearMap.snd K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = b := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.snd_apply, LinearMap.snd_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, zero_add]
  rw [hx0, map_zero, map_zero] at ha hb
  exact ⟨ha.symm, hb.symm⟩

theorem coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) →
    ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 :=
  fun _ _ w hw a b h => coords_unique_of_field w hw a b h

end GlobalTheory.CoordUnique
