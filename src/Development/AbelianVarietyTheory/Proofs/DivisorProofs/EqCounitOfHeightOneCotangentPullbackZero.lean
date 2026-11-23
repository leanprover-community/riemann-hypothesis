module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit (R := k) (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit (R := k) (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
