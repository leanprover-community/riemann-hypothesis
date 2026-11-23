module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.stickH :
    ∀ (M c : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L], c.Coprime M → Odd c → 2 < M → (cycRep M L).asAlgebraHom (thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))) = 0 := by
  intro M c _ L _ _ _ hc hodd hM

  rw [(thetaFull M c hc hodd hM).1, map_sum]
  refine LinearMap.ext fun x => ?_
  simp only [Representation.asAlgebraHom_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply]
  have key : ∀ y : Cl L, ∑ s : (ZMod M)ˣ, gc M c ↑s • (cycRep M L s) (Additive.ofMul y) = 0 := by
    intro y
    simp only [cycRep_apply, ← ofMul_zpow, ← ofMul_prod, clA, ofMul_eq_zero]
    haveI : Fact (1 < M) := ⟨by omega⟩
    set u : (ZMod M)ˣ := ZMod.unitOfCoprime c hc with hu_def
    set k : ℤ := (((c - 1) / 2 : ℕ) : ℤ) with hk
    refine (Stick.coef M L y).2
      (fun s => (c : ℤ) * (if s = u⁻¹ then 1 else 0) - (k + 1) * (if s = 1 then 1 else 0)
        - k * (if s = -1 then 1 else 0)) (fun t => gc M c ↑t) ?_
    intro t
    haveI : NeZero (t : ZMod M) := ⟨t.ne_zero⟩
    have hlt := ZMod.val_lt (t : ZMod M)
    have hneg : ((-(t : ZMod M)).val : ℤ) = M - (t : ZMod M).val := by
      rw [ZMod.val_neg_of_ne_zero (t : ZMod M), Nat.cast_sub hlt.le]
    have hu : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = (c : ZMod M)⁻¹ := by
      rw [← ZMod.inv_coe_unit]
      rfl
    have hmod : c * ((c : ZMod M)⁻¹ * t).val % M = (t : ZMod M).val := by
      rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one c hc, one_mul]
    have hdiv := Nat.div_add_mod (c * ((c : ZMod M)⁻¹ * t).val) M
    rw [hmod] at hdiv
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Units.val_one, Units.val_neg,
      neg_one_mul, hu, hneg, gc]
    generalize c * ((c : ZMod M)⁻¹ * t).val / M = q at hdiv ⊢
    have hz : (M : ℤ) * q + ((t : ZMod M).val : ℤ) = c * (((c : ZMod M)⁻¹ * t).val : ℤ) := by
      exact_mod_cast hdiv
    linear_combination hz
  exact key (Additive.toMul x)
