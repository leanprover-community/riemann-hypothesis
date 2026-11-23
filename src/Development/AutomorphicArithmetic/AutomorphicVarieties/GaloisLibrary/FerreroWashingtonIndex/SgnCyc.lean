module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HMinus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnitSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.UnrJPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.sgnCyc :
    ∀ (f n c N : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L] (γ : (ZMod (f * 2 ^ n))ˣ), Odd f → 1 < f → 2 ≤ n → c.Coprime (f * 2 ^ n) → Odd c → (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * 2 ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * 2 ^ n))ˣ), ((2 : ℕ) : MonoidAlgebra ℤ (ZMod (f * 2 ^ n))ˣ)} → (difR (clMap (cE L))).relIndex (minK (clMap (cE L))) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro f n c N _ L _ _ _ _ γ hf hf1 hn hc ho hmem
  have hM : 2 < f * 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  obtain ⟨φ, hφ⟩ := sgnUnit (f * 2 ^ n) c L hc ho hM
  obtain ⟨h1, h2, h3, h4⟩ := sgnStab (f * 2 ^ n) L φ
  refine (hMinus L _ (embT (f * 2 ^ n) L φ) (evenF (-1 : (ZMod (f * 2 ^ n))ˣ))
    (unrJ f n L hf hf1 hn) (unitSurj f n L hf hf1 hn) h1 h2).trans ?_
  haveI : Fact (2 < f * 2 ^ n) := ⟨hM⟩
  refine sgnAlg _ (-1) γ (thetaH (f * 2 ^ n) c) N _ (by simp) ?_ h3 ?_ hmem
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    exact ZMod.neg_one_ne_one h'
  · have h5 := (sgnE (embT (f * 2 ^ n) L φ)).sub_mem (h3 _ hφ (ZMod.unitOfCoprime c hc)⁻¹)
      ((sgnE (embT (f * 2 ^ n) L φ)).nsmul_mem h4 ((c - 1) / 2))
    convert h5 using 1
    funext s
    rw [(thetaFull (f * 2 ^ n) c hc ho hM).2 s]
    have hi : (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = (c : ZMod (f * 2 ^ n))⁻¹ := by
      rw [← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]
    rw [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, mul_one]
    simp only [gc, Units.val_mul, hi, Int.cast_sub, Int.cast_natCast]
