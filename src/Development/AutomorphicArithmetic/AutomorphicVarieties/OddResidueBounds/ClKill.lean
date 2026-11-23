module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Normkill
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem jv_eq (M a : ℕ) [NeZero M] (ha : a.Coprime M) (b : ZMod M) :
    (M : ℤ) * jv M a b = (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
  unfold jv
  have hdiv : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    unfold yCl
    rw [← mul_assoc, ZMod.coe_mul_inv_eq_one a ha, one_mul, sub_self]
  exact Int.mul_ediv_cancel' hdiv

theorem UpperTheory.V.Odd.clKill :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a : ℕ), Odd a → a.Coprime M → ∀ c : Additive (ClassGroup (𝓞 K)), ∑ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c = 0 := by
  intro M _ K _ _ _ a ha hcop c
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have hterm : ∀ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c =
      Additive.ofMul ((clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (Eone M a b)) := by
    intro b
    rfl
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← ofMul_prod]
  show Additive.ofMul _ = Additive.ofMul 1
  congr 1
  have hnorm : ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) = 1 := by
    rw [← Stk.prod_galois_classGroup_map_eq_one K (Additive.toMul c)]
    exact Fintype.prod_equiv ((Stick.sg M K).toEquiv.trans (Equiv.inv _)) _ _ (fun b => rfl)
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime a hcop
  let β : (ZMod M)ˣ → ℤ := fun s => (if s = u⁻¹ then (a : ℤ) else 0) - (if s = 1 then 1 else 0)
  have hβ : ∀ t : (ZMod M)ˣ, (M : ℤ) * jv M a (t : ZMod M) =
      ∑ s, β s * (((s : ZMod M) * (t : ZMod M)).val : ℤ) := by
    intro t
    rw [jv_eq M a hcop t]
    have hy : yCl a (t : ZMod M) = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * t := by
      unfold yCl
      rw [← ZMod.inv_coe_unit]
      rfl
    simp only [β, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, one_mul, Units.val_one]
    rw [hy]
  have hj := (Stick.coef M K (Additive.toMul c)).2 β (fun t => jv M a (t : ZMod M)) hβ
  calc ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ Eone M a b
      = ∏ b : (ZMod M)ˣ, (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ (((a : ℤ) - 1) / 2) *
          (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹) := by
        refine Finset.prod_congr rfl (fun b _ => ?_)
        unfold Eone
        rw [zpow_sub]
    _ = (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (((a : ℤ) - 1) / 2) *
          (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_zpow]
    _ = 1 := by
        rw [hnorm, hj, one_zpow, inv_one, one_mul]
