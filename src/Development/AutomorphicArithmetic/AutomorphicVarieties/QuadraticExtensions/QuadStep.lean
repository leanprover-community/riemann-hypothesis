module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DegBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
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
import Mathlib.GroupTheory.IndexNormal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.quadStep :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (p N n : ℕ), p.Prime → p ∣ N → CardLe (CharOff (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) 2) n → CardLe (CharOff (cycU 2 (abU Ω (A.sup (AbF.quad p)))) (ineOff ℚ Ω N) 2) (n ^ 2) := by
  intro Ω _ _ _ A p N n hp hpN h
  have hsup := (abBasic Ω).1 A (AbF.quad p)
  have hq := (abBasic Ω).2.1 (AbF.quad p)
  have key : cycU 2 (abU Ω (A.sup (AbF.quad p))) = abU Ω (AbF.quad p) ⊓ cycU 2 (abU Ω A) := by
    ext g
    simp only [cycU, hsup, Subgroup.mem_inf]
    tauto
  rw [key]
  have hidx : (abU Ω (AbF.quad p)).index ∣ 2 := by
    rw [hq.1]
    exact degBasic.2.2.1 p hp
  have hnorm : (abU Ω (AbF.quad p)).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  refine idxTwo (G ℚ Ω) _ (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) n inf_le_right ?_ ?_ ?_ ?_ h
  · rw [Subgroup.inf_subgroupOf_right, Subgroup.coe_subgroupOf]
    exact hq.2.2.1.preimage continuous_subtype_val
  · rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx
  · intro v _ s hs
    exact (ineConj ℚ Ω v).2.2 N s hs
  · intro s hs hsV
    refine Subgroup.mem_inf.2 ⟨?_, hsV⟩
    obtain ⟨B, hB, hsB⟩ := hs
    haveI : NeZero (AbF.quad p).m := ⟨by simp [AbF.quad]⟩
    have hv : ¬ B.valuation ((AbF.quad p).m : Ω) < 1 := by
      intro hlt
      apply hB
      obtain ⟨k, rfl⟩ := hpN
      have hm : (AbF.quad p).m = p := max_eq_left hp.one_lt.le
      rw [hm] at hlt
      rw [Nat.cast_mul, map_mul]
      have hk : B.valuation (k : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B k)
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hk) hlt
    exact hq.2.2.2 (ineChar Ω (AbF.quad p).m B hv hsB)
