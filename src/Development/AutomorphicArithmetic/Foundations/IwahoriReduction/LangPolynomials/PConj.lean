module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pConj : SConj := by
  intro l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hti : t⁻¹ ∈ Ine (F := ℚ) A := inv_mem ht
  have h1I : (1 : G ℚ Ω) ∈ Ine (F := ℚ) A := one_mem _
  refine ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · have h0 : Z m 1 x = 0 := by
      have h := hZ.coc m 1 h1I 1 h1I x
      rw [mul_one, map_one, inv_one, mul_one] at h
      linear_combination -h
    have h2 := hZ.coc m t ht t⁻¹ hti x
    rw [mul_inv_cancel, h0] at h2
    have h3 := hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x
    have h4 := hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)
    rw [hsk, inv_one, mul_one] at h4
    rw [mul_assoc, h3, h4]
    linear_combination -h2

end UpperTheory.Kd.C7
