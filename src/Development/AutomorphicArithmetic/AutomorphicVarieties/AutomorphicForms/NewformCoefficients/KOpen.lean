module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.kOpen :
    UpperTheory.V.Af.Nf.KOpen := by
  intro M hM
  refine ⟨Subgroup.isOpen_mono (H₁ := KLev ℚ 2 M) (fun g hg => ?_) (isOpen_KLev hM), fun u hu x hx => ?_⟩
  · obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
    refine (memK M g).2 ⟨ha, hb, ?_, ?_⟩
    · simpa using hc 1 0
    · simpa using hc 1 1
  · refine (memK M _).2 ⟨?_, ?_, ⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.1, hx⟩, Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.2, neg_mem (mul_mem hu.2 hx)⟩,
        Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · exact (mul_zero _).symm
    · exact (sub_self (1 : Af ℚ)).trans (mul_zero _).symm
