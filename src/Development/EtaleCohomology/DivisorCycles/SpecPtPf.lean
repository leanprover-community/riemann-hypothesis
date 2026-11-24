module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace LateralTheory.DivDb.SpecPtPf

theorem SpecPt_of : LateralTheory.DivDb.SpecPt := by
  intro C R σ _ _ _ _ _ _ x G hG hx
  classical
  let I : Ideal (MvPolynomial σ C) := RingHom.ker (MvPolynomial.aeval (R := C) x)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  let P : MvPolynomial σ C := ∏ g ∈ hG.toFinset, g
  have hP : MvPolynomial.aeval x P ≠ 0 := by
    simp only [P, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)
  have hPI : P ∉ I.radical := by
    rw [hI.radical]; exact hP
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff] at hPI
  push Not at hPI
  obtain ⟨y, hy, hyP⟩ := hPI
  rw [MvPolynomial.mem_zeroLocus_iff] at hy
  refine ⟨y, fun f hf => ?_, fun g hg => ?_⟩
  · have := hy f (RingHom.mem_ker.mpr hf)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  · simp only [P, map_prod] at hyP
    exact (Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)

end LateralTheory.DivDb.SpecPtPf
