module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem sz_adjoin_rootOfUnity :
    ∀ n : ℕ, 0 < n → Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF
  haveI hc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hfd : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {n} ℚ F
  refine ⟨hfd, ?_⟩
  letI : NumberField F := NumberField.mk
  have hrk : Module.finrank ℚ F = Nat.totient n :=
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have htR : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast ht
  have hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr n F]
    exact Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · rw [hrk]
    exact Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)
  · rw [hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]
    have h0 : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hd

end GlobalTheory.FieldSize
