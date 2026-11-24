module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem ch_eq_exp_pow_val (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring

theorem exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by
  intro N _ g
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hg : IsPrimitiveRoot (g (Complex.exp (2 * Real.pi * Complex.I / N))) N :=
    hζ.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime N := by
    rw [← hi] at hg
    exact (hζ.pow_iff_coprime (NeZero.pos N) i).mp hg
  refine ⟨ZMod.unitOfCoprime i hcop, fun j => ?_⟩
  rw [ch_eq_exp_pow_val, ch_eq_exp_pow_val, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime,
    ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  conv_lhs => rw [← Nat.div_add_mod (i * j.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.WpFam
