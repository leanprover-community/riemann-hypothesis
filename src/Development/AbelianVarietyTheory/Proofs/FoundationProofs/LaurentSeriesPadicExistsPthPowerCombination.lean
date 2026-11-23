module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPowStatement
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
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]

    simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
