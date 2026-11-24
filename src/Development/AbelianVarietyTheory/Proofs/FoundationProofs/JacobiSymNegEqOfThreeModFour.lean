module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

theorem jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.neg _ hn]
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hq h]
    ring

end GlobalTheory
