module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.HostProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem goodAt_iff (l : Level H) {p : ℕ} (hp : p.Prime) : l.GoodAt p ↔ ∀ k, l.M ≠ p ^ k := by
  have h3 := l.three_le
  have hM : l.M ≠ 0 := by omega
  have hmul : p ^ l.M.factorization p * (l.M / p ^ l.M.factorization p) = l.M :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  unfold Level.GoodAt
  constructor
  · intro h k hk
    rw [hk] at h
    simp [hp.factorization_pow, Nat.div_self (pow_pos hp.pos k)] at h
  · intro h
    set c := l.M / p ^ l.M.factorization p with hc
    have hodd : Odd c := by
      have := l.odd
      rw [← hmul] at this
      exact (Nat.odd_mul.1 this).2
    have h1 : c ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hmul
      exact h _ hmul.symm
    obtain ⟨t, ht⟩ := hodd
    omega

end GlobalTheory.HostProbe
