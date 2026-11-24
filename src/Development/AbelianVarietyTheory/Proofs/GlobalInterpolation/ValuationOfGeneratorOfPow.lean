module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_of_generator_of_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K) (h : 𝔭.asIdeal ^ n = Ideal.span {π}) :
    𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact 𝔭.ne_bot (pow_eq_zero_iff'.mp h).1
  rw [show (π : K) = algebraMap (𝓞 K) K π from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    𝔭.intValuation_if_neg hπ, ← h, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr 𝔭.ne_bot) 𝔭.associates_irreducible,
    Associates.count_self 𝔭.associates_irreducible, mul_one]

end GlobalTheory
