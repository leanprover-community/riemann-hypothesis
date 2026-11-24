module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.ImaginarySqrtEmbedding

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.conj_eq_neg_of_sq_eq_neg_natCast <;> assumption

theorem embedding_sqrt_sq_and_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : E →+* ℂ) :
    τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
        = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) ∧
      starRingEnd ℂ (τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E))
        = -τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  have h1 : τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
      = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at h
    exact h
  exact ⟨h1, conj_eq_neg_of_sq_eq_neg_nat _ _ h1⟩

end GlobalTheory.ImaginarySqrtEmbedding
