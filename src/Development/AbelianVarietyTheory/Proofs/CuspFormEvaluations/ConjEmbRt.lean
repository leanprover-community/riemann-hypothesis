module

import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
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

namespace GlobalTheory.ConjugateEmbeddingSquareRoot

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z ^ 2 = -(r : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  apply GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.conj_eq_neg_of_sq <;> assumption

theorem conjEmb_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    conjEmb τ (H.rt : E) = -τ (H.rt : E) := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ)) : ℂ) := by
    rw [← map_pow, h1]
    simp
  exact conj_eq_neg_of_sq hd h2

end GlobalTheory.ConjugateEmbeddingSquareRoot
