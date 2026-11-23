module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AgreeOfAdjoin
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem agree_of_adjoin {E : Type} [Field E] [NumberField E] (φ ψ : E →+* ℂ) {a b : E}
    (h : φ a = ψ a) (hb : b ∈ IntermediateField.adjoin ℚ {a}) : φ b = ψ b :=
  _root_.UpperTheory.Reformulated.B.Qk58.agree_of_adjoin φ ψ h hb

private theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z :=
  _root_.UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq hd hz

theorem pEpsIff_of : EpsIff := by
  intro E _ _ _ d x ω hd hx hω hx' τ φ
  have hτ : (τ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hc : ComplexEmbedding.conjugate τ x = -τ x := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg_of_sq hd hτ
  constructor
  · intro h
    have h' : φ ω = ComplexEmbedding.conjugate τ ω := by
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact h
    rw [agree_of_adjoin φ _ h' hx', hc]
  · intro h
    have h' : φ x = ComplexEmbedding.conjugate τ x := by rw [h, hc]
    rw [agree_of_adjoin φ _ h' hω, ComplexEmbedding.conjugate_coe_eq]

end UpperTheory.Gal.CertificateRingHomMap

end
