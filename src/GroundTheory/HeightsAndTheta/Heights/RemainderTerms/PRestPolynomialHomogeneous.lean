module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem choose_two_add (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  rw [← Finset.sum_range_id, ← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_add,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem RestPolynomialHomogeneous.proof (h1 : VandermondeOfHomogeneous.Statement) :
    RestPolynomialHomogeneous.Statement := by
  intro f r a c
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a) + 1)).mul hfib
  have hdeg : 1 * (f * (r * a) + 1) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) + 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end GroundTheory.Heights₂.Heights.RestTerms
