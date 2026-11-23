module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt {X : Scheme.{0}} [IsIntegral X] (p : ℕ)
    (G H : _root_.GlobalTheory.Cartier.CartierDiv X) (y : X) (h : (H - p • G).Eff) :
    {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c},
      ∃ b ∈ _root_.GlobalTheory.LogDR.locRing y, z = c ^ p * b} ⊆
      {c | H.RegularAt y c} := by
  rintro z ⟨c, ⟨g, hg, hcg⟩, b, hb, rfl⟩
  obtain ⟨k, hk, hk1⟩ := h y
  have hH : H.IsEqn y (k * g ^ p) := by
    have := hk.add (hg.nsmul p)
    simpa using this
  refine ⟨k * g ^ p, hH, ?_⟩
  rw [← _root_.GlobalTheory.LogDR.mem_locRing] at hcg hk1 ⊢
  have hz : c ^ p * b * ((k * g ^ p : (X.functionField)ˣ) : X.functionField) =
      (c * g) ^ p * b * (1 * k) := by
    push_cast
    ring
  rw [hz]
  exact mul_mem (mul_mem (pow_mem hcg p) hb) hk1

end GlobalTheory.DI
