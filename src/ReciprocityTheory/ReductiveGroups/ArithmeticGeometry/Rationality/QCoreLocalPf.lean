module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalLengthAverage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain Module

theorem qcoreLocal : QCoreLocalStatement := by
  intro hLD hQL K K₁ V _ _ _ _ _ _ _ _ _ _ M hM hspan W θ hθ c hc be s hbe hs hint
  refine ⟨LocalQuotientRank.detCT_ne_zero (M := M) (hM := hM) (hspan := hspan) (W := W)
    (θ := θ) (hθ := hθ) (c := c) (hc := hc), ?_⟩
  intro la
  obtain ⟨ℓ, hℓ, hle⟩ := LocalLengthAverage.average (la := la)
    (L := lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))))
    (D := detCT c θ) (t := fun w => ∑ i, s i w)
    (ρ := Module.finrank (𝓞 K) (QuotMW M W)) (B := be la) (by
      intro w hw

      obtain ⟨n, hn, hnle⟩ := LocalLengthAverage.lenW_bound (hL := hQL) (M := M) (hM := hM)
        (hspan := hspan) (W := W) (θ := θ) (hθ := hθ) (c := c) (hc := hc) (w := w)
        (s := fun i => s i w) (β := (w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la)
        (hint := fun i m hm hne => hint la w hw i m hm hne)
      refine ⟨n, ?_, ?_⟩
      · rw [← hLD K K₁ V M hM hspan W θ la w hw]
        exact hn
      · simpa only using hnle)
  refine ⟨ℓ, hℓ, ?_⟩
  simpa only [nnFun] using hle

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
