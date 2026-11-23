module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
