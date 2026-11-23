module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeCompStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasPeriod_of_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M K : Type) [Field M] [NumberField M] [Field K] [NumberField K] (j : M →+* K) (ω : 𝓞 M) (ω' : 𝓞 K) (C : Ell H (𝓞 M) ω) (C' : Ell H (𝓞 K) ω') (φ : C'.P.A.left ⟶ C.P.A.left) (x : ℝ), EllMap C' C (RingOfIntegers.mapRingHom j) φ → C.HasPeriod x → C'.HasPeriod x := by
  intro hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx
  obtain ⟨n, hn, hmean⟩ := hx
  refine ⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.cmCurveBaseChange_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]
    have e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j)
        = (s.comp j).comp (algebraMap (𝓞 M) M) := by
      ext a; rfl
    rw [e]
    exact (hn _).2 r
  · rw [GlobalTheory.meanLog_comp]; exact hmean

end GlobalTheory.CM
