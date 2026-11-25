module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

noncomputable section

namespace GlobalTheory.Discrepancy.DivOver

theorem exists_through_of_isProper : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ x : X, E.Through x → ∃ y : Y, s y = x ∧ E'.Through y := by
  intro k _ X Y _ _ p s _ _ hprop E' E hOver x hx
  haveI := hprop
  have hmem : ∀ a : X.presheaf.stalk x,
      functionFieldMap s (algebraMap _ X.functionField a) ∈ E'.ring :=
    fun a => (hOver _).1 (hx _ ⟨a, rfl⟩)
  let ψ : X.presheaf.stalk x →+* E'.ring :=
    ((functionFieldMap s).comp (algebraMap _ X.functionField)).codRestrict E'.ring.toSubring hmem
  have hc : genericFieldPoint Y ≫ s = specAlgebraMap E'.ring Y.functionField ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) := by
    rw [← specMap_functionFieldMap, ← specAlgebraMap_fromSpecStalk x]
    simp only [specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨b, hb1, hb2⟩ := exists_valuativeExtension s _ (genericFieldPoint Y) hc
  have hdom : DominatesStalk E'.ring (b (IsLocalRing.closedPoint E'.ring)) :=
    dominatesStalk_iff_exists_hom.mpr ⟨b, hb1, rfl⟩
  have hw : E'.Through (b (IsLocalRing.closedPoint E'.ring)) := by
    rintro f ⟨c, rfl⟩
    exact hdom.1 c
  have hz : s (b (IsLocalRing.closedPoint E'.ring)) ⤳ x := by
    have e : s (b (IsLocalRing.closedPoint E'.ring)) = X.fromSpecStalk x
        (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring)) := by
      have := congrArg (fun l : Spec (CommRingCat.of E'.ring) ⟶ X =>
        l (IsLocalRing.closedPoint E'.ring)) hb2
      exact this
    rw [e]
    have := (IsLocalRing.specializes_closedPoint
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring))).map
        (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  obtain ⟨y, hwy, hy⟩ := s.isClosedMap.specializingMap hz
  exact ⟨y, hy, hw.of_specializes hwy⟩

end GlobalTheory.Discrepancy.DivOver
