module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimitStatement
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.RingContH

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨_, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit R F hF J D c hc n
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj (sp c.pt) n x
    obtain ⟨j, w, y, hw, hwy⟩ := h1 z hz
    refine ⟨j, cl _ n w hw, ?_⟩
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, heq]
    exact ⟨y, hwy⟩
  · obtain ⟨w, hw, rfl⟩ := hsurj (sp (D.obj j)) n y
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, hzero] at hy
    obtain ⟨k, f, y', hy'⟩ := h2 j w hw hy
    refine ⟨k, f, ?_⟩
    obtain ⟨h', hh'⟩ := hpull (sp (D.obj k)) (sp (D.obj j)) (spMap (D.map f).hom) n w hw
    rw [hh', hzero]
    exact ⟨y', hy'⟩

end GlobalTheory.EtC.RingContH
