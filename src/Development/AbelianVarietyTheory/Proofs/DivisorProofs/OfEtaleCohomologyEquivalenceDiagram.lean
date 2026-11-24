module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ContCone.iff_of_eqv (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt)
    (h : ∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) (hα : ∀ i, Eqv R (α.app i) F) (hβ : Eqv R β F) :
    ContCone R F c ↔ ContCone R F c' := by
  have hsq : ∀ n i (y' : H R (G'.obj i) F n),
      pull R (c.π.app i) F n (pull R (α.app i) F n y') = pull R β F n (pull R (c'.π.app i) F n y') := by
    intro n i y'
    rw [← pull_comp, ← pull_comp, h i]
  have hnat : ∀ n {k i : I} (f : k ⟶ i) (y' : H R (G'.obj i) F n),
      pull R (G.map f) F n (pull R (α.app i) F n y') = pull R (α.app k) F n (pull R (G'.map f) F n y') := by
    intro n k i f y'
    rw [← pull_comp, ← pull_comp, α.naturality f]
  constructor
  · intro hc n
    refine ⟨fun x' => ?_, fun i y' hy' => ?_⟩
    · obtain ⟨i, y, hy⟩ := (hc n).1 (pull R β F n x')
      obtain ⟨y', rfl⟩ := (hα i n).2 y
      refine ⟨i, y', (hβ n).1 ?_⟩
      rw [← hsq, hy]
    · obtain ⟨k, f, hf⟩ := (hc n).2 i (pull R (α.app i) F n y') (by rw [hsq, hy', map_zero])
      refine ⟨k, f, (hα k n).1 ?_⟩
      rw [← hnat, hf, map_zero]
  · intro hc n
    refine ⟨fun x => ?_, fun i y hy => ?_⟩
    · obtain ⟨x', rfl⟩ := (hβ n).2 x
      obtain ⟨i, y', hy'⟩ := (hc n).1 x'
      exact ⟨i, pull R (α.app i) F n y', by rw [hsq, hy']⟩
    · obtain ⟨y', rfl⟩ := (hα i n).2 y
      have h0 : pull R (c'.π.app i) F n y' = 0 := (hβ n).1 (by rw [← hsq, hy, map_zero])
      obtain ⟨k, f, hf⟩ := (hc n).2 i y' h0
      exact ⟨k, f, by rw [hnat, hf, map_zero]⟩

end GlobalTheory.EtC
