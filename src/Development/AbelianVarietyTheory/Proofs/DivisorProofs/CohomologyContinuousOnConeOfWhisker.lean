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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  intro R _ F I _ _ I' _ _ L G c hL hc n
  obtain ⟨h1, h2⟩ := hc n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨i', y, hy⟩ := h1 x
    exact ⟨L.obj i', y, hy⟩
  · obtain ⟨i', ⟨f⟩⟩ := hL i
    have hy' : pull R ((c.whisker L).π.app i') F n (pull R (G.map f) F n y) = 0 := by
      change pull R (c.π.app (L.obj i')) F n (pull R (G.map f) F n y) = 0
      rw [← pull_comp, c.w f]
      exact hy
    obtain ⟨k', g, hg⟩ := h2 i' _ hy'
    refine ⟨L.obj k', L.map g ≫ f, ?_⟩
    rw [Functor.map_comp, pull_comp]
    exact hg

end GlobalTheory.EtC
