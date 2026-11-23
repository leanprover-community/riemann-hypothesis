module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
