module

public import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (hG : IsZero G) (a : Sec G X) :
    a = 0 := by
  have h1 : Sec.map (𝟙 G) a = a := rfl
  have h2 : Sec.map (0 : G ⟶ G) a = 0 := rfl
  rw [← h1, hG.eq_of_src (𝟙 G) 0, h2]

theorem LeafZero_of : LeafZero := by
  intro R _ K X U n hz
  refine ⟨?_, ?_, ?_⟩
  · intro V W h a _
    rw [sec_eq_zero_of_isZero hz (rs h a)]
    exact zero_mem _
  · intro W a _
    rw [sec_eq_zero_of_isZero hz a]
    exact zero_mem _
  · intro V W h a _
    exact ⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩

end LateralTheory.CohomologicalPurity.Cl.Flq
