module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.FirstBlockLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : Field.{0} L] [NumberField.{0} L] (x : L) (c : Int),
  Eq.{1} (HPow.hPow.{0, 0, 0} x 2) (HAdd.hAdd.{0, 0, 0} x (Int.cast.{0} c)) →
    Exists.{1} fun (X : NumberField.RingOfIntegers.{0} L) ↦
      And (Eq.{1} (NumberField.RingOfIntegers.val.{0} X) x)
        (Eq.{1} (HPow.hPow.{0, 0, 0} X 2) (HAdd.hAdd.{0, 0, 0} X (Int.cast.{0} c))) := by
  intro L _ _ x c h
  have hi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, h]
      simp
  refine ⟨⟨x, hi⟩, rfl, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  exact h

end Bl.FirstBlockLemmaE
