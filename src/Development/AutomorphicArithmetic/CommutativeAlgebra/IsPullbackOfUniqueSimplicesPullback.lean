module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.isPullback_of_unique_simplices_pullback :
    ∀ {P A B C : Spc} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (u : B ⟶ C), t ≫ r = l ≫ u →
        (∀ (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u → ∃! z : Sx P k T, z.map t = x ∧ z.map l = y) →
        IsPullback t l r u := by
  intro P A B C t l r u hw h
  refine IsPullback.of_forall_isPullback_app (fun n => ?_)
  refine IsPullback.of_forall_isPullback_app (fun T => ?_)
  obtain ⟨⟨k⟩⟩ := n
  obtain ⟨T⟩ := T
  have hw' : ∀ x : Sx P k T, Sx.map r (Sx.map t x) = Sx.map u (Sx.map l x) := by
    intro x
    have := congrArg (fun f : P ⟶ C => (f.app (op ⟨k⟩)).app (op T) x) hw
    simpa [Sx.map] using this
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact hw' x
  · rintro x y ⟨h1, h2⟩
    obtain ⟨z, -, hz⟩ := h k T (Sx.map t (x : Sx P k T)) (Sx.map l (x : Sx P k T)) (hw' x)
    have hx := hz x ⟨rfl, rfl⟩
    have hy := hz y ⟨h1.symm, h2.symm⟩
    exact hx.trans hy.symm
  · intro a b hab
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := h k T a b hab
    exact ⟨z, h1, h2⟩
