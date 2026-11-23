module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.injAE_pf :
    UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.InjAE := by
  intro hN n
  have h : ∀ i j : Fin n, ∀ᵐ θ : Fin n → UnitAddCircle, i ≠ j → pt θ i ≠ pt θ j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun θ h => absurd hij h)
    · have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun e => hij (MvPolynomial.X_injective e))
      filter_upwards [hN n _ hp] with θ hθ _ e
      apply hθ
      simp [e]
  have h2 : ∀ᵐ θ : Fin n → UnitAddCircle, ∀ i j : Fin n, i ≠ j → pt θ i ≠ pt θ j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  filter_upwards [h2] with θ hθ i j e
  by_contra hne
  exact hθ i j hne e
