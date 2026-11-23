module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvr
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.kummer_aeval_valuation_dvr : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  first | (exact @GlobalTheory.kummer_valuation) | (exact GlobalTheory.kummer_valuation) | (intros; apply GlobalTheory.kummer_valuation  <;> assumption)
