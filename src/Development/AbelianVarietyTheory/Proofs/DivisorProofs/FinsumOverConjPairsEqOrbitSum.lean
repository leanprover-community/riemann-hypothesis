module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieBundleIntersection
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

open scoped Classical

theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
