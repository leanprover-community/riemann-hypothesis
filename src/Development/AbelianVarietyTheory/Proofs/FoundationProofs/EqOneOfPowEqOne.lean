module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.RootOfUnityEqOne

open IsLocalRing

theorem eq_one_of_pow_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ}
    (hm : V.valuation (m : F) = 1) {ζ : F} (hζ : ζ ^ m = 1)
    (h1 : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  apply GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt <;> assumption

theorem main : ∀ {F : Type} [inst : Field F] (V : ValuationSubring F) {m : ℕ},
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (↑m : F) = (1 : ValuationSubring.ValueGroup V) →
    ∀ {ζ : F}, ζ ^ m = (1 : F) →
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (ζ - (1 : F)) < (1 : ValuationSubring.ValueGroup V) →
    ζ = (1 : F) := by
  intro F _ V m hm ζ hζ h1
  exact eq_one_of_pow_eq_one V hm hζ h1

end GlobalTheory.RootOfUnityEqOne
