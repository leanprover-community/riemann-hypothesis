module

public import Formalism.CharacterColumnKernels.StatementN
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

def LocalSubalgebraEtaBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
    ∀ B : X → ℕ∞, (∀ x ∈ Zg, vcc T (Z : Set X) x ≤ B x) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (B x + IsDiscreteValuationRing.addVal O (A : O))

end Formalism.NG
