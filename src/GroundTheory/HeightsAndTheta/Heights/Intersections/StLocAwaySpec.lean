module

public import Mathlib.RingTheory.Localization.Away.Basic
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def LocAwaySpec.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] (φ : R →+* Φ) (S : Finset Φ),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    ∃ (E : R) (hE : IsUnit (φ E)),
      (∀ c ∈ S, c ∈ Set.range (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ)) ∧
      ∀ (B : Type) [CommRing B] (ψ : R →+* B) (hψ : IsUnit (ψ E)), RingHom.ker φ ≤ RingHom.ker ψ →
        RingHom.ker (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ≤
          RingHom.ker (IsLocalization.Away.lift E hψ : Localization.Away E →+* B)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
