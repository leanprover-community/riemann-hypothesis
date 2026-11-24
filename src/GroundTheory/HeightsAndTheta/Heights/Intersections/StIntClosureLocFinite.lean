module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def IntClosureLocFinite.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (S : Finset L), Subfield.closure (S : Set L) = ⊤ →
    ∀ (A : Subring F) (T : Finset F), Subring.closure (T : Set F) ≤ A →
    (∀ z ∈ A, ∃ b ∈ Subring.closure (T : Set F), ∃ c ∈ Subring.closure (T : Set F),
      c ≠ 0 ∧ c⁻¹ ∈ A ∧ z * c = b) →
    letI := (φ.comp A.subtype).toAlgebra
    letI : Module A L := Algebra.toModule
    ∃ t : Finset L, ∀ x : L, IsIntegral A x → x ∈ Submodule.span A (t : Set L)

end GroundTheory.Heights₂.Heights.Inter
