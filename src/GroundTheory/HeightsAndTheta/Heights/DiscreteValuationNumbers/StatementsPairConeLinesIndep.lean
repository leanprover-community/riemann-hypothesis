module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
