module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartZeroTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω) (j : Fin n),
      (∀ q ∈ Q, aeval y q = 0) → y j ≠ 0 →
        Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => y m * (y j)⁻¹)) ≤ (d : Cardinal)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
