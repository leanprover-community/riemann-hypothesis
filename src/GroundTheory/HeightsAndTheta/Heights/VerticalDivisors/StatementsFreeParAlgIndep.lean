module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
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

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def FreeParAlgIndep.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (L : Type) [Field L] [Algebra k L]
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    [Module.Finite (GenParField k e n) L] (x : Fin n → L),
    Algebra.adjoin (GenParField k e n) (Set.range x) = ⊤ →
    (∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0) →
    ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1 →
    ∀ j₀, x j₀ ≠ 0 →
      Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin k (Set.range fun m => x m * (x j₀)⁻¹))
        (fun p : Fin e × {j : Fin n // j ≠ j₀} =>
          algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1))))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
