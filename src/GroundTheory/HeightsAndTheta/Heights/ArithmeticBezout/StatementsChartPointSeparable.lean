module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartParAlgebraic.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.IsAlgebraic
        (Algebra.adjoin (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1)))) L

def ChartFreeParAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1))) ∧
        Algebra.IsAlgebraic K L

def ChartPointSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F)
    (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    (∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable K L

section Inhabitants

namespace ChartPointLine

end ChartPointLine

open ChartPointLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights
