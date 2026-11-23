module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def OneCopyOrth : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∃ (m : ℕ) (e : Fin m → Matrix (Fin 1) (Fin 1) D.host.E) (u : Fin m → ℚ),
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) e ∧
      (∀ i j, i ≠ j → hYY D (e i) (e j) = 0) ∧
      ∀ i, 0 < u i ∧ ¬ (p : ℤ) ∣ (u i).num ∧ ¬ p ∣ (u i).den ∧ hYY D (e i) (e i) = ((u i : ℚ) : D.host.K)

def UnitVec : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (k : ℕ) (e : Fin k → D.host.E),
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧
        (s : D.host.E) * e i ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) →
      (∀ i j, i ≠ j → Algebra.trace D.host.K D.host.E (e i * D.host.conj (e j)) = 0) →
      (∀ i, ∃ u : ℚ, 0 < u ∧ ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den ∧
        Algebra.trace D.host.K D.host.E (e i * D.host.conj (e i)) = ((u : ℚ) : D.host.K)) →
      k < Module.finrank D.host.K D.host.E →
      ∃ z : D.host.E,
        (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * z ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) ∧
        (∀ i, Algebra.trace D.host.K D.host.E (z * D.host.conj (e i)) = 0) ∧
        ∃ u : ℚ, 0 < u ∧ ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den ∧
          Algebra.trace D.host.K D.host.E (z * D.host.conj z) = ((u : ℚ) : D.host.K)

end Formalism.L2.KerInert
