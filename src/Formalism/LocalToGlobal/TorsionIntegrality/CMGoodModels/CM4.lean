module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.CM

def CM4 : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
      (lam ^ 4 * ι L.g₂) ∈ MaximalUnramifiedExtension l → (lam ^ 6 * ι L.g₃) ∈ MaximalUnramifiedExtension l → ‖lam ^ 4 * ι L.g₂‖ ≤ 1 →
      ‖lam ^ 6 * ι L.g₃‖ ≤ 1 → ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      lam ^ 2 * ι (L.weierstrassP z) ∈ MaximalUnramifiedExtension l ∧ lam ^ 3 * ι (L.derivWeierstrassP z) ∈ MaximalUnramifiedExtension l ∧
        ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1

end Formalism.L2.Th1.CM
