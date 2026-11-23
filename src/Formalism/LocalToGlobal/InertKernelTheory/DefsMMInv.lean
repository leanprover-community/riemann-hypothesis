module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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

def UnitSubstLoc : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
    ∀ (r : ℕ) (M : Fin r → Fin r → ℂ_[p] × ℂ_[p]), (∀ i j, M i j ∈ Formalism.MainNotions.GL3Theta.OKp D lam) →
      (∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0) →
      ∃ S : Fin r → MvPowerSeries (Fin r) ℂ_[p],
        (∀ i, MvPowerSeries.constantCoeff (S i) = 0) ∧ (∀ i, IntegralMv (S i)) ∧
        (∀ i, PowerSeries.subst (S i) (flog (C • wModel lam (lamOf D cc δ)) wq) =
          ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (M i j).1 *
            PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p])
              (flog (C • wModel lam (lamOf D cc δ)) wq)) ∧
        ∃ V : MvPowerSeries (Fin r) ℂ_[p], IntegralMv V ∧
          ePh lam (lamOf D cc δ) C wq r = MvPowerSeries.subst S (ePh lam (lamOf D cc δ) C wq r) * V

end Formalism.L2.KerInert
