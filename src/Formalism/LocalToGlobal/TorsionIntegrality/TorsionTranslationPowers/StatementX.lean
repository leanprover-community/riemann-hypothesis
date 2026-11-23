module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
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

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def VJoint : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ (g2 g3 s2 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l), (g2 : ℂ_[l]) = ι L.g₂ → (g3 : ℂ_[l]) = ι L.g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L) → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      ∃ V : PowerSeries ℂ_[l], IntS V ∧
        (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l).subtype
                  (Formalism.L2.Th1.D.phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
          (PowerSeries.map (ι : ℂ →+* ℂ_[l])
            (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
            (C (ε : ℂ_[l]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l)

def InWTh0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) =
        Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW l L ι W (ω₀ / 2)))))

end Formalism.L2.Th1.E
