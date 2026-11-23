module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
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
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)

def QuadTwoAdic : Prop :=
  ∀ T N : ℤ, Odd T → Even N →
    ∃ b b' : ℤ_[2], b + b' = (T : ℤ_[2]) ∧ b * b' = (N : ℤ_[2]) ∧ ‖b‖ = 1 ∧ ‖b'‖ < 1

def RootsTwoAdic : Prop :=
  ∀ (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (T N : ℤ), α + conj α = (T : ℂ) → α * conj α = (N : ℂ) → Odd T →
    Even N → ∃ b b' : ℤ_[2], ‖b‖ = 1 ∧ ‖b'‖ < 1 ∧
      ((ι α = ((b : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2])) ∨
        (ι α = ((b' : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b : ℚ_[2]) : ℂ_[2])))

def ThetaZeroTwoTrace : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (T N : ℤ), MulStable L α → α + conj α = (T : ℂ) →
    α * conj α = (N : ℂ) → Odd T → Even N →
    ω₀ ∈ L.lattice → α * (ω₀ / 2) ∉ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def ThetaZeroTwoCM : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    conj (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.B
