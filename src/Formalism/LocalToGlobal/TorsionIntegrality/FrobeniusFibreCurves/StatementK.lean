module

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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit GaussOne)


open Classical in
def TwoTorsionKernelUnique : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ‖W.a₁‖ = 1 →
    ∀ P Q : W.toAffine.Point, P ≠ 0 → P + P = 0 → InFormalGroupPoints P →
      ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q)



def TorsBound : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ∀ (P : W.toAffine.Point) (k : ℕ), (2 ^ k) • P = 0 → P + P ≠ 0 →
      ‖px W P‖ < 4

def KapNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.A.IntModel W → ‖(2 : K)‖ = 2⁻¹ → ∀ x : K,
      (‖x‖ = 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ = 16) ∧
      (‖x‖ < 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ < 16)

def KappaSum : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∑ P ∈ S, (3 * L.weierstrassP P ^ 2 - L.g₂ / 4) = (α ^ 4 - 1) * L.g₂ / 20

def KernelIntegral : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, α * t ∈ L.lattice → t ∉ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W t)

def KernelStableUnderMultiplier : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, InFormalGroupPoints (ptW 2 L ι W t) → InFormalGroupPoints (ptW 2 L ι W (α * t))

def PointsTwoFinal : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    ¬ InFormalGroupPoints (ptW 2 L ι W (ω₀ / 2)) ∧
      (∀ Q, α * Q - ω₀ / 2 ∈ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W Q)) ∧
      (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice)

def ThetaZeroAtTwo : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ 2 ∣ N → (N : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.B
