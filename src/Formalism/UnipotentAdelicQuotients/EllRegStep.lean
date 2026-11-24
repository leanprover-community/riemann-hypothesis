module

public import Formalism.UnipotentAdelicQuotients.EllRegCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

def Decompose : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ (x0 : E d) (ψ0 : E d → ℝ) (r : ℝ), ContDiff ℝ ∞ ψ0 → HasCompactSupport ψ0 →
      (∀ y ∈ ball (0 : E d) 1, ψ0 y = 1) → tsupport ψ0 ⊆ ball 0 2 → 0 < r → ball x0 (2 * r) ⊆ U →
    ∀ (χ χ' : E d → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r →
      ContDiff ℝ ∞ χ' → HasCompactSupport χ' → tsupport χ' ⊆ U →
      (∀ x ∈ tsupport χ, χ' =ᶠ[𝓝 x] fun _ => 1) →
    ∀ i : ι, ∃ lo c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ,
      (∀ n w, ContDiff ℝ ∞ (lo n w) ∧ HasCompactSupport (lo n w)) ∧
      (∀ n w, ContDiff ℝ ∞ (c n w) ∧ HasCompactSupport (c n w)) ∧
      ∀ ξ : E d,
        (∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x0 * mono w ξ) * 𝓕 (cut χ u) ξ
          + ∑ w : Fin (P.ord i) → Fin d,
              conv (𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) *
                (P.a i (P.ord i) w x - P.a i (P.ord i) w x0))) (fun η => mono w η * 𝓕 (cut χ u) η) ξ
          + ∑ n ∈ Finset.range (P.ord i), ∑ w : Fin n → Fin d,
              conv (𝓕 (lo n w)) (fun η => mono w η * 𝓕 (cut χ u) η) ξ
        = ∑ n ∈ Finset.range (P.ord i), ∑ w : Fin n → Fin d,
            (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ

def DecomposeOf : Prop :=
  PairingFourier → DwExp → FourierPair → PairingLocal → WeakFourier → Decompose

def FiniteWeighted : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → ∀ s M ε : ℝ, 0 < ε → s + d / 2 < M →
    nrm s M ε (𝓕 g) < ⊤

def EpsLimit : Prop :=
  ∀ (d : ℕ) (s M : ℝ) (F : E d → ℂ) (B : ℝ≥0∞), 0 ≤ M → Continuous F →
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → nrm s M ε F ≤ B) → nrm s 0 0 F ≤ B

def StepCore : Prop :=
  SymbLower → WeightDiff → ConvBound → KernelSmall → Decompose → FiniteWeighted → EpsLimit → CutCont → Step

theorem stepOfParts_of (hD : DecomposeOf) (hF : FiniteWeighted) (hE : EpsLimit) (hS : StepCore) :
    StepOfParts :=
  fun hSL hW hCB hK hPF hDE hFP hPL hWF _ hC => hS hSL hW hCB hK (hD hPF hDE hFP hPL hWF) hF hE hC

end

end ZetaZeros.D.EllReg
