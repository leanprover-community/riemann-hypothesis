module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LFunctionChainParameters.UnitWeightPartition

open Finset

noncomputable section

variable {ι κ : Type*} [DecidableEq ι]

def sgw (J : Finset κ) (gain F E : κ → ι → ℝ) (w : ι) : ℝ :=
  ∑ j ∈ J, (gain j w + F j w - E j w)

def Ga (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain : κ → ι → ℝ) (tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * ((∑ j ∈ J, gain j w) - tau w)

def Fo (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (F : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * F j w

def Ee (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (E : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * E j w

def Sg (W : Finset ι) (l s tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * (s w - tau w)

def Ta (W : Finset ι) (l tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * tau w

def IO (W : Finset ι) (l io : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * io w

def be (du : ℝ) (len tau : ι → ℝ) (w : ι) : ℝ :=
  (len w - du * tau w) / du

def BeSum (W : Finset ι) (l : ι → ℝ) (du : ℝ) (len tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * be du len tau w

def ClaimSg (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : Prop :=
  Sg W l (sgw J gain F E) tau = Ga W J l gain tau + Fo W J l F - Ee W J l E

def ClaimDe (f : ℕ) (T dM du : ℝ) : Prop :=
  0 < dM → 2 < T → du = dM * (1 - 1 / (T - 1)) ^ f →
  du = (1 - (1 - du / dM)) * dM ∧ 0 ≤ 1 - du / dM ∧ 1 - du / dM < 1 ∧
    1 - du / dM ≤ 2 * (f : ℝ) / T

def ClaimT (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) : Prop :=
  (∀ w ∈ WT, 0 ≤ l w) → 0 < dM → 0 ≤ de → de ≤ 1 / 2 → du = (1 - de) * dM → 0 ≤ lam →
  (∀ w ∈ WT, len w ≤ dM * lam) → ∑ w ∈ WT, l w = Real.log T →
  ∑ w ∈ WT, 2 * l w * len w / du ≤ 4 * lam * Real.log T

def HypLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ dM * (tau w + io w)) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + Sg W l sg' tau - BeSum W l du len tau

def HypLow2 (W : Finset ι) (l tau io : ι → ℝ) (f T de b muM muMu IOp PT LT Rd RX : ℝ) :
    Prop :=
  muMu = muM - f * Real.log (T - 1) / (T - 2) ∧ de ≤ 2 * f / T ∧ 2 * f / T ≤ 1 / 2 ∧
  (∀ w ∈ W, 0 ≤ tau w) ∧ Ta W l tau ≤ b ^ 2 ∧
  4 * f / T * b ^ 2 + f * Real.log (T - 1) / (T - 2) ≤ 1 ∧
  IO W l io = 2 * IOp ∧ PT ≤ LT ∧ Rd ≤ RX

def ClaimLow2 (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  HypLow2 W l tau io f T de b muM muMu IOp PT LT Rd RX →
  muM + Ga W J l gain tau + Fo W J l F - Ee W J l E - (4 * IOp + LT + RX + 1) ≤ muN

def HypHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ (∀ w ∈ W, sg' w ≤ sgw J gain F E w) ∧
  muMaxN ≤ muMaxMu + Sg W l sg' tau ∧ muMaxMu ≤ muMaxM

def ClaimHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  HypHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN →
  muMaxN ≤ muMaxM + Ga W J l gain tau + Fo W J l F - Ee W J l E

end

end Formalism.LFunctionChainParameters.UnitWeightPartition
