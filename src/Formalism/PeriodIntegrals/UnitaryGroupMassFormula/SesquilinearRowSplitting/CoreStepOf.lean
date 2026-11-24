module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

def FrameP {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r : ℕ} {T : E}
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V) (f : Fin r → S.V) : Prop :=
  (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ b, S.hT (f b) F0.z = 0) ∧
    (∀ b, ∀ x ∈ Λ, S.hT (f b) x ∈ aa b)

def FrameStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∃ f, FrameP S aa F0 Λ f

def DualEStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ b, ∀ x ∈ Λ, S.hT (F0.e b) x ∈ (aa b)⁻¹

def DualFStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      ∀ b, ∀ y ∈ (aa b)⁻¹, y • f b ∈ Λ

def IsoStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      ∃ f', FrameP S aa F0 Λ f' ∧ ∀ a b, S.hT (f' a) (f' b) = 0

def AsmStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V), CoreHyp S aa F0 Λ → ∀ f, FrameP S aa F0 Λ f →
      (∀ a b, S.hT (f a) (f b) = 0) → Formalism.L2.SG.Saturated.IsSplitBy aa F0 Λ

theorem coreStep_of (h1 : FrameStep) (h2 : IsoStep) (h3 : AsmStep) : CoreStep := by
  intro E _ _ _ S r T aa F0 Λ hC
  obtain ⟨f, hf⟩ := h1 E S r T aa F0 Λ hC
  obtain ⟨f', hf', hiso⟩ := h2 E S r T aa F0 Λ hC f hf
  exact h3 E S r T aa F0 Λ hC f' hf' hiso

end PI.SRW
