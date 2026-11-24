module

public import Formalism.PeriodIntegrals.PhConvProj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.Defs

open PI.PhConvProj

def SelfAdjStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

def SandStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ a, T.comp ((π a).comp T) = m a • T

theorem convProj_of (h1 : SelfAdjStep) (h2 : SandStep) : ConvProj := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hci K _ _ π T hπ hT
  have hsa := h1 G μ ph m hph hci K π T hπ hT
  have hsw := h2 G μ ph m hph hci K π T hπ hT
  obtain ⟨hπ1, -⟩ := hπ
  obtain ⟨hm1, -⟩ := hci
  refine ⟨hsa, ?_, hsw⟩
  have h := hsw 1
  rw [hπ1, hm1, one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at h
  exact h

end PI.UnitaryGroupMassFormula.PhConvProj.Defs
