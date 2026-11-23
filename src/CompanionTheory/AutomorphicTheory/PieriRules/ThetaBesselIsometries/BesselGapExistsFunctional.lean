module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapIntegrabilityStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasicStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.FamilyDerivativeExpansion.BeL

theorem exists_normalised_bessel_map : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -⟩ := id hside
  obtain ⟨L, hL⟩ := hH.1.2.2.2 k r ε mu R Wp z u₀ π μW μN hDS hz hT hπ hW hN
  have hTK : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.T.discreteSeries_unitary_smooth_basic hH.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
  by_cases h0 : ∀ v ∈ R.TK, L v = 0
  · refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2, h0 v hv]
    ext ξ
    simp
  · push Not at h0
    obtain ⟨v₀, hv₀, hne⟩ := h0
    have hB := Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul
      (GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside v₀ hv₀ (L v₀)) (⟪L v₀, L v₀⟫_ℂ)⁻¹
    have e : ∀ w ∈ R.sm, (⟪L v₀, L v₀⟫_ℂ)⁻¹ • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ (L v₀) = L w := by
      intro w hw
      rw [(hL w hw v₀ (hTK _ hv₀)).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
        inv_mul_cancel₀ (inner_self_ne_zero.2 hne), one_smul]
    refine ⟨_, hB, fun w hw v hv => ⟨(hL w hw v (hTK v hv)).1, ?_⟩⟩
    rw [(hL w hw v (hTK v hv)).2]
    simp only [e w hw, e v (hTK v hv)]

end CompanionTheory.FamilyDerivativeExpansion.BeL
