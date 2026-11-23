module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.IntDvr

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧
    Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  intro l _ K
  refine ⟨Formalism.BasicNotions.Examples₂.LB.OL_dvr K, Formalism.BasicNotions.Examples₂.LB.OL_finite K,
    fun x => ⟨fun h => h.map _, fun h => ?_⟩⟩
  rw [Formalism.BasicNotions.Examples₂.LB.isUnit_iff]
  obtain ⟨u, hu⟩ := h
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 (u : OC l).2
  have h2 := (GlobalTheory.RingBasics.mem_OC _).1 ((u⁻¹ : (OC l)ˣ) : OC l).2
  have h3 : ((u : OC l) : ℂ_[l]) * (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l]) = 1 := by
    have := congrArg (fun z : OC l => (z : ℂ_[l])) u.mul_inv
    exact this
  have h4 : ‖((u : OC l) : ℂ_[l])‖ = 1 := by
    have h5 := congrArg norm h3
    rw [norm_mul, norm_one] at h5
    nlinarith [norm_nonneg ((u : OC l) : ℂ_[l]), norm_nonneg (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l])]
  have h6 : ((u : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [hu, coe_intToOC]
  rw [h6, PadicComplex.norm_extends] at h4
  exact h4

end GlobalTheory.IntDvr
