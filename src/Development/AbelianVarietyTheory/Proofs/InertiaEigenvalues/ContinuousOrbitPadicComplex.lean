module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
