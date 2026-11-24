module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
