module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem re_pi_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hdeg0 := FA.Re.degree
  unfold ReciprocityTheory.AnForm.M.IsDegreeOff at hdeg0
  have hdeg := hdeg0.2.2.2.2.1
  rw [FA.br_empty, FA.deg_one] at hdeg
  have h1 : ∀ x, ∃ a, FA.Re.π ⁻¹' {x} = {a} := fun x => Set.ncard_eq_one.1 (hdeg x (by simp))
  constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := h1 (FA.Re.π a)
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton _)
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton_iff.2 hab.symm)
    rw [hc] at ha hb
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro x
    obtain ⟨c, hc⟩ := h1 x
    have hcx : c ∈ FA.Re.π ⁻¹' {x} := by
      rw [hc]
      exact Set.mem_singleton c
    exact ⟨c, Set.mem_singleton_iff.1 (Set.mem_preimage.1 hcx)⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
