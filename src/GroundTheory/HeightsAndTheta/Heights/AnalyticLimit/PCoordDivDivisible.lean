module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem cofactor_vanish {D : ℕ} {Ω : Set (Fin D → ℂ)} (hΩ : IsOpen Ω) {F G : (Fin D → ℂ) → ℂ}
    {i k : Fin D} (hik : k ≠ i) (hG : AnalyticOnNhd ℂ G Ω) (hFG : ∀ z ∈ Ω, F z = z i * G z)
    (hF : ∀ z ∈ Ω, z k = 0 → F z = 0) {z : Fin D → ℂ} (hz : z ∈ Ω) (hzk : z k = 0) : G z = 0 := by
  classical
  by_cases hzi : z i = 0
  swap
  · have h := hFG z hz
    rw [hF z hz hzk] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hzi

  set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw
  have hwc : Continuous w := continuous_const.update i continuous_id
  have hw0 : w 0 = z := by rw [← hzi]; simp [hw]
  have hcont : ContinuousAt (fun ε => G (w ε)) 0 := by
    have h := (hG z hz).continuousAt
    rw [← hw0] at h
    exact h.comp hwc.continuousAt
  have hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω := by
    exact hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)

  have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne
    have hwk : w ε k = 0 := by simp [hw, hik, hzk]
    have hwi : w ε i = ε := by simp [hw]
    have h := hFG _ hε
    rw [hF _ hε hwk, hwi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  have h := tendsto_nhds_unique ht1 ht2
  rwa [hw0] at h

theorem CoordDivDivisible.proof (hH : HyperplaneDivisible.Statement) : CoordDivDivisible.Statement := by
  classical
  intro D Ω F S hΩ hFa hF
  induction S using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hFa, fun z _ => by simp⟩
  | insert i S hi ih =>
    obtain ⟨G₁, hG₁a, hG₁⟩ := hH D Ω F i hΩ hFa fun z hz hzi =>
      hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩
    have hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0 := by
      rintro z hz ⟨k, hk, hzk⟩
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      exact cofactor_vanish hΩ hki hG₁a hG₁
        (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk
    obtain ⟨G, hGa, hG⟩ := ih G₁ hG₁a hG₁0
    refine ⟨G, hGa, fun z hz => ?_⟩
    rw [hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]

end GroundTheory.Heights₂.Heights.AnalyticLimit
