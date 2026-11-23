module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakClosed

theorem tailDecomp {O : Type} [CommRing O] {n : ℕ} (k : ℕ) (a : LetA O n) :
    a = (∑ j ∈ Finset.range k, fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j) +
      (letπ : LetA O n) ^ k * (fun i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (a i)) := by
  funext i
  ext m

  simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, letπ, map_add (f := _), map_sum,
  PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
  Finset.sum_ite_eq, Finset.mem_range]
  by_cases hk : m < k
  · simp [hk, Nat.not_le.2 hk]
  · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]

theorem continuous_of_tail {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U)
    (hmono : ∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hU
  obtain ⟨k, hk⟩ := hsmall V hV
  let mono : ℕ → LetA O n → M := fun j a =>
    Φ (fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hcont : ∀ j, Continuous (mono j) := fun j =>
    (hmono j).comp (continuous_pi fun i =>
      (PowerSeries.WithPiTopology.continuous_coeff O j).comp (continuous_apply i))
  let S : LetA O n → M := fun a => ∑ j ∈ Finset.range k, (mono j a - mono j a₀)
  have hS : Continuous S := continuous_finsetSum _ fun j _ => (hcont j).sub continuous_const
  have hS0 : S a₀ = 0 := by simp [S]
  have hSV : ∀ᶠ a in 𝓝 a₀, S a ∈ V := by
    have := hS.continuousAt (x := a₀)
    rw [ContinuousAt, hS0] at this
    exact this hV
  rw [Filter.mem_map]
  filter_upwards [hSV] with a ha
  let tl : LetA O n → LetA O n := fun b i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (b i)
  have hΦ : ∀ b, Φ b = (∑ j ∈ Finset.range k, mono j b) + Φ (letπ ^ k * tl b) := by
    intro b
    conv_lhs => rw [tailDecomp k b]

    rw [map_add (f := _), map_sum]
  have : Φ a - Φ a₀ = S a + Φ (letπ ^ k * (tl a - tl a₀)) := by
    rw [hΦ a, hΦ a₀, mul_sub, map_sub]
    simp only [S, Finset.sum_sub_distrib]
    abel
  show Φ a - Φ a₀ ∈ U
  rw [this]
  exact hVV _ ha _ (hk _)

end GlobalTheory.WeakClosed
