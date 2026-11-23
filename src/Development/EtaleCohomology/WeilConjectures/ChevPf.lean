module

public import Development.EtaleCohomology.WeilConjectures.ContinCut
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

namespace LateralTheory.EWeil.ChevPf

open Topology

theorem Chev_of : LateralTheory.EWeil.ContinCut.Chev := by
  intro l _ M _ _ _ K hK h0 N
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  let V : ℕ → Set (Fin r → ℤ_[l]) := fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))
  have hc : ∀ k, IsCompact (V k) := by
    intro k
    obtain ⟨s, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)
    have : V k = Set.range (((K k).comap π).subtype.comp g) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := hg ⟨z, hz⟩
        exact ⟨a, by simp [ha]⟩
      · rintro ⟨a, rfl⟩
        exact (g a).2
    rw [this]
    exact isCompact_range (LinearMap.continuous_on_pi _)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro z hz; exact hK (le_max_left a b) hz
    · intro z hz; exact hK (le_max_right a b) hz
  let ε : ℝ := (l : ℝ) ^ (-(N : ℤ))
  have hε : 0 < ε := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  let U : Set (Fin r → ℤ_[l]) :=
    {z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}
  have hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x := by
    intro x hx
    have hx0 : π x = 0 := h0 _ (fun k => Set.mem_iInter.1 hx k)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro z hz
    refine ⟨x, z - x, hx0, fun i => ?_, by abel⟩
    have h1 : dist (z i) (x i) ≤ dist z x := dist_le_pi_dist z x i
    rw [Metric.mem_ball] at hz
    rw [Pi.sub_apply, ← dist_eq_norm]
    linarith
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hc (mem_nhdsSet_iff_forall.mpr hU)
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨c, w, hc0, hw, rfl⟩ := hk (show x ∈ V k from hy)
  have hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u := by
    intro i
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  choose u hu using hu
  refine ⟨π u, ?_⟩
  have : w = (l : ℤ_[l]) ^ N • u := funext fun i => by simp [hu i]
  rw [map_add (f := _), hc0, zero_add, this, map_smul]

end LateralTheory.EWeil.ChevPf
