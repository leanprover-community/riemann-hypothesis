module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]


omit [NumberField K] in
theorem apply_eq_abs_embedding_of_isReal {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    v x = |embedding_of_isReal hv x| := by
  rw [← norm_embedding_of_isReal hv x, Real.norm_eq_abs]

theorem exists_units_neg_iff_mem (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (embedding_of_isReal v.2 (a : K) < 0 ↔ v ∈ S) ∧ (0 < embedding_of_isReal v.2 (a : K) ↔ v ∉ S) := by
  classical

  set c : InfinitePlace K → K := fun v => if h : v.IsReal then
    (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1) else 1 with hcdef
  let t : (v : InfinitePlace K) → WithAbs v.1 := fun v => WithAbs.toAbs v.1 (c v)
  let U : Set ((v : InfinitePlace K) → WithAbs v.1) := Set.pi Set.univ fun v => Metric.ball (t v) 1
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have htU : t ∈ U := fun v _ => Metric.mem_ball_self one_pos
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open hU ⟨t, htU⟩

  have hclose : ∀ v : InfinitePlace K, v (x - c v) < 1 := by
    intro v
    have h := hx v (Set.mem_univ v)
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hc : ∀ v : InfinitePlace K, v (c v) = 1 := by
    intro v
    rw [hcdef]
    show v.1 (if h : v.IsReal then (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1)
      else 1) = 1
    split_ifs <;> simp only [AbsoluteValue.map_neg, AbsoluteValue.map_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have := hclose v
    rw [zero_sub, show v (-c v) = v (c v) from v.1.map_neg _, hc] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 x hx0, fun v => ?_⟩
  have h := hclose v.1
  rw [apply_eq_abs_embedding_of_isReal v.2, map_sub] at h
  have hcv : c v.1 = if v ∈ S then -1 else 1 := by rw [hcdef]; exact dif_pos v.2
  rw [hcv] at h
  rw [Units.val_mk0]
  by_cases hv : v ∈ S
  · rw [if_pos hv, map_neg, map_one, sub_neg_eq_add, abs_lt] at h
    exact ⟨⟨fun _ => hv, fun _ => by linarith [h.2]⟩, ⟨fun h' => by linarith [h.2], fun h' => absurd hv h'⟩⟩
  · rw [if_neg hv, map_one, abs_lt] at h
    exact ⟨⟨fun h' => by linarith [h.1], fun h' => absurd h' hv⟩, ⟨fun _ => hv, fun _ => by linarith [h.1]⟩⟩


omit [NumberField K] in
theorem extensionEmbeddingOfIsReal_algebraMap {v : InfinitePlace K} (hv : v.IsReal) (x : K) :
    Completion.extensionEmbeddingOfIsReal hv (algebraMap K v.Completion x) = embedding_of_isReal hv x :=
  by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    simpa using Completion.extensionEmbeddingOfIsReal_coe hv (WithAbs.toAbs v.1 x)

end GroundTheory.ProfCoh
