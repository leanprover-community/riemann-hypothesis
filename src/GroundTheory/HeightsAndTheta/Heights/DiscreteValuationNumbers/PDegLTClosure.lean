module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Filter.AtTopBot.Group

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type}

theorem tendsto_sub_const_atTop (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id

theorem diffStep_eventuallyEq (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']

theorem foldr_diffStep_eventuallyEq (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih

theorem DegLTClosure.proof (h1 : MixedDiffLinear.Statement) : DegLTClosure.Statement := by
  intro K n f g c s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf hg bs
    filter_upwards [hf bs, hg bs] with m hm hm'
    rw [(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]
  · intro hf bs
    filter_upwards [hf bs] with m hm
    rw [(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]
  · intro hf bs
    have h' := (tendsto_sub_const_atTop s).eventually (hf bs)
    filter_upwards [h'] with m hm
    rw [(h1 K n bs f g c s 0).2.2.1]
    exact hm
  · intro hf bs
    have hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0 :=
      hf (fun i => bs i.succ)
    have hz' := (tendsto_sub_const_atTop (bs 0)).eventually hz
    filter_upwards [hz, hz'] with m hm hm'
    have e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f) := by
      unfold mixedDiff
      rw [List.ofFn_succ, List.foldr_cons]
    rw [e]
    simp only [diffStep, hm, hm', sub_zero]
  · intro hfg hf bs
    have e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g :=
      foldr_diffStep_eventuallyEq (List.ofFn bs) hfg
    filter_upwards [e, hf bs] with m hm hm'
    rw [← hm, hm']

end

end GroundTheory.Heights₂.Heights.NumbersDVR
