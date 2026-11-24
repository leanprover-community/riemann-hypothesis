module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Mathlib.NumberTheory.LocalField.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem unifLC {F : Sp k n → ℂ} (hF : F ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    ∃ W ∈ nhds (0 : Matrix (Fin n) (Fin n) k), ∀ w ∈ W, ∀ p : Sp k n, F (p.1 + w, p.2) = F p := by
  obtain ⟨hlc, hcs⟩ := hF
  have hK : IsCompact (tsupport F) := hcs
  have hc1 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 + z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hc2 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 - z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hev : ∀ᶠ w in nhds (0 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport F,
      F (q.1 + w, q.2) = F q ∧ F (q.1 - w, q.2) = F q := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro q _
    have e1 := (hlc.comp_continuous hc1).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e2 := (hlc.comp_continuous hc2).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e3 := (hlc.comp_continuous continuous_snd).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    simp only [Function.comp_apply, add_zero, sub_zero] at h1 h2 h3
    exact ⟨by rw [h1, h3], by rw [h2, h3]⟩
  refine ⟨_, hev, ?_⟩
  intro w hw p
  by_cases hp : p ∈ tsupport F
  · exact (hw p hp).1
  · have h0 : F p = 0 := image_eq_zero_of_notMem_tsupport hp
    by_cases hp' : ((p.1 + w, p.2) : Sp k n) ∈ tsupport F
    · have := (hw _ hp').2
      simp only [add_sub_cancel_right] at this
      rw [h0] at this ⊢
      exact this.symm
    · rw [h0]
      exact image_eq_zero_of_notMem_tsupport hp'

end PositivityTheory.RgUd.TP.Nil.Fib2

end
