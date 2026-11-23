module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.general_b_fact_third''''

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsFullLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) := by
  intro E _ _ _ S Λ hL x
  have hx : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • (a • y) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem b hay) (Λ.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨w, hw⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(w.2 : NumberField.RingOfIntegers E) * a, mul_ne_zero (nonZeroDivisors.ne_zero w.2.2) ha, ?_⟩
    have key : ((w.2 : NumberField.RingOfIntegers E) * a) • (c • y) = w.1 • (a • y) := by
      rw [← algebraMap_smul E ((w.2 : NumberField.RingOfIntegers E) * a), ← algebraMap_smul E w.1,
        ← algebraMap_smul E a, smul_smul, smul_smul, ← hw, map_mul]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem w.1 hay

end Bl.general_b_fact_third''''
