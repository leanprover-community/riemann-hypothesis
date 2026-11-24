module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.general_b_fact_second_alt

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)) (v : Fin r → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (a : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} a 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} a v)) := by
  intro K _ _ r L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨(d : NumberField.RingOfIntegers K) * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ha, ?_⟩
    have key : ((d : NumberField.RingOfIntegers K) * a) • (c • x) = n • (a • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * a), ← algebraMap_smul K a,
        ← algebraMap_smul K n, smul_smul, smul_smul]
      simp only at hnd
      rw [← hnd, map_mul]
      congr 1
      ring
    rw [key]
    exact L.smul_mem n hax

end Bl.general_b_fact_second_alt
