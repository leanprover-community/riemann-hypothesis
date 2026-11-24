module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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

namespace GlobalTheory.DenominatorOfSpan

open GlobalTheory.UnitLemma

theorem exists_smul_mem_of_span_eq_top {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay

theorem exists_denominator {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x

end GlobalTheory.DenominatorOfSpan
