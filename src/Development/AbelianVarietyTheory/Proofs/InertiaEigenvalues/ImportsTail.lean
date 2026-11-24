module

public import Mathlib.RingTheory.Localization.FractionRing
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

namespace GlobalTheory.NonzeroScalarMembership

theorem exists_ne_zero_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay

end GlobalTheory.NonzeroScalarMembership
