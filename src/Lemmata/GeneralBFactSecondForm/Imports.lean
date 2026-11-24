module

public import Mathlib.Algebra.Module.Lattice.Full
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

namespace Bl.general_b_fact_second_form

theorem goal1 :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [StarRing.{0} K] [inst_3 : AddCommGroup.{0} V]
  [inst_4 : Module.{0, 0} K V] [inst_5 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [inst_6 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  {Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V},
  Submodule.IsFullLattice.{0, 0, 0} K Λ →
    ∀ (v : V),
      Exists.{1} fun (r : NumberField.RingOfIntegers.{0} K) ↦
        And (Ne.{1} r 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} r v)) := by
  intro K V _ _ _ _ _ _ _ Λ hΛ v
  have hv : v ∈ Submodule.span K (Λ : Set V) := by
    rw [hΛ.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have h1 : (r * s) • x ∈ Λ := by rw [mul_comm, mul_smul]; exact Λ.smul_mem s hrx
    have h2 : (r * s) • y ∈ Λ := by rw [mul_smul]; exact Λ.smul_mem r hsy
    rw [smul_add]; exact Λ.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    dsimp only at hab
    refine ⟨r * (b : NumberField.RingOfIntegers K),
      mul_ne_zero hr (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have hb : (b : NumberField.RingOfIntegers K) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : NumberField.RingOfIntegers K) (c • x), smul_smul, mul_comm,
        hab, algebraMap_smul]
    rw [mul_smul, hb, smul_smul, mul_comm, ← smul_smul]
    exact Λ.smul_mem a hrx

end Bl.general_b_fact_second_form
