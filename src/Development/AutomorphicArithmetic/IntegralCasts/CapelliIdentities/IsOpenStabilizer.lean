module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G _ _ _ V _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {g : G | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        change ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by simp }
  exact H.isOpen_of_mem_nhds (g := 1) h
