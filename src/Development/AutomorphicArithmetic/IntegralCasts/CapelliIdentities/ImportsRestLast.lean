module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
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

theorem UpperTheory.Reformulated.B.Yhd4.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousMul G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v hS
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  have hc : Filter.Tendsto (fun h : G => g⁻¹ * h) (nhds g) (nhds 1) := by
    have := ((continuous_const_mul g⁻¹ : Continuous (fun h : G => g⁻¹ * h)).tendsto g)
    simpa using this
  filter_upwards [hc hS] with h hh
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hh ⊢
  have : h = g * (g⁻¹ * h) := by group
  rw [this, map_mul, Module.End.mul_apply, hh, hg]
