module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
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

theorem UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open :
    ∀ {G H : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : Group H] (f : G →* H), IsOpen (↑f.ker : Set G) → IsLocallyConstant (⇑f : G → H) := by
  intro G H _ _ _ _ f hk
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : G => x⁻¹ * y := continuous_const.mul continuous_id
  have ho : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G)) := hk.preimage hc
  have hx : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G) := by
    simp [Set.mem_preimage, MonoidHom.mem_ker]
  filter_upwards [ho.mem_nhds hx] with y hy
  have h1 : f (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm
