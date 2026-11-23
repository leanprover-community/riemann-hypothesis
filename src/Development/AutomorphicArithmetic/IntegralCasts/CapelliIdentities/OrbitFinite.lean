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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by
  intro V _ _ G _ _ _ ρ K hK w hw
  have hloc : IsLocallyConstant (fun g : G => ρ g w) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun g : G => k⁻¹ * g) ⁻¹' {g : G | ρ g w = w},
      hw.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hg' : ρ (k⁻¹ * g) w = w := hg
    calc ρ g w = ρ (k * (k⁻¹ * g)) w := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hg']
  haveI : CompactSpace (K : Set G) := isCompact_iff_compactSpace.mp hK
  have hfin := (hloc.comp_continuous
    (continuous_subtype_val (p := fun g : G => g ∈ (K : Set G)))).range_finite
  refine hfin.subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩
