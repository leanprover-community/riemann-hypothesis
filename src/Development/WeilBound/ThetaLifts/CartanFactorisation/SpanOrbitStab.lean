module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKF.Abs

open scoped InnerProductSpace

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem orth_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (z : U) (hz : z ∈ Yᗮ) : κ k z ∈ Yᗮ := by
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro y hy
  have e : y = κ k (κ k⁻¹ y) := by rw [← mul_apply_eq_comp, ← map_mul]; simp
  rw [e, hi]
  exact hz _ (hY _ _ hy)

theorem span_orbit_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) (k : K) :
    ∀ y ∈ Submodule.span ℂ (Set.range fun k => κ k x), κ k y ∈ Submodule.span ℂ (Set.range fun k => κ k x) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => obtain ⟨k', rfl⟩ := h; exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : Submodule ℂ U := Submodule.span ℂ (Set.range fun k => κ k x)

theorem mem_orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : x ∈ orb κ x := Submodule.subset_span ⟨1, by simp⟩

end PositivityTheory.ThKF.Abs

end
