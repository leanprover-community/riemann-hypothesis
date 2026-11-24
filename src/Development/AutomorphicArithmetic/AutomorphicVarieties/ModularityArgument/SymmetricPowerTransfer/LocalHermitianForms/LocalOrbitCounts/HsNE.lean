module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.hsNE : UpperTheory.V.Z.Sym.Loc.HsNE := by
  intro O K _ _ _ _ _ Δ τ hL _ t
  have h2 : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hiff : hs (τ ^ 2 - 4) (t : K) = 1 ↔ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = t := by
    unfold hs
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      norm_num
  rw [hiff]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : QuadraticAlgebra.norm (z : QuadraticAlgebra K (-1) τ) = (t : K) := by
      have h := congrArg Units.val hz
      rwa [Units.coe_map] at h
    refine ⟨((z : QuadraticAlgebra K (-1) τ).re * 2 + τ * (z : QuadraticAlgebra K (-1) τ).im) / 2,
      (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩
    rw [← hz', norm_def]
    field_simp
    ring
  · rintro ⟨a, b, hab⟩
    have hw : QuadraticAlgebra.norm (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) = (t : K) := by
      rw [← hab, norm_def]
      ring
    have hu : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) := by
      rw [isUnit_iff_norm_isUnit, hw]
      exact t.isUnit
    refine ⟨hu.unit, ?_⟩
    ext
    rw [Units.coe_map, IsUnit.unit_spec]
    exact hw
