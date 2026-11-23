module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Trace
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

noncomputable section

namespace GlobalTheory.DatumSign

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct

section Lin

variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem _root_.GlobalTheory.DatumSign.trace_eq :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (s : ℝ),
      ∀ (hs : (0 : ℝ) < s) (hT : ∀ (x : V), T (T x) = (s * s) • x),
        LinearMap.trace ℝ V T =
          s * ((2 : ℝ) * (Module.finrank ℝ (T - s • LinearMap.id).ker : ℝ) -
            (Module.finrank ℝ V : ℝ)) := by
  intro V _ _ _ T s hs hT
  set P : V →ₗ[ℝ] V := (2 * s)⁻¹ • (T + s • LinearMap.id) with hP
  have hproj : LinearMap.IsProj (T - s • LinearMap.id).ker P := by
    constructor
    · intro x
      simp only [LinearMap.mem_ker, hP, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, hT]
      rw [smul_sub s (T x), smul_smul, sub_add_sub_cancel, sub_self, smul_zero]
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
      simp only [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hx,
        ← two_smul ℝ (s • x), smul_smul]
      rw [show (2 * s)⁻¹ * (2 * s) = 1 by field_simp, one_smul]
  have htr := hproj.trace
  have hTP : T = (2 * s) • P - s • LinearMap.id := by
    rw [hP, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
  clear_value P
  conv_lhs => rw [hTP]
  rw [map_sub, map_smul, map_smul, htr, LinearMap.trace_id, smul_eq_mul, smul_eq_mul]
  ring

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.DatumSign
