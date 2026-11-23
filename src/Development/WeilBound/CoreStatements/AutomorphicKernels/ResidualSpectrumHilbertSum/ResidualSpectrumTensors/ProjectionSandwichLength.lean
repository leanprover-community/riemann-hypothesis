module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.ProjectionSandwichLength

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eq_of_isAbsPow {ν ν' : HChar E} {s : ℝ} (h : ν.IsAbsPow s) (h' : ν'.IsAbsPow s) : ν = ν' := by
  have h0 : (ν * ν'⁻¹).IsAbsPow 0 := by
    refine ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
    · change ν.loc v x * (ν'.loc v x)⁻¹ = 1
      rw [h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
    · have e : ν.val v = ν'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
      simp [HChar.val_mul, HChar.val_inv, e]
    · have e : ν.inf k = ν'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
      simp [HChar.inf_mul, HChar.inf_inv, e]
  exact mul_inv_eq_one.1 (GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow h0)

section Quot

variable {I V : Submodule ℂ (Sm E N)} {f : Sm E N →ₗ[ℂ] Sm E N}

end Quot

end PositivityTheory.RSHS.ProjectionSandwichLength

end
