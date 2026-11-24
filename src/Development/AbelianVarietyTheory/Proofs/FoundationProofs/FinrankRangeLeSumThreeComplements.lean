module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem finrank_range_le_three (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (P a b : Module.End ℂ M) :
    Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - a) * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  have hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔
      (LinearMap.range ((1 - b) * P)).map a := by
    rintro _ ⟨x, rfl⟩
    have hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x) := by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P))
    ((LinearMap.range ((1 - b) * P)).map a)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))
  have h4 := Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))
  omega

end GlobalTheory.BadShare
