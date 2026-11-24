module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
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
public import Mathlib.NumberTheory.Bernoulli

@[expose] public section

namespace ReciprocityTheory.PGsh

open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma

def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

theorem qExpansion_E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) e4Z := by
  ext n
  rw [coeff_map, e4Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, hn, show bernoulli 4 = -1 / 30 by decide +kernel]

theorem qExpansion_E₆_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) e6Z := by
  ext n
  rw [coeff_map, e6Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, hn, show bernoulli 6 = 1 / 42 by decide +kernel]

end ReciprocityTheory.PGsh
