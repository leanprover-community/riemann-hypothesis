module

public import Mathlib.Analysis.CStarAlgebra.Classes
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

def chartBase (a : Fin 2) : (Σ _ : Unit, Fin 2) → ℂ := fun p => if p.2 = a then 1 else 0

def chartLin (a : Fin 2) : (Fin 1 → ℂ) →L[ℂ] ((Σ _ : Unit, Fin 2) → ℂ) :=
  ContinuousLinearMap.pi fun p => if p.2 = a then 0 else (2 : ℂ) • ContinuousLinearMap.proj 0

theorem chartLin_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartLin a t p = if p.2 = a then 0 else 2 * t 0 := by
  unfold chartLin
  split_ifs <;> simp [*]

def chartMap (a : Fin 2) (t : Fin 1 → ℂ) : (Σ _ : Unit, Fin 2) → ℂ := chartBase a + chartLin a t

theorem chartMap_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartMap a t p = if p.2 = a then 1 else 2 * t 0 := by
  simp only [chartMap, Pi.add_apply, chartBase, chartLin_apply]
  split_ifs <;> simp

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
