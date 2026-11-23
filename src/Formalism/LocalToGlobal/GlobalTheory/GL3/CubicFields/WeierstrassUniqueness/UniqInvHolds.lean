module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEq
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEqNhdsNEOfZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem uniqLat_holds (Λ Λ' : AddSubgroup ℂ) (hΛ : IsLat Λ) (hΛ' : IsLat Λ')
    (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ') (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ') : Λ = Λ' := by
  obtain ⟨L, hL⟩ := exists_periodPair_of_isLat Λ hΛ
  obtain ⟨L', hL'⟩ := exists_periodPair_of_isLat Λ' hΛ'
  obtain ⟨a2, a3⟩ := g2_g3_eq_periodPair Λ L hL
  obtain ⟨b2, b3⟩ := g2_g3_eq_periodPair Λ' L' hL'
  have e : (L.lattice : Set ℂ) = L'.lattice :=
    lattice_eq_of_weierstrassP L L'
      (weierstrassP_eventuallyEq L L' (by rw [← a2, ← b2, h2]) (by rw [← a3, ← b3, h3]))
  apply SetLike.coe_injective
  rw [← hL, ← hL', e]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
