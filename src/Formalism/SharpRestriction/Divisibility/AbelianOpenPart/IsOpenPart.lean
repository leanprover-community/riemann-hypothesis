module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace Formalism.MainNotions.DIV.Cons

abbrev BigT : Type := Set (Set ℝ)

structure SCF (p : ℕ) where
  S : Set BigT
  [fld : NontriviallyNormedField S]
  [ultra : IsUltrametricDist S]
  [ac : IsAlgClosed S]
  [cpl : CompleteSpace S]
  [ch0 : CharZero S]
  norm_p : ‖(p : S)‖ = (p : ℝ)⁻¹

attribute [instance] SCF.fld SCF.ultra SCF.ac SCF.cpl SCF.ch0

def SCF.toCF {p : ℕ} (c : SCF p) : Formalism.MainNotions.ModuliIntegralCharts.CF p where
  C := c.S
  norm_p := c.norm_p

def intO (C : Type) [NormedField C] [IsUltrametricDist C] : Subring C where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a + b‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

end Formalism.MainNotions.DIV.Cons
