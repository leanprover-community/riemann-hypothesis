module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def CC (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) := ZN Z ∩ Bz Z


open Classical in
def zpart (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  if h : ∃ c ∈ Z, IsNilpotent (x - c) then h.choose else 0

structure IsLat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (L : AddSubgroup (Matrix (Fin n) (Fin n) k)) : Prop where
  sub : (L : Set (Matrix (Fin n) (Fin n) k)) ⊆ Z
  cpt : IsCompact (L : Set (Matrix (Fin n) (Fin n) k))
  nhd : ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) k) ∈ U ∧ U ∩ Z ⊆ L
  int : ∀ a : k, ValuativeRel.valuation k a ≤ 1 → ∀ x ∈ L, a • x ∈ L

end PositivityTheory.RgUd.TP.Nil.Fib1
