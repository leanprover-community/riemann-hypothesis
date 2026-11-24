module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ := by
  exact Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)
    (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
