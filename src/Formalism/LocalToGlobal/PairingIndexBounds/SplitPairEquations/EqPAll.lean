module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen
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

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem eqP_all {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hP : SplitPairGen) : B.EqP χ := by
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc
    rw [← hδ, h0]
    norm_num
  exact eqP_gen B hcc hδ hδ0 hS χ hχ hP

end Formalism.L2.PairingIndexBounds.Eq.SqG
