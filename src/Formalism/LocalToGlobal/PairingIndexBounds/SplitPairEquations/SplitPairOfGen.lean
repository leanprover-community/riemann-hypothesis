module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.BasicNotions.D7) : SquareSplitPairs.SplitPair D := by
  letI := D.host.cmStar
  intro N' L' L'' hN h1 h2 n hn
  exact h D.host.E D.sp.cm.cmUnram N' L' L'' hN h1 h2 n hn

theorem eqP_gen {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

end Formalism.L2.PairingIndexBounds.Eq.SqG
