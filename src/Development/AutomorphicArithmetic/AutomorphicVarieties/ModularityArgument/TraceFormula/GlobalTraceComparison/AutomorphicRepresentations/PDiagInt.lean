module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm
