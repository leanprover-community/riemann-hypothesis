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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

theorem gFac_pf : FinFac → DropP → GFac := by
  intro hF hD E _ _ _ n ι _ s
  obtain ⟨p, hp⟩ := hF E n ι s
  refine ⟨p, fun m x y => ?_⟩
  have hd := hD E n ι s m
  rw [hd x y]
  simp only [hd (ac E n (ldet x) * p.x _) y, Gk, ContinuousLinearMap.comp_apply]
  have hmem : ∀ i, (piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i)) ∈ piSp s.D s.π ι := fun i =>
    Submodule.starProjection_apply_mem _ _
  calc _ = ∑ i, ∑ b, (p.w b).1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * p.x b) i)
          ((piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i))) :=
        Finset.sum_congr rfl fun i _ => hp _ (hmem i) x i
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
