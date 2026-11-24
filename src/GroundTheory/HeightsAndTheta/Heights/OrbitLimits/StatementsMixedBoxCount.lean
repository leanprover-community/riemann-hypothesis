module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding


open scoped Classical in
def MixedBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F)) [DiscreteTopology La]
    [IsZLattice ℝ (E := mixedSpace F) La] (f : InfinitePlace F → ℝ), (∀ w, 0 < f w) →
      {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite ∧
        Real.log (convexBodyLTFactor F : ℝ) + ∑ w, (mult w : ℝ) * Real.log (f w) -
            Module.finrank ℚ F * Real.log 2 - Real.log (ZLattice.covolume La) ≤
          Real.log ({y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.ncard : ℝ)

end GroundTheory.Heights₂.Heights.Targets
