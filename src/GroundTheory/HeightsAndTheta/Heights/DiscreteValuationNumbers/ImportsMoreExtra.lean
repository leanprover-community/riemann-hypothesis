module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsProjVarF)

def VerticalDivisorSupportFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRingOver O ι)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W : Ideal (MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g W ≠ 0 →
      IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
