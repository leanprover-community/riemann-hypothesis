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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelRootIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E')
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
      IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
    ∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₁ W d
                                (Fin.append F₁.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₁.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₁.z)) (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I₂ W d
                                (Fin.append F₂.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₂.K') (L l))
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x F₂.z)) (C a)))

end GroundTheory.Heights₂.Heights.NumbersDVR
