module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
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

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def segreJoin {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    (Σ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) → Ω :=
  IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (NumbersDVR.segreVec y)) y

def SegreBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (segreJoin y) (Sum.inl ()) ∧
      (∀ β : K → ℤ, secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) = secOver S y β) ∧
      ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
        GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) η ↔ GeneratesOver S y β η

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
