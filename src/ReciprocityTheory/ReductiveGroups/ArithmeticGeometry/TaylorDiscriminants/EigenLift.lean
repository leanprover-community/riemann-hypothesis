module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
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

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def BetaSesqSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)),
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)

def EigenOrthSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (χ χ' : O → k) (ξ η : (Fin d → k) × (Fin d → k)),
    (∀ a, OactH k B a ξ = χ a • ξ) → (∀ a, OactH k B a η = χ' a • η) →
    (∃ a, IsUnit (χ a - χ' (star a))) → betaH k ξ η = 0

end ReciprocityTheory.ChartRestriction.G.TB
