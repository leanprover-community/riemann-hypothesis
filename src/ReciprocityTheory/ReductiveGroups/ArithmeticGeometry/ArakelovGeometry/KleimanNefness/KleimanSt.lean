module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def NefOnV {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → V ≤ W →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ geoNum 1 W (fun _ => α)

def NefOnF {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsProjVarF W 1 → V ≤ W → 0 ≤ I W 1 ![α]

def KleimanNefIntersectionNonneg : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ),
    IsMultiProjPrime V → charOf V ≠ 0 →
    ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ j, NefOnV V (a j)) → 0 ≤ geoNum n V a

def KleimanNefFStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) (a : Fin n → K → ℤ),
    IsFieldIntersection I → IsProjVarF V n → (∀ j, NefOnF I V (a j)) → 0 ≤ I V n a

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
