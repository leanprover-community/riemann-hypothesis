module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]


variable {ι}



variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]



variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]


section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements


variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
