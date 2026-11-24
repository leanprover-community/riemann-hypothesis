module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairNumberExpansionIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (f g : Fin n → MRing ι O),
      (∀ i, IsVerticalDivisor P ϖ (z i - z' i) (f i) (g i)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin n) ℤ), A.IsHomogeneous m →
    ∀ (As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ), IsPairExpansion m A As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum P z z' f g As Q = pairNum P z z' f g Bs Q

def hsymmTimes (N n a : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (N + n)) ℤ :=
  rename (Fin.castAdd n) (hsymm (Fin N) ℤ a) * rename (Fin.natAdd N) R

def HsymmPairFlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ (As Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
      IsPairExpansion (a + r) (hsymmTimes N n a R) Bs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        pairNum (pointIdeal O y) (Fin.append u z) (Fin.append u' z') (Fin.append f₂ fz)
          (Fin.append g₂ gz) Bs Q

def SymmetricSpanHsymm.Statement : Prop :=
  ∀ (N m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    G ∈ Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
