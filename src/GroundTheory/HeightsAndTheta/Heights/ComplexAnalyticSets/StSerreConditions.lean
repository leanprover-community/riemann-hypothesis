module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def SerreRAt (B : Type*) [CommRing B] (k : ℕ) : Prop :=
  ringKrullDim B ≤ (k : WithBot ℕ∞) → IsRegularLocalRing B

def SerreSAt (B : Type*) [CommRing B] [IsLocalRing B] (k : ℕ) : Prop :=
  ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ IsWeaklyRegular B rs ∧
    min (k : WithBot ℕ∞) (ringKrullDim B) ≤ (rs.length : WithBot ℕ∞)

def SerreR (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreRAt (Localization.AtPrime P) k

def SerreS (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreSAt (Localization.AtPrime P) k

def NormalRing (A : Type*) [CommRing A] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)

theorem primeFibreLocalRing_ideal_ne_top (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] :
    Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≠ ⊤ := by
  intro h
  have hle : Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≤ maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono Ideal.map_comap_le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

instance primeFibreLocalRing.isLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] : IsLocalRing (primeFibreLocalRing R P) := by
  have : Nontrivial (primeFibreLocalRing R P) :=
    Ideal.Quotient.nontrivial_iff.mpr (primeFibreLocalRing_ideal_ne_top R P)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
