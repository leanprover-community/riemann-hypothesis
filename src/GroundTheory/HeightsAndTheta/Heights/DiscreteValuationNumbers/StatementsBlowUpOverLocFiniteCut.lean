module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
public import Mathlib.Order.CompletePartialOrder
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {A : Type*} [CommRing A] (L : Type*) [Field L] [Algebra A L]

def blowUpColon (I : Ideal A) : Submodule A L :=
  ⨆ n : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ n / (Submodule.map (Algebra.linearMap A L) I) ^ n

end Objects

section Lemmas

def BlowUpOverLocInChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (J : Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], IsMultiHomogIdeal P → W.IsPrime → P ≤ W → IsRelevant W →
    ∀ (N : K → ℕ) (u : J → MRing ι R), (∀ j, IsMultiHomog (u j) N) → ∀ j, u j ∉ P →
      blowUpOverLoc P W u ≤ Subring.closure ((homLocRing P W : Set (FractionRing (MRing ι R ⧸ P))) ∪
        Set.range fun k =>
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)))

def ChartsInColon.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (L : Type u) [Field L] [Algebra A L] (J : Type) [Fintype J] (a : J → A) (f : L),
    (∀ j, algebraMap A L (a j) ≠ 0 →
      f ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) →
    f ∈ blowUpColon L (Ideal.span (Set.range a))

def BlowUpColonFinite.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra A L], Function.Injective (algebraMap A L) → ringKrullDim A = 1 →
    ∀ I : Ideal A, I ≠ ⊥ → (blowUpColon L I).FG

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
