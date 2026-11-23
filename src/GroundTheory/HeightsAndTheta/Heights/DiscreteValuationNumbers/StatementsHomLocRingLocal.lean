module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def HomLocRingMem.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    ∀ z : FractionRing (MRing ι R ⧸ P), z ∈ homLocRing P W ↔
      ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
        z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)

def HomLocRingIsLocal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    IsLocalRing (homLocRing P W) ∧
      ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
        ∀ hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ∈
              homLocRing P W,
          IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W

def HomLocRingNoetherian.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      IsNoetherianRing (homLocRing P W)

def HomLocRingDimLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      ringKrullDim (homLocRing P W) ≤ ((W.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
