module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxPoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          (W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W) ∧
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

def BlowUpOverLocPointMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpLocRingInj.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q Q' : Ideal (MRing (extIdx ι J) R)),
    Q.IsPrime → IsMultiHomogIdeal Q → IsRelevant Q → blowUpOf P u ≤ Q →
    Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' → blowUpOf P u ≤ Q' →
    blowUpLocRing P u Q = blowUpLocRing P u Q' → Q = Q'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
