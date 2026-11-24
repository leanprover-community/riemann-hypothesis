module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

def FibreClosedComponent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        W.IsMaximal →
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) = 0

def FibreCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O))
    (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ¬ W.IsMaximal →
          ∃ (P' W' : Ideal (MvPolynomial (Fin n) O)) (f : MvPolynomial (Fin n) O),
            f ∉ P ∧ P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
            P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ ∧
            W' ∈ (P' ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧
            ringKrullDim (MvPolynomial (Fin n) O ⧸ W') + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)

def GenericFibreDrop.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P P' : Ideal (MvPolynomial (Fin n) O))
    (f : MvPolynomial (Fin n) O),
    P.IsPrime → P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ → f ∉ P →
      P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P'.map (MvPolynomial.map (algebraMap O F))) + 1

def CodimOnePrimeAvoid.Statement : Prop :=
  ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (h : B),
    h ≠ 0 → 1 ≤ ringKrullDim B →
      ∃ N : Ideal B, N.IsPrime ∧ h ∉ N ∧ ringKrullDim (B ⧸ N) + 1 = ringKrullDim B

end GroundTheory.Heights₂.Heights.Vertical
