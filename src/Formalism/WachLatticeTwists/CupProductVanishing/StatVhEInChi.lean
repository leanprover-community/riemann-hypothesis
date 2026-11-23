module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import ReciprocityTheory.GaloisValuations.Global
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatVhE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] KO O) →
    ∀ (ρ : Representation O (G E Ω) M), (∀ g m, ρ g m = m) →
    ∀ S : Submodule O (H1z ρ),
      (∀ x ∈ S, ∃ z : coZ1s ρ, Submodule.mkQ _ z = x ∧ IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, S ≤ unrH1 ρ (Ine (F := E) (Av v))) →
      Module.length O S ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

def StatVhEInChi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
      (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M],
      Nonempty (M ≃ₗ[O] KO O) →
    ∀ (r : G E Ω →* A) (χ : G E Ω →* T'ˣ), (∀ g (m : M), uElt r χ g • m = m) →
    ∀ (D : ℕ → Subgroup (G E Ω)) (places : Finset ℕ)
      (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
      (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup (G E Ω)) (IS : VS → Subgroup (G E Ω)),
      (∀ x ∈ HcG, ∃ z : coZ1s (uRep O (M := M) r χ), Submodule.mkQ _ z = x ∧
        IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, (∃ a, Ine (F := E) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := E) (Av v) ≤ IS a) ∨
        ∃ w ∈ places, ∃ I : Subgroup (D w), F w ≤ unrH1 (resRep (uRep O (M := M) r χ) (D w)) I ∧
          Ine (F := E) (Av v) ≤ I.map (D w).subtype) →
      Module.length O ↥((HcG ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
          ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
        ⨅ w ∈ places, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.T2
