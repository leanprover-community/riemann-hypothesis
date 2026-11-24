module

public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinEtSectionPf

def Pieces : Prop := LateralTheory.E.t_E1Cut.EtLift → LateralTheory.E.t_E1Cut.EtAIC → ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C], LateralTheory.E.t_E1Cut.QA S →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))))

def FinOpen : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C), IsIdempotentElem e →
  IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) →
  ∃ ε : S, IsIdempotentElem ε ∧
    Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum S)) ∧
    ∃ h : Localization.Away e →+* Localization.Away ε,
      h.comp ((algebraMap C (Localization.Away e)).comp (algebraMap S C)) = algebraMap S (Localization.Away ε)

def Glue : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] (n : ℕ) (e : Fin n → C),
  CompleteOrthogonalIdempotents e → Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) →
  ∀ ε : Fin n → S, (∀ j, IsIdempotentElem (ε j)) →
  (∀ j, Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))) →
  (∀ j, ∃ h : Localization.Away (e j) →+* Localization.Away (ε j),
      h.comp ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C)) = algebraMap S (Localization.Away (ε j))) →
  Nonempty (C →ₐ[S] S)

theorem FinEtSection_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) (hP : Pieces) (hF : FinOpen) (hG : Glue) : LateralTheory.E.t_E1Cut.FinEtSection := by
  intro S C _ _ _ _ _ hQA hsurj
  obtain ⟨n, e, he, hoi⟩ := hP hL hA S C hQA
  choose ε hε hr hh using fun j => hF S C (e j) (he.idem j) (hoi j)
  exact hG S C n e he hsurj ε hε hr hh

end LateralTheory.E.FinEtSectionPf
