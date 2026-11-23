module

public import Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf
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
import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf
