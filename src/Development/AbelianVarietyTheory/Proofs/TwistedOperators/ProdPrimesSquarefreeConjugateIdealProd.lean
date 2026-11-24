module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory

theorem primeProd_conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (I : Ideal (𝓞 E)) :
    conjI I = I.map (RingOfIntegers.mapRingHom ((IsCMField.complexConj E).toRingEquiv.toRingHom)) := by
  unfold conjI
  show _ = Ideal.span _
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem primeProd_squarefree_le_conj : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), Squarefree (∏ PP ∈ P, PP.asIdeal) ∧ (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (∏ PP ∈ P, PP.asIdeal) ≤ PP'.asIdeal ↔ PP' ∈ P) ∧ conjI (∏ PP ∈ P, PP.asIdeal) = ∏ PP ∈ P, conjI PP.asIdeal := by
  intro D P
  refine ⟨?_, ?_, ?_⟩
  · have hprod : (∏ PP ∈ P, PP.asIdeal) = (P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal)).prod := by
      rw [Finset.prod_eq_multiset_prod]
    have hprime : ∀ p ∈ P.val.map (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal), Prime p := by
      intro p hp
      obtain ⟨PP, -, rfl⟩ := Multiset.mem_map.1 hp
      exact PP.prime
    have hne : (∏ PP ∈ P, PP.asIdeal) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro PP _
      exact PP.ne_bot
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne, hprod,
      UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime]
    exact (Multiset.nodup_map_iff_of_injective (fun a b h => HeightOneSpectrum.ext h)).2 P.nodup
  · intro PP'
    constructor
    · intro hle
      obtain ⟨PP, hPP, hle'⟩ := (Ideal.IsPrime.prod_le PP'.isPrime).1 hle
      have : PP.asIdeal = PP'.asIdeal := PP.isMaximal.eq_of_le PP'.isPrime.ne_top hle'
      have h2 : PP = PP' := HeightOneSpectrum.ext this
      exact h2 ▸ hPP
    · intro h
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ h)
  · simp only [primeProd_conjI_eq_map]
    exact map_prod (Ideal.mapHom _) _ _

end GlobalTheory
