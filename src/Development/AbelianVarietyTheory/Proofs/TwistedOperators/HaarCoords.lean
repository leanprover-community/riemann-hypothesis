module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNBPreserves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.HaarCoords

theorem haar_coords : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure ∧ lB.IsAddHaarMeasure ∧ lC.IsAddHaarMeasure ∧ SFinite μ ∧ SFinite lB ∧ SFinite lC ∧ Measurable (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∧ ∃ ν₀ : Measure (flagN d), ν₀.IsHaarMeasure ∧ ν₀.map Subtype.val = (μ.prod (lB.prod lC)).map (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d
  obtain ⟨iU1, iU2, iU3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨-, familyMassSecondLine, iM3, iM4, -⟩ := lattice_Mx D ρ S₀.rank
  obtain ⟨-, indexCSecond, iC3, iC4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨iN1, iN2, iN3, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have hcl : IsClosed ((skewA D ρ : Set (Mx D ρ ρ))) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : T2Space (skewA D ρ) := inferInstance
  let μ : Measure (UX D ρ) := Measure.haar
  let lB : Measure (Mx D ρ S₀.rank) := Measure.addHaar
  let lC : Measure (skewA D ρ) := Measure.addHaar
  obtain ⟨e, he⟩ := GlobalTheory.MixPer.flagCoord_homeo D S S₀ ρ d
  have hΦ : (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
      Subtype.val ∘ e := funext fun p => (he p).symm
  have hem : Measurable e := e.continuous.measurable
  refine ⟨μ, lB, lC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hΦ]; exact (continuous_subtype_val.comp e.continuous).measurable
  refine ⟨(μ.prod (lB.prod lC)).map e, ?_, ?_⟩
  · haveI := Measure.IsFiniteMeasureOnCompacts.map (μ.prod (lB.prod lC)) e
    haveI : ((μ.prod (lB.prod lC)).map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
    suffices h : ((μ.prod (lB.prod lC)).map e).IsMulLeftInvariant from ⟨⟩
    refine ⟨fun g => ?_⟩
    obtain ⟨p₀, hp₀⟩ := e.surjective g
    have hg : (g : GA D S) = d.levi p₀.1.1 * (d.nB p₀.2.1 * d.nC p₀.2.2) := by rw [← hp₀, he]
    obtain ⟨⟨u', hu'⟩, b', c'⟩ := p₀
    obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.HaarCoords.transl_nB_preserves D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b'
    obtain ⟨Tc, hTc, hTc'⟩ := GlobalTheory.HaarCoords.transl_nC D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance c'
    let Ta : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) :=
      Prod.map (fun u => ⟨u', hu'⟩ * u) id
    have hTa : MeasurePreserving Ta (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) :=
      (measurePreserving_mul_left μ _).prod (MeasurePreserving.id _)
    have hT := hTa.comp (hTb.comp hTc)
    have key : (fun x => g * x) ∘ e = e ∘ (Ta ∘ Tb ∘ Tc) := by
      funext p
      apply Subtype.ext
      have h3 : ∀ q, d.levi (Ta q).1.1 * (d.nB (Ta q).2.1 * d.nC (Ta q).2.2) =
          d.levi u' * (d.levi q.1.1 * (d.nB q.2.1 * d.nC q.2.2)) := fun q => by
        simp only [Ta, Prod.map_fst, Prod.map_snd, id, Subgroup.coe_mul, map_mul, mul_assoc]
      simp only [Function.comp_apply, Subgroup.coe_mul, he]
      rw [h3, hTb', hTc', hg]
      simp only [mul_assoc]
    rw [Measure.map_map (measurable_const_mul g) hem, key, ← Measure.map_map hem hT.measurable, hT.map_eq]
  · rw [Measure.map_map continuous_subtype_val.measurable hem, hΦ]

end GlobalTheory.HaarCoords

end
