module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
