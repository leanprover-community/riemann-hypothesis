module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqPlGwOrIsConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
