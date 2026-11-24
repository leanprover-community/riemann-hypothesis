module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem restrict_dvr_essFiniteType : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hL0 := GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex
  have hL1 := GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional
  have hL2 := GlobalTheory.T.dvr_eq_localization_integralClosure_comap
  have hL4 := GlobalTheory.T.fractions_unitDenominators_replace_generators
  have hL3 := GlobalTheory.T.zariski_descent_dvr_trace_localisation
  intro K L _ _ φ c hfin V _ hc hV
  have hE : IsDiscreteValuationRing (V.comap φ) := hL1 K L φ hfin V
  haveI : CharZero K := RingHom.charZero_iff c.injective |>.mp inferInstance
  obtain ⟨s₀, hs₀V, hs₀⟩ := hL0 L (φ.comp c) V hc hV
  obtain ⟨t, ht, htV⟩ := hL4 L (φ.comp c) V
    (fun x => x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) s₀
    (fun x hx => hL2 K L φ hfin V hE x (hs₀V x hx)) hs₀
  exact ⟨hE, hL3 K L φ c hfin V hc t ht htV⟩

end GlobalTheory
