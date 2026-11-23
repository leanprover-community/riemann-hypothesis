module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBandStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcludedStatement
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := GlobalTheory.T.admA_admB_inert_band_tab D L P X C tf h
  obtain ⟨hE, hExc⟩ := GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded D L P X C tf h
  obtain ⟨hG, hH⟩ := GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab D L P X C tf h
  exact ⟨h.pass, h2, h.rank, GlobalTheory.T.admissible_table_of_local_bounds D L P X C tf h h23, GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive D L P X C tf h,
    GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    GlobalTheory.T.smallPrimeLengthBound_tab D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
