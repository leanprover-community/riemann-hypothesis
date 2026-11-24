module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmul
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ z : GA D S, (∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT) → ∀ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T z⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf (cA D e) u) → (∀ w, actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf (cA D e) w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) → (∀ w ∈ latAll S T ΛS ΛT, IsHalf (cA D e) w → actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT) → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∑ u ∈ Rr, heisO ψ S T u f₀ = (Rr.card : ℂ) • Tm (actPull (z, (1 : GA D T)) (halfInd e (latAll S T ΛS ΛT))) := by
  first | exact @GlobalTheory.HeisTranslSum.sum_heisO_base_eq | exact GlobalTheory.HeisTranslSum.sum_heisO_base_eq | (intros; apply GlobalTheory.HeisTranslSum.sum_heisO_base_eq <;> assumption)
