module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.OrthOrIso
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem orth_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {U U' : Submodule ℂ H}
    (h : U ⟂ U') : U.topologicalClosure ⟂ U'.topologicalClosure := by
  have key : ∀ {A B : Submodule ℂ H}, A ⟂ B → A.topologicalClosure ⟂ B := fun {A B} hAB =>
    Submodule.isOrtho_iff_le.2
      (Submodule.topologicalClosure_minimal _ (Submodule.isOrtho_iff_le.1 hAB) (Submodule.isClosed_orthogonal B))
  exact (key (key h).symm).symm

theorem UpperTheory.ConvolutionTheory.Dp.multiplicity_one_cuspidal_spectrum_normOneGL :
    UpperTheory.ConvolutionTheory.C.CuspidalMultiplicityOneTotallyComplex := by
  intro E _ _ _ n μ _ V V' hV hV' hne
  obtain ⟨π, hπ⟩ := ExistsUnique.exists (exCusp E n μ V hV)
  obtain ⟨π', hπ'⟩ := ExistsUnique.exists (exCusp E n μ V' hV')
  obtain ⟨hs, -, hi, hc⟩ := formsIrr E n μ V hV
  obtain ⟨hs', -, hi', hc'⟩ := formsIrr E n μ V' hV'
  rw [← hπ.carrier_eq] at hs hi hc
  rw [← hπ'.carrier_eq] at hs' hi' hc'
  have hle : Cm.carrier π ≤ centralCuspForms E n := hπ.carrier_eq ▸ inf_le_left
  have hle' : Cm.carrier π' ≤ centralCuspForms E n := hπ'.carrier_eq ▸ inf_le_left
  rcases orthOrIso E n μ _ _ hle hle' hs hs' hi hi' with h | ⟨T, hρ, hσ, hτ⟩
  · rw [← hc, ← hc']
    exact orth_closure h
  · refine (hne ((isoIff E n μ π π' V V' hπ hπ').1 ?_)).elim
    refine ⟨((Cm.carrierEq π).symm.trans T).trans (Cm.carrierEq π'), fun o φ => ?_⟩
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective φ
    cases o with
    | fin k =>
      simp only [← Cm.carrierEq_τ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact congrArg _ (Subtype.ext (hτ k ψ _ rfl))
    | cpt k =>
      simp only [← Cm.carrierEq_σ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact congrArg _ (Subtype.ext (hσ _ ψ _ rfl))
    | lie X =>
      simp only [← Cm.carrierEq_ρ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact congrArg _ (Subtype.ext (hρ _ ψ _ rfl))
