module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CharacterExtendsToGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjPlaceUnderEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DualBaseChangeOfFrobeniusDualityOfConjUnder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteCharacterOfAlgebraicCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusDualityComplexConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobOfProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NormCharacterOfFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exDownC_sv_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : ExDownC := by
  have hA0 := _root_.UpperTheory.V.Af.algOfCyc_s H
  have hTo := UpperTheory.cyclotomicCharacter_plusPart hA0 UpperTheory.cyclotomic_char_conj_invariant
  have hDual := UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder UpperTheory.frobeniusDuality_complexConj UpperTheory.complexConj_place_under_eq
  have hNorm := _root_.UpperTheory.norm_character_of_printed_char_frobenius H.toClassicalTheorems UpperTheory.galois_character_frobenius_compatibility
  have hFin := UpperTheory.finiteCharacter_of_algebraic_cyclotomic hA0
  have hExt := UpperTheory.character_extends_to_galois_group
  have hEig := UpperTheory.hecke_eigenvalue_basic_properties
  have hSign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l _ ι n hn r π sat' inf' hpol hreg hc' hbc hatt
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := hTo K Ω l ι n r hpol
  have huniq : ∀ w B B', sat' w B → sat' w B' → B = B' := by
    rcases hc' with ⟨_, Q, rfl, -⟩ | ⟨_, Q, rfl, -⟩
    · exact fun _ _ _ h h' => h.unique h'
    · exact fun _ _ _ h h' => TR.CuspSub.HasSat.unique h h'
  have hbc' := hDual K M Ω l ι n r π sat' huniq hbc hatt μ χ c P hμ hc hP
  obtain ⟨η, hη, hev⟩ := (cyc K M hp inferInstance n hn).2.2 _ _ sat' inf'
    (Or.inl ⟨inferInstance, π, rfl, rfl⟩) hc' hbc _ _ (Or.inl ⟨inferInstance, _, rfl, rfl⟩) hbc'
  obtain ⟨δ, hδ, hδe⟩ := hNorm K M Ω l ι η hη
  obtain ⟨δ', hδ', hδc, hδo⟩ := hExt K M Ω l δ hδ
  have hA := (_root_.UpperTheory.V.Af.algOfCyc_s H (maximalRealSubfield K) Ω l ι).2.1
  have h1 : IsAlgChar ι μ := ⟨χ, hμ⟩
  have h2 := hFin.1 _ Ω l ι δ' hδo
  obtain ⟨χ', hχ'⟩ := (hA _ _ h1 (hA _ _ h2 h2).2).1
  have hs' : SameSign (μ * δ'⁻¹) := fun a b ha hb => by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, hδc a ha, hδc b hb, hs a b ha hb]
  have hd : GlobalTheory.ContraPair.DualIsConjBy π (compNorm K χ') := by
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk K n hn π _ ?_
    have h3 := (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hev
    filter_upwards [Bc.normGal K Ω l ι χ μ hμ, Bc.normGal K Ω l ι χ' _ hχ', hev, h3, hδe] with w ⟨hu, he⟩ ⟨hu', he'⟩
      ⟨_, B, hB, hB₁⟩ ⟨_, B', hB', _⟩ hw
    refine ⟨hu', B, B', hB, hB', ?_⟩
    have e1 : (μ * δ'⁻¹).comp (res (maximalRealSubfield K) Ω K) = μ.comp (res (maximalRealSubfield K) Ω K) * δ⁻¹ := by
      rw [← hδ']
      rfl
    rw [e1] at he'
    have e2 := (hEig K Ω l ι w).2.1 _ _ _ he' ((hEig K Ω l ι w).1 _ _ _ _ he hw)
    have e3 := hB₁.unique (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) w _ hu (UpperTheory.theta_satake_parameters_inverse K n π w B' hB'))
    have e4 := congrArg (Multiset.map (· * ((compNorm K χ).val w)⁻¹)) e3
    simp only [Multiset.map_map, Function.comp_def, mul_inv_cancel_right] at e4
    rw [← e4, e2]
    refine Multiset.map_congr rfl fun a _ => ?_
    rw [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨_, R, _, _, _, hR, hatt', -⟩ := _root_.UpperTheory.Gal.SV.exCS_of_prints H.toClassicalTheorems K Ω l ι n hn π χ' hreg (hSign _ Ω l ι χ' _ hχ' hs') hd
  exact ⟨R, hR.cont, hatt'⟩
end UpperTheory.V.Z.Bc
end
