module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkRam
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.minkGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], (⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ)) = ⊤ := by
  intro K _ _ _
  set I : Subgroup Gal(K/ℚ) := ⨆ w : HeightOneSpectrum (𝓞 K), w.asIdeal.inertia Gal(K/ℚ) with hI
  have hconj : ∀ (τ : Gal(K/ℚ)) (w : HeightOneSpectrum (𝓞 K)), ∃ w' : HeightOneSpectrum (𝓞 K),
      ∀ σ ∈ w.asIdeal.inertia Gal(K/ℚ), τ * σ * τ⁻¹ ∈ w'.asIdeal.inertia Gal(K/ℚ) := by
    intro τ w
    refine ⟨⟨τ • w.asIdeal, by haveI := w.isPrime; infer_instance, ?_⟩, ?_⟩
    · intro h
      apply w.ne_bot
      rw [eq_bot_iff]
      intro x hx
      have hx' : τ • x ∈ τ • w.asIdeal := Ideal.smul_mem_pointwise_smul τ x _ hx
      rw [h, Ideal.mem_bot] at hx'
      rw [Ideal.mem_bot]
      exact (smul_eq_zero_iff_eq τ).mp hx'
    · intro σ hσ x
      have hm := Ideal.smul_mem_pointwise_smul τ _ w.asIdeal (hσ (τ⁻¹ • x))
      rwa [smul_sub, smul_inv_smul, ← mul_smul, ← mul_smul] at hm
  haveI hN : I.Normal := by
    constructor
    intro σ hσ τ
    have hle : I ≤ I.comap (MulAut.conj τ).toMonoidHom := by
      refine iSup_le fun w => ?_
      obtain ⟨w', hw'⟩ := hconj τ w
      intro σ' hσ'
      exact le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w' (hw' σ' hσ')
    exact hle hσ
  set F := IntermediateField.fixedField I with hF
  haveI hFgal := IsGalois.of_fixedField_normal_subgroup I
  haveI hgF : IsGalois ℚ F := by
    convert hFgal
  have hunr : ∀ p, Nat.Prime p → UnramAt F p := by
    intro p hp
    refine (UpperTheory.V.CF.ineFixQ F K p hp).mpr ?_
    intro w _ σ hσ
    rw [MonoidHom.mem_ker]
    ext x
    rw [AlgEquiv.one_apply]
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F K σ x
    exact hc.trans ((IntermediateField.mem_fixedField_iff I _).mp x.2 σ
      (le_iSup (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.inertia Gal(K/ℚ)) w hσ))
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra h
    obtain ⟨p, hp, hnot⟩ := UpperTheory.V.CF.minkRam F h
    exact hnot (hunr p hp)
  have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField I, ← hF, hbot,
    IntermediateField.fixingSubgroup_bot]
