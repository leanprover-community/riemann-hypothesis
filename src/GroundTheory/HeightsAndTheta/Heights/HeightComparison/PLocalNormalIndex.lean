import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCentred
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem card_quot_span_eq_relIndex {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by
  have h : (Ideal.span {x}).toAddSubgroup =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [mul_comm]⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩
  rw [AddSubgroup.relIndex, ← h]
  rfl

theorem relIndex_mulLeft_eq {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hf
  have h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f) :=
    AddSubgroup.map_mono hAB
  have h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (hAB hfA) hy
  have h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.mul_mem hfA hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm] at e1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm

theorem LocalQuotCentred.proof (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalNormalIndex.proof : LocalNormalIndex.Statement := by
  intro L _ _ O hft hfr m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors
  set C := integralClosure A L
  have : Algebra.FiniteType ℤ O := hft
  have : CharZero O := ⟨fun a b h ↦ by
    have := congrArg (fun t : O ↦ (t : L)) h
    simpa using this⟩

  have hfin : Module.Finite O (integralClosure O L) :=
    Model.finite_integralClosure_fractionRing_of_charZero O L
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O)
    (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap O L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := O) (M := m.primeCompl) (Rₘ := A) x hx
    obtain ⟨o, ho⟩ := hdI _ hsx
    have hs0 : algebraMap O L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)
    simp only [Submonoid.smul_def, Algebra.smul_def] at ho
    refine ⟨o, s, hs, ?_⟩
    rw [ho]
    field_simp

  have hAC : A.toSubring ≤ C.toSubring := fun x hx ↦
    (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  set f := algebraMap O L d
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hdL
  have h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤
      C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) := AddSubgroup.map_mono hAC
  have h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdC y hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at e1
  have hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex
      A.toSubring.toAddSubgroup ≠ 0 := by
    let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
    have hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) =
        Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)}) := by
      refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact (e.commutes d).symm
    have hfL : ((algebraMap O A d : A.toSubring) : L) = f := rfl
    have hcq := card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)
    rw [hfL] at hcq
    have key : Nat.card (Localization.AtPrime m ⧸
        Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0 := by
      rw [LocalQuotCard.proof L O hft hfr m d hd0]
      refine pow_ne_zero _ ?_
      have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
        @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
          (Ideal.Quotient.mkₐ_surjective ℤ m)
      let _ : Field (O ⧸ m) := Ideal.Quotient.field m
      obtain ⟨hp, hc⟩ :=
        @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
          (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)
      rw [hc]
      exact pow_ne_zero _ hp.ne_zero
    rw [← hcq]
    exact fun h ↦ key (hq1.trans h)
  rw [← e1] at hcard
  exact left_ne_zero_of_mul hcard

end GroundTheory.Heights₂.Heights
end
