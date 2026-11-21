import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionHyperplaneAvoid
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SectionHyperplaneAvoid

def linFormMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  Fintype.linearCombination ℂ (fun j => (X j : MvPolynomial (Fin n) ℂ))

theorem linFormMap_apply {n : ℕ} (ℓ : Fin n → ℂ) : linFormMap n ℓ = linForm ℓ := by
  simp [linFormMap, linForm, Fintype.linearCombination_apply, C_mul']

def formSpace {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) : Submodule ℂ (Fin n → ℂ) :=
  (I.restrictScalars ℂ).comap (linFormMap n)

theorem mem_formSpace {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} :
    ℓ ∈ formSpace I ↔ linForm ℓ ∈ I := by
  simp [formSpace, linFormMap_apply]

theorem formSpace_ne_top {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : IsRelevant I) :
    formSpace I ≠ ⊤ := by
  obtain ⟨j, hj⟩ := hI
  intro htop
  have h : Pi.single j 1 ∈ formSpace I := htop ▸ Submodule.mem_top
  rw [mem_formSpace] at h
  apply hj
  have : linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by
    rw [← linFormMap_apply]
    simp [linFormMap, Fintype.linearCombination_apply, Pi.single_apply]
  rwa [this] at h

theorem isRelevant_of_mem_support {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : W ∈ (divCycle J u).support) : IsRelevant W := by
  rw [Finsupp.mem_support_iff] at hW
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply] at hW
  by_contra h
  exact hW (if_neg fun h' => h h'.2)

theorem proof : SectionHyperplaneAvoid.Statement := by
  intro n J u hJ
  let p : Option (divCycle J u).support → Submodule ℂ (Fin n → ℂ) :=
    fun o => o.elim (formSpace J) (fun W => formSpace W.1)
  have hp : ∀ o, p o ≠ ⊤ := by
    rintro (_ | ⟨W, hW⟩)
    · exact formSpace_ne_top hJ.isRelevant
    · exact formSpace_ne_top (isRelevant_of_mem_support hW)
  have hcov : ⋃ o, (p o : Set (Fin n → ℂ)) ≠ Set.univ := fun h =>
    (Subspace.exists_eq_top_of_iUnion_eq_univ h).elim hp
  obtain ⟨ℓ, hℓ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcov
  simp only [Set.mem_iUnion, not_exists, SetLike.mem_coe] at hℓ
  refine ⟨ℓ, fun h => hℓ none (mem_formSpace.mpr h), fun W hW h => hℓ (some ⟨W, hW⟩) ?_⟩
  exact mem_formSpace.mpr h

end SectionHyperplaneAvoid

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

theorem FormIntLelong.proof (hCP : ConeToProjective.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) (hFS : FormIntSlice.Statement)
    (hSL : SliceFormLelong.Statement) : FormIntLelong.Statement := by
  intro n e h W u u' δ hW hg hu' hδ
  obtain ⟨F, hF⟩ := hg
  obtain ⟨ℓ, hℓW, hℓP⟩ := SectionHyperplaneAvoid.proof n W u' hW
  have ha0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → fsLogReg h u δ (t • x) = fsLogReg h u δ x :=
    fun t x ht => fsLogReg_smul h u δ t x ht
  have ha1 : ContDiffOn ℝ ∞ (fsLogReg h u δ) {x | x ≠ 0} := contDiffOn_fsLogReg h u hδ

  have hWc := hCP n (e + 1) h W F ℓ (fsLogReg h u δ) hW hF hℓW ha0 ha1.continuousOn

  obtain ⟨c, -, gP, hgP, -⟩ := hCh ℂ n (e + 1) W F u' hW hF hu'
  have hcyc : cycleIntegral h (divCycle W u') e (fsLogReg h u δ) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fsLogReg h u δ)
          (fun _ x => Real.log (h.dualNorm x)) := by
    unfold cycleIntegral
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hCP n e h P (gP P) ℓ (fsLogReg h u δ) (DivCyclePrime.proof n W u' hW P hP) (hgP P hP)
      (hℓP P hP) ha0 ha1.continuousOn]
  rw [hcyc, hWc]

  refine (hSL n e h W F u' ℓ (fsLogReg h u δ) hW hF hu' hℓW hℓP ha0 ha1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hFS n e h W F ℓ (fsLogReg h u δ) (fsLogReg h u' ε) hW hF hℓW ha0 ha1.continuousOn
    (fun t x ht => fsLogReg_smul h u' ε t x ht) (contDiffOn_fsLogReg h u' hε)).symm

end GroundTheory.Heights₂.Heights
end
