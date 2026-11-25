module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsNhdsInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryHypotheses

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open Filter Topology NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.Ar.RT.Move

theorem indicator_mem {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) {Φ : X → ℂ} (h : Φ ∈ SB X) :
    U.indicator Φ ∈ SB X := by
  classical
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.mono (fun x hx => ?_)⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hU.isOpen.mem_nhds hx, h1.eventually_eq x] with y hy hy'
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy']
    · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · by_cases hxU : x ∈ U
    · simpa [Function.mem_support, hxU] using hx
    · simp [Function.mem_support, hxU] at hx

theorem kill {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Y₁ : X)
    (h : ∀ Y ≠ Y₁, ∃ m : X → ℂ, IsLocallyConstant m ∧ m Y ≠ m Y₁ ∧ ∀ Φ ∈ SB X, (fun y => (m y - m Y₁) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, Φ Y₁ = 0 → Φ ∈ N := by
  classical
  intro Φ hΦ hΦ0
  let mm : X → X → ℂ := fun Y => if hY : Y = Y₁ then 0 else Classical.choose (h Y hY)
  have hmm : ∀ Y, Y ≠ Y₁ → IsLocallyConstant (mm Y) ∧ mm Y Y ≠ mm Y Y₁ ∧
      ∀ Φ ∈ SB X, (fun y => (mm Y y - mm Y Y₁) * Φ y) ∈ N := by
    intro Y hY
    simp only [mm, dif_neg hY]
    exact Classical.choose_spec (h Y hY)
  let U : X → Set X := fun Y => {y | mm Y y ≠ mm Y Y₁}
  have hUc : ∀ Y, Y ≠ Y₁ → IsClopen (U Y) := by
    intro Y hY
    exact ((hmm Y hY).1.isClopen_fiber (mm Y Y₁)).compl
  have key : ∀ (s : Finset X), (∀ Y ∈ s, Y ≠ Y₁) → ∀ Ψ ∈ SB X,
      Function.support Ψ ⊆ ⋃ Y ∈ s, U Y → Ψ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Ψ _ hs
      have h0 : Ψ = 0 := by
        ext x
        by_contra hx
        have := hs hx
        simp at this
      rw [h0]
      exact N.zero_mem
    | insert Y s hYs ih =>
      intro hne Ψ hΨ hs
      have hY : Y ≠ Y₁ := hne Y (Finset.mem_insert_self _ _)
      have hsplit : Ψ = (U Y).indicator Ψ + (U Y)ᶜ.indicator Ψ :=
        (Set.indicator_self_add_compl _ _).symm
      rw [hsplit]
      refine N.add_mem ?_ ?_
      · obtain ⟨hlc, _, hN⟩ := hmm Y hY
        have hg : IsLocallyConstant (fun y => (mm Y y - mm Y Y₁)⁻¹) :=
          hlc.comp (fun a => (a - mm Y Y₁)⁻¹)
        have hΨg : (Ψ * fun y => (mm Y y - mm Y Y₁)⁻¹) ∈ SB X := ⟨hΨ.1.mul hg, hΨ.2.mul_right⟩
        have hI := hN _ (indicator_mem (hUc Y hY) hΨg)
        convert hI using 1
        ext y
        by_cases hy : y ∈ U Y
        · have hy' : mm Y y - mm Y Y₁ ≠ 0 := sub_ne_zero.mpr hy
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          simp only [Pi.mul_apply]
          field_simp
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
      · refine ih (fun Z hZ => hne Z (Finset.mem_insert_of_mem hZ)) _
          (indicator_mem (hUc Y hY).compl hΨ) ?_
        intro x hx
        rw [Set.support_indicator] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have := hs hx2
        simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop] at this ⊢
        obtain ⟨Z, hZ, hxZ⟩ := this
        rcases hZ with rfl | hZ
        · exact absurd hxZ hx1
        · exact ⟨Z, hZ, hxZ⟩
  have hcl : IsClosed (Function.support Φ) := (hΦ.1.isClopen_fiber 0).isOpen.isClosed_compl
  have hS : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset hcl (subset_tsupport Φ)
  have hne : ∀ x ∈ Function.support Φ, x ≠ Y₁ := by
    rintro x hx rfl
    exact hx hΦ0
  have hnhds : ∀ x ∈ Function.support Φ, U x ∈ 𝓝 x := fun x hx =>
    (hUc x (hne x hx)).isOpen.mem_nhds (hmm x (hne x hx)).2.1
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover U hnhds
  exact key t (fun Y hY => hne Y (ht Y hY)) Φ hΦ hcov

theorem lc_of_mul {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (m : X → ℂ)
    (h : ∀ Φ ∈ SB X, (fun y => m y * Φ y) ∈ SB X) : IsLocallyConstant m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨V, hVc, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKx
  have hVc' : IsClopen V := hVc
  have hVcomp : IsCompact V := hK.of_isClosed_subset hVc'.1 hVK
  have hΦ : V.indicator (1 : X → ℂ) ∈ SB X := by
    refine ⟨?_, HasCompactSupport.intro hVcomp (fun y hy => Set.indicator_of_notMem hy _)⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    by_cases hz : z ∈ V
    · filter_upwards [hVc'.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · filter_upwards [hVc'.compl.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]
  have hm := (h _ hΦ).1.eventually_eq x
  filter_upwards [hm, hVc'.isOpen.mem_nhds hxV] with y hy hyV
  simpa [Set.indicator_of_mem hyV, Set.indicator_of_mem hxV] using hy

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def ballAt (M : ℕ) (c : κ → Af F) (v : Pl F) : Set (κ → Fv F v) :=
  {z | ∀ i, Valued.v (z i - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}

def box (M : ℕ) (c : κ → Af F) (y : κ → Af F) : ℂ := ∏ᶠ v, (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) fun i => evalV F v (y i)

def Near (M : ℕ) (c y : κ → Af F) : Prop := ∀ v i, Valued.v (evalV F v (y i) - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)

theorem schA_le (L : Submodule ℂ ((κ → AF F) → ℂ))
    (hL : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ L) :
    schA F κ ≤ L :=
  by apply _root_.GlobalTheory.ThetaInterchange.schA_le_of_pure <;> assumption

end PositivityTheory.KCo
