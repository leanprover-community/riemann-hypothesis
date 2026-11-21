import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMasses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClasses

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectShare

lemma tsum_subtype_le {α : Type} (P : α → Prop) (s : Set α) (hs : ∀ a, P a → a ∈ s) (f : α → ℝ≥0∞)
    (c N : ℝ≥0∞) (hf : ∀ a, P a → f a ≤ c) (hN : (s.encard : ℝ≥0∞) ≤ N) :
    ∑' a : {a // P a}, f a ≤ N * c := by
  calc ∑' a : {a // P a}, f a ≤ ∑' _ : ({a | P a} : Set α), c :=
        ENNReal.tsum_le_tsum fun a => hf a.1 a.2
    _ = (({a | P a} : Set α).encard : ℝ≥0∞) * c := ENNReal.tsum_set_const _ _
    _ ≤ N * c := by
        gcongr
        refine le_trans ?_ hN
        exact_mod_cast Set.encard_le_encard (fun a ha => hs a ha)

theorem share_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (C : Set S.FrP) (hC : S.IsCls C) (β : ℕ) (_hβ : 1 ≤ β) :
    (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤
      ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) *
        S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ ∧ S.Fr d Λ = C
  swap
  · have h0 : (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) = 0 := by
      unfold Frames.sumData
      refine ENNReal.tsum_eq_zero.2 fun o => ?_
      have : ({Λ | S.IsTerm o.out Λ ∧ S.be o.out Λ = β ∧ S.Fr o.out Λ = C} :
          Set (Submodule L.O S.V)) = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h3⟩
        exact h ⟨_, _, h1, h3⟩
      simp [Frames.nT, this]
    rw [h0]
    exact zero_le
  obtain ⟨d, Λ, hT, hFr⟩ := h
  obtain ⟨hSD, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have ha : 0 ≤ S.a := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).1
  have hp : (S.fr d Λ, S.fr' d Λ) ∈ C := by
    rw [← hFr]
    exact (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ, hSD⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC _ hp
  have h3 := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC _ hp ha
  have hlow : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.Mof (S.fr d Λ) (S.fr' d Λ)) := by
    have := (hU C hC _ hp _ le_rfl (fun x hx => (hM hx).2)
      (fun x hx y hy => (hSD.2 y).2 (hM hy).1 x (hM hx).1)).1
    simpa using this
  rw [h2]
  refine (h1 fun n => n = β).trans ?_
  refine (tsum_subtype_le _ _ (fun Mh hMh => ?_) S.massSig
    (ENNReal.ofReal (2 * κ * ((β : ℝ) ^ (k - 1))⁻¹)) _ (fun Mh hMh => ?_) h3).trans ?_
  · exact ⟨hMh.1, hMh.2.1, hMh.2.2.1⟩
  · have := (hU C hC _ hp Mh hMh.1 hMh.2.1 hMh.2.2.1).2
    rw [hMh.2.2.2] at this
    exact this
  · refine le_trans (le_of_eq ?_) (mul_le_mul_right hlow _)
    have hz : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = (S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2)) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      rw [Int.toNat_of_nonneg ha]
    have hq : (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) =
        ENNReal.ofReal ((S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    rw [hz, hq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.HL.DefectShare
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_defectOrder_share_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ C, S.IsCls C → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) * S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  atlas_forward_decl GlobalTheory.HL.DefectShare.share_le
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DefectShare

theorem mass_defect_order_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β hβ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ
  swap
  · have h0 : (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) = 0 := by
      have : ∀ d Λ, ¬ S.IsTerm d Λ := fun d Λ h => hex ⟨d, Λ, h⟩
      simp [Frames.sumData, Frames.mass, this]
    rw [h0]; exact zero_le
  obtain ⟨d0, Λ0, h0⟩ := hex
  obtain ⟨-, -, -, hq, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d0 Λ0 h0
  have hconst : 4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹ ≤
      (4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹ := by
    have e : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = ((S.q : ℝ) ^ S.a) ^ (4 * (r + 1)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e]
    have hn : (0 : ℝ) ≤ (S.q : ℝ) ^ S.a := zpow_nonneg (Nat.cast_nonneg _) _
    gcongr
  have s1 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun d Λ => S.be d Λ = β) (fun h hh d Λ hT hP => by
    have := (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.1
    exact this.trans hP)).1
  have s2 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)).1
  unfold Frames.nn
  rw [s1, s2]
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with hC
  · rw [mul_left_comm]
    refine mul_le_mul_right ?_ _
    refine (GlobalTheory.T.hermitianFrames_defectOrder_share_le L r k S hk _ hC.1 β hβ).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) ?_
    unfold Frames.sumData
    refine ENNReal.tsum_le_tsum fun o' => mul_le_mul' le_rfl ?_
    unfold Frames.nT
    exact ENat.toENNReal_le.mpr (Set.encard_le_encard fun Λ h => ⟨h.1, trivial, h.2.2⟩)
  · exact zero_le

end GlobalTheory.DefectShare
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumData_mass_be_eq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  atlas_forward_decl GlobalTheory.DefectShare.mass_defect_order_le
end
