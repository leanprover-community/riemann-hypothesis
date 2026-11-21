import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroDefectHeightPowerAbsorbsConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbits
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCardStatement

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NoCancellation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop) (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) :
    S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases hP : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨i, hi, hQ⟩ := h _ hP.1 hP.2
    rw [if_pos hP]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => if S.IsTerm d o.out ∧ Q i o.out then
      ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => zero_le) hi)
    exact (if_pos ⟨hP.1, hQ⟩).ge
  · rw [if_neg hP]
    exact zero_le

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S {()} d P (fun _ => Q) (fun Λ h1 h2 => ⟨(), by simp, h Λ h1 h2⟩)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumData_mass_le (P : S.Datum → Submodule L.O S.V → Prop) :
    (S.sumData fun d => S.mass d (P d)) ≤ S.nn := by
  unfold Frames.nn Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (mass_mono S _ _ _ fun _ _ _ => trivial) _

theorem ampSq_le_of_mass (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop) (B : ℝ)
    (hB : ∀ d, S.mass d (P d) ≤ ENNReal.ofReal B) :
    S.ampSq P ≤ ENNReal.ofReal B * S.sumData fun d => S.mass d (P d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk
  simpa using h2 P B 1 zero_le_one hB (fun d => by simpa using h1 d (P d))

theorem ampSq_le_of_zero (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop)
    (hP : ∀ d Λ, S.IsTerm d Λ → P d Λ → S.BBzero d Λ) :
    S.ampSq P ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  refine (ampSq_le_of_mass S hk P _ fun d => ?_).trans
    (mul_le_mul_right (sumData_mass_le S P) _)
  by_cases hT : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hT
    have hH : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀).2.2.2.2.1
    have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    refine (mass_mono S d _ (fun Λ => S.cardI d Λ = 1) fun Λ h1 h2 => ?_).trans
      (((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk d).1 1).trans (ENNReal.ofReal_le_ofReal ?_))
    · have hb := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h1).2.2.2.2.2.2.1.1 (hP d Λ h1 h2)
      obtain ⟨⟨i, hi⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      have : 0 < S.q ^ i := by positivity
      omega
    · rw [Nat.cast_one, one_pow, mul_one]
      exact pow_le_pow_right₀ hH (by nlinarith)
  · refine (mass_le_sum S (∅ : Finset Unit) d _ (fun _ _ => True) fun Λ h1 _ =>
      (hT ⟨Λ, h1⟩).elim).trans ?_
    simp

theorem ampSq_defect_le (hk : 4 * r + 7 ≤ k) (hH : 0 ≤ S.Hp) (i : ℕ) :
    (S.ampSq fun d Λ => S.be d Λ = S.q ^ i) ≤
      ENNReal.ofReal ((i + 1) * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (4 * S.Hp ^ (4 * (r + 1)))) * S.nn := by
  have hk1 : 1 ≤ k := by omega
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hβ : 0 < S.q ^ i := by positivity
  have hβ' : (0 : ℝ) < ((S.q ^ i : ℕ) : ℝ) ^ (k - 1) := by positivity
  have hm : ∀ d, S.mass d (fun Λ => S.be d Λ = S.q ^ i) ≤ ENNReal.ofReal ((i + 1) *
      (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1))) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun j Λ => S.cardI d Λ = S.q ^ j)
      fun Λ h1 h2 => ?_).trans ?_
    · obtain ⟨⟨j, hj⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      refine ⟨j, Finset.mem_range.2 ?_, hj⟩
      rw [hj, h2] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      omega
    · refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal
        (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1)))
        fun j hj => ?_).trans ?_
      · refine ((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hji : S.q ^ j ≤ S.q ^ i :=
          Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.1 hj; omega)
        gcongr
      · rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ i + 1),
          ← ENNReal.ofReal_natCast, Nat.cast_succ]
  refine (ampSq_le_of_mass S hk1 _ _ hm).trans ?_
  refine (mul_le_mul_right (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk _ hβ) _).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem ampSq_le_height_mul_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.ampSq S.BBzero ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn ∧ (S.ampSq fun _ _ => True) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  have hk1 : 1 ≤ k := by omega
  refine ⟨ampSq_le_of_zero S hk1 _ fun _ _ _ h => h, ?_⟩
  by_cases hz : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ
  · exact ampSq_le_of_zero S hk1 _ fun d Λ h _ => hz d Λ h
  push_neg at hz
  obtain ⟨d₀, Λ₀, h₀, hn⟩ := hz
  obtain ⟨ha, -, -, hqa, hH, -, -, hqH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq' : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have h2 : (2 : ℝ) ≤ S.Hp := hq'.trans (hqH hn)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le ha
  have hAH : (A : ℝ) + 1 ≤ S.Hp := by
    rw [hA, zpow_natCast] at hqa
    have h1 : A + 1 ≤ S.q ^ A := Nat.lt_pow_self (by omega)
    exact le_trans (by exact_mod_cast h1) hqa
  refine (GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (Finset.range (A + 1))
    (fun i d Λ => S.be d Λ = S.q ^ i) _ (fun d Λ h => ?_) (fun d Λ h i _ i' _ h1 h2 => ?_)).trans ?_
  · obtain ⟨i, hi, hb⟩ := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.1
    exact ⟨fun _ => ⟨i, Finset.mem_range.2 (by omega), hb⟩, fun _ => trivial⟩
  · exact Nat.pow_right_injective hq (h1.symm.trans h2)
  have hsum := Finset.sum_le_card_nsmul (Finset.range (A + 1))
    (fun i => S.ampSq fun d Λ => S.be d Λ = S.q ^ i)
    (ENNReal.ofReal (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) * S.nn) (fun i hi => by
      refine (ampSq_defect_le S hk (by linarith) i).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
      have hi' : (i : ℝ) ≤ A := by
        have := Finset.mem_range.1 hi
        exact_mod_cast (by omega : i ≤ A)
      have h4 : (4 : ℝ) ≤ S.Hp ^ 2 := by nlinarith
      have h5 : (i : ℝ) + 1 ≤ S.Hp := by linarith
      gcongr)
  refine (mul_le_mul_right hsum _).trans ?_
  have hc : ((A + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal S.Hp := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact hAH)
  rw [Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  refine (mul_le_mul_left (mul_le_mul' hc hc) _).trans ?_
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : S.Hp * S.Hp * (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
      (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) = S.Hp ^ (9 * (r + 1) ^ 2 + 16 * (r + 1) + 5) := by
    ring
  rw [he]
  exact pow_le_pow_right₀ hH (by nlinarith)

end GlobalTheory.HL.NoCancellation
end

section
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSq

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.CoordSq.sums_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d0 : _root_.Formalism.MainNotions.S.LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H))
        = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t)
        = ENNReal.ofReal κ * S.ampSq S.BBzero ∧
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧
      _root_.Formalism.MainNotions.S.LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.HL.CoordSum.tsum_reps_eq M hM H r k P S c R d0
  have hamp := _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq M hM H r k P S c R
  have hvanA : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.amp δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.amp
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hvanM : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop),
      (¬ ∃ Λ, S.IsTerm δ Λ) → S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold _root_.GlobalTheory.HL.Frames.mass
    refine (tsum_congr fun o => ?_).trans tsum_zero
    rw [if_neg fun h => hδ ⟨_, h.1⟩]
  have hinv : ∀ h ∈ S.H0, ∀ (δ : S.Datum) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      S.amp (h • δ) (Q (h • δ)) = S.amp δ (Q δ) ∧
        S.mass (h • δ) (Q (h • δ)) = S.mass δ (Q δ) :=
    fun h hh δ Q h1 h2 => _root_.GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Q δ)
      (Q (h • δ)) (fun s hs Λ hΛ => h1 δ s hs Λ hΛ) (fun Λ hΛ => h2 δ Λ hΛ)
  have hBBst : ∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' (s • Λ) ↔ S.BBzero δ' Λ) :=
    fun δ' s hs Λ hΛ =>
      (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ' Λ hΛ s hs).2.2.2.2.2.2.2.1
  have hBBh : ∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ →
      (S.BBzero δ' Λ ↔ S.BBzero (h • δ') (h • Λ)) := by
    intro h hh δ' Λ hΛ
    obtain ⟨-, -, -, hM', hsat, -⟩ :=
      _root_.GlobalTheory.HL.ComplAct.main M.L r k S δ' Λ hΛ h hh
    unfold _root_.GlobalTheory.HL.Frames.BBzero
    rw [hM', hsat]
  have hsq : ∀ z : ℂ, ((‖z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  have hA : ∀ (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : S.Datum → Submodule M.L.O S.V → Prop),
      (∀ d, _root_.Formalism.MainNotions.S.LocNG.amp R d p
        = S.amp (c.dat d) (Q (c.dat d))) →
      (∀ δ', ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ' Λ → Q δ' Λ → Q δ' (s • Λ)) →
      (∀ h ∈ S.H0, ∀ δ' Λ, S.IsTerm δ' Λ → (Q δ' Λ ↔ Q (h • δ') (h • Λ))) →
      _root_.Formalism.MainNotions.S.LocNG.sumSq R d0 p = ENNReal.ofReal κ * S.ampSq Q := by
    intro p Q hpQ h1 h2
    unfold _root_.Formalism.MainNotions.S.LocNG.sumSq _root_.GlobalTheory.HL.Frames.ampSq
    rw [← hsum (fun δ => ENNReal.ofReal (‖S.amp δ (Q δ)‖ ^ 2))
      (fun h hh δ => by rw [(hinv h hh δ Q h1 (h2 h hh)).1])
      (fun δ hδ => by rw [hvanA δ _ hδ, norm_zero]; simp)]
    refine tsum_congr fun d => ?_
    rw [hpQ, hsq]
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_⟩
  · exact hA _ (fun δ Λ => ¬ S.BBzero δ Λ) (fun d => (hamp d).1)
      (fun δ' s hs Λ hΛ hq => by rwa [hBBst δ' s hs Λ hΛ])
      (fun h hh δ' Λ hΛ => not_congr (hBBh h hh δ' Λ hΛ))
  · exact hA _ S.BBzero (fun d => (hamp d).2.1)
      (fun δ' s hs Λ hΛ hq => (hBBst δ' s hs Λ hΛ).2 hq)
      (fun h hh δ' Λ hΛ => hBBh h hh δ' Λ hΛ)
  · exact hA _ (fun _ _ => True) (fun d => (hamp d).2.2.1)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => Iff.rfl)
  · unfold _root_.Formalism.MainNotions.S.LocNG.nn _root_.GlobalTheory.HL.Frames.nn
    rw [← hsum (fun δ => S.mass δ (fun _ => True))
      (fun h hh δ => (hinv h hh δ (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
        (fun _ _ _ => Iff.rfl)).2)
      (fun δ hδ => hvanM δ _ hδ)]
    refine tsum_congr fun d => ?_
    rw [(hamp d).2.2.2]

end GlobalTheory.HL.CoordSq
end

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ LocNG.sumSq R d0 (LocNG.BBne (H := H)) = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧ LocNG.sumSq R d0 (fun t => ¬ LocNG.BBne (H := H) t) = ENNReal.ofReal κ * S.ampSq S.BBzero ∧ LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧ LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  atlas_forward_decl GlobalTheory.HL.CoordSq.sums_eq
end

section
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AbstractBound

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem nn_eq_zero (h : ∀ d Λ, ¬ S.IsTerm d Λ) : S.nn = 0 := by
  simp [Frames.nn, Frames.sumData, Frames.mass, h]

theorem ampSq_BBzero_eq (h : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) :
    S.ampSq S.BBzero = S.ampSq fun _ _ => True := by
  have : ∀ d, S.amp d (S.BBzero d) = S.amp d (fun _ => True) := by
    intro d
    unfold Frames.amp
    refine tsum_congr fun o => ?_
    by_cases H : S.IsTerm d o.out
    · simp [H, h _ _ H]
    · simp [H]
  simp only [Frames.ampSq, this]

theorem raise [IsNonarchimedeanLocalField F] [CharZero F] {C : ℝ} (hC : 39 ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * t) * S.nn ≤
      ENNReal.ofReal (S.Hp ^ (C * ((r : ℝ) + 1) ^ 2) * t) * S.nn := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ
  · obtain ⟨d, Λ, hd⟩ := h
    have h1 : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hd).2.2.2.2.1
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ ht)) _
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le h1 ?_
    push_cast
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  · push_neg at h
    simp [nn_eq_zero S h]

end

theorem ngAt : ∀ (C : ℝ), 39 ≤ C → ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → LocNG.NGAt k P C := by
  intro C hC F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hV hP R d0
  letI := hM.loc
  letI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hV hP
  obtain ⟨κ, -, e1, e2, e3, e4⟩ := GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums M hM H r k P S c R d0
  obtain ⟨hH, hq, hpr⟩ := GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard M hM H r k P S c
  have n1 := GlobalTheory.HL.NonzeroDefect.ampSq_nonzero_defect M.L r k S hk
  obtain ⟨n2, n3⟩ := GlobalTheory.HL.NoCancellation.ampSq_le_height_mul_mass M.L r k S hk
  have r1 := raise S hC (t := 1) zero_le_one
  simp only [mul_one] at r1
  rw [e1, e2, e3, e4, hH, hq]
  refine ⟨?_, ?_, ?_, fun hp => ?_⟩
  · rw [mul_left_comm]
    refine mul_le_mul_right (n1.trans ?_) _
    have : (S.q : ℝ) ^ (-((k : ℝ) - 2 * r - 5)) = (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) := by
      rw [← Real.rpow_intCast]; push_cast; rfl
    rw [this]
    exact raise S hC (by positivity)
  · rw [mul_left_comm]
    exact mul_le_mul_right (n2.trans r1) _
  · rw [mul_left_comm]
    exact mul_le_mul_right (n3.trans r1) _
  · obtain ⟨g1, g2, g3⟩ := hpr hp
    obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.HL.GoodPlace.equality M.L r k S hk g1 g2 g3
    rw [ampSq_BBzero_eq S a1, a3]
    exact ⟨a2, rfl, rfl⟩

end GlobalTheory.HL.AbstractBound
end

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local : ∀ (C : ℝ), 39 ≤ C → ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → LocNG.NGAt k P C := by
  atlas_forward_decl GlobalTheory.HL.AbstractBound.ngAt
end

section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem local_nongeneric_bound_record_family :
    ∀ (C : ℝ), 39 ≤ C → (∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C) ∧
      (∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C ∧ Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBoundOfLargeRank D C ∧ Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C) ∧
      ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C ∧ Formalism.MainNotions.UniformConstantsAndStatements.admF5 Fm C := by
  intro C hC
  have h1 : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
    intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP
    exact GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local C hC M hM H r k P hk hV hP
  have h2 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C := fun D hk => h1 _ _ hk
  have h3 : ∀ D : D7, Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C := fun D => h2 D
  exact ⟨h1, fun D => ⟨h2 D, h2 D, h3 D⟩, fun Fm => ⟨fun x i => h2 _, fun x i => h3 _⟩⟩

end GlobalTheory
end
