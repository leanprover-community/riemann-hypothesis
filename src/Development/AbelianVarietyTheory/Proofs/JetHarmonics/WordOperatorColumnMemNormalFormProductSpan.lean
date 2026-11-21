import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.WordL

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem mem_of_bmon (d : Q.NFData P A) {b : A} (hb : b ∈ bmon d) : b ∈ nfSpan d ∅ 0 0 0 :=
  Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩

theorem span_eq (d : Q.NFData P A) : nfSpan d ∅ 0 0 0 = Submodule.span ℂ (bmon d : Set A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨b, hb, H, hH, -, rfl⟩
    rw [List.length_eq_zero_iff.mp hH]
    simpa using Submodule.subset_span (R := ℂ) (s := (bmon d : Set A)) hb
  · exact Submodule.span_le.mpr fun b hb => mem_of_bmon d hb

theorem span_mul (d : Q.NFData P A) {x y : A} (hx : x ∈ nfSpan d ∅ 0 0 0) (hy : y ∈ nfSpan d ∅ 0 0 0) :
    x * y ∈ nfSpan d ∅ 0 0 0 := by
  rw [span_eq] at *
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (bmon d).mul_mem ha hb

theorem kappa_mem (d : Q.NFData P A) (f : M.Ty P → ℂ) : d.κ f ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))))

theorem zbi_mem (d : Q.NFData P A) : d.L.ζbi ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp)))))

variable {S : Type} [Fintype S] [DecidableEq S]

def BMat (d : Q.NFData P A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0

theorem BMat.mul {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E * F) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => span_mul d (hE i k) (hF k j)

theorem BMat.add {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E + F) :=
  fun i j => add_mem (hE i j) (hF i j)

theorem BMat.sub {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E - F) :=
  fun i j => sub_mem (hE i j) (hF i j)

theorem BMat.smul {d : Q.NFData P A} {E : SlopeTestRemainingChoices S A} (c : ℂ) (hE : BMat d E) : BMat d (c • E) :=
  fun i j => Submodule.smul_mem _ c (hE i j)

theorem bMat_io {d : Q.NFData P A} {a : A} (ha : a ∈ nfSpan d ∅ 0 0 0) : BMat d (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := map_add (Matrix.scalar (Ix S)) a b

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := map_mul (Matrix.scalar (Ix S)) a b

theorem inv_subset {r : ℕ} (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    ∀ Y ∈ (ofWord L st w).inv, Y ∈ st.inv := by
  induction w with
  | nil => exact fun Y hY => hY
  | cons l w ih =>
    intro Y hY
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1

theorem comm_id {R : Type*} [Ring R] (l K E α β γ : R) (h1 : β * l = l * β) (h2 : β * K = K * β)
    (h3 : α * K = K * α) :
    α * ((l + K * E) * β - β * (l + K * E)) * γ = K * (α * (E * β - β * E) * γ) := by
  have : (l + K * E) * β - β * (l + K * E) = K * (E * β - β * E) := by
    rw [mul_add, h1, ← mul_assoc β K, h2]; noncomm_ring
  rw [this, ← mul_assoc α K, h3]; simp only [mul_assoc]

end

theorem word_l_shape : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  intro P A _ _ _ _ d hd L st s hT S _ _ w hA Y hY hY1
  obtain ⟨hk, h0⟩ := GlobalTheory.T.frameStart_constants_normalForm_empty_word P A d hd L st s hT
  obtain ⟨E0, hE0, e0⟩ := h0 Y (inv_subset L st w Y hY)
  obtain ⟨hH, hS, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, s1, s2, s3, -, s4, s5⟩ := hS
  have hkap : (kapL L : SlopeTestRemainingChoices S A) = kapL d.L := by simp only [kapL, s1, s2, s4]
  have htz : (tz L : SlopeTestRemainingChoices S A) = tz d.L := by simp only [tz, s3, s5]
  have hl0 : (st.frame : FrameData S A).l L Y = io (d.L.l0 Y) + kapL d.L * io E0 := by
    show io (L.l0 Y) + io (L.ζb * L.ζi * L.GGi) * io (st.ee Y) =
      io (d.L.l0 Y) + io (d.L.ζb * d.L.ζi * d.L.GGi) * io E0
    rw [← io_mul, ← io_add, e0, io_add, io_mul]
  have hsh := (Formalism.FourierDecayAlt.P.l_shape A S P.r L st w hH.starLev hH.start hA).2.2 Y hY hY1
  rw [hl0, hkap, htz] at hsh
  have hc := hd.2.2.1.2.1
  have cζb : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hc f _ (by simp [LevelData.fns])
  have cζi : ∀ f, Commute (d.κ f) d.L.ζi := fun f => hc f _ (by simp [LevelData.fns])
  have cG : ∀ f, Commute (d.κ f) d.L.GGi := fun f => hc f _ (by simp [LevelData.fns])
  have cn : ∀ f, Commute (d.κ f) d.L.nab := fun f => hc f _ (by simp)
  have cio : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io a = io a * α := by
    intro a ha α hα
    refine (Formalism.FourierDecayAlt.P.TLA.L1.io_comm fun i j => ?_).symm.eq
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact (ha f).symm
  have cK : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * kapL d.L = kapL d.L * α :=
    cio _ fun f => ((cζb f).mul_right (cζi f)).mul_right (cG f)
  have cl : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io (d.L.l0 Y) = io (d.L.l0 Y) * α :=
    cio _ fun f => (cn f).neg_right.sub_right
      ((show Commute (d.κ f) (algebraMap ℂ A (Y + 1 / 2)) from (Algebra.commutes _ _).symm).mul_right
        ((cζb f).mul_right (cG f)))
  have hB : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → BMat d α := by
    intro α hα i j
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact kappa_mem d f
  have hE : BMat d (io E0 : SlopeTestRemainingChoices S A) := bMat_io hE0
  have key : ∀ M ∈ TL.dSpan st (io (d.L.l0 Y) + kapL d.L * io E0 : SlopeTestRemainingChoices S A) (kapL d.L) (tz d.L),
      ∃ E : SlopeTestRemainingChoices S A, BMat d E ∧ M = kapL d.L * E := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
      · exact ⟨_, ((hB α h1).mul ((hE.mul (hB β h2)).sub ((hB β h2).mul hE))).mul (hB γ h3),
          comm_id _ _ _ _ _ _ (cl β h2) (cK β h2) (cK α h1)⟩
      · exact ⟨γ, hB γ h, rfl⟩
      · exact ⟨tz d.L * γ, (bMat_io (Submodule.smul_mem _ _ (zbi_mem d))).mul (hB γ h), mul_assoc _ _ _⟩
    | zero => exact ⟨0, fun _ _ => zero_mem _, (mul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨E, hE, rfl⟩ := hx
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨E + F, hE.add hF, (mul_add _ _ _).symm⟩
    | smul c x _ hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact ⟨c • E, hE.smul c, (mul_smul_comm _ _ _).symm⟩
  obtain ⟨E, hE', e⟩ := key _ hsh
  refine ⟨io E0 + E, hE.add hE', ?_⟩
  rw [sub_eq_iff_eq_add.mp e, mul_add]
  abel

end GlobalTheory.HatNF.WordL
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_l_decomposition_nf_span : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  atlas_forward_decl GlobalTheory.HatNF.WordL.word_l_shape
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MShapeNF

open Formalism.FourierDecayAlt.P.TLA.M2

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def bAlg (d : Q.NFData P A) : Subalgebra ℂ A :=
  (Submodule.span ℂ (bmon d : Set A)).toSubalgebra (Submodule.subset_span (bmon d).one_mem) (by
    intro x y hx hy
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (bmon d).mul_mem ha hb)

variable {S : Type} [Fintype S] [DecidableEq S]

def EM (B : Subalgebra ℂ A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ B

theorem EM.add {B : Subalgebra ℂ A} {E F : SlopeTestRemainingChoices S A} (hE : EM B E) (hF : EM B F) : EM B (E + F) := fun i j =>
  B.add_mem (hE i j) (hF i j)

theorem EM.smul {B : Subalgebra ℂ A} {E : SlopeTestRemainingChoices S A} (z : ℂ) (hE : EM B E) : EM B (z • E) := fun i j =>
  B.smul_mem (hE i j) z

theorem EM.io {B : Subalgebra ℂ A} {a : A} (ha : a ∈ B) : EM B (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact B.zero_mem

variable [StarModule ℂ A]

open MeasureTheory in
private lemma mem_inv_of_mem_ofWord_inv {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [Fintype S] [DecidableEq S] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) :
    ∀ (w : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S)) (Z : ℂ), Z ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv → Z ∈ st.inv := by
  intro w
  induction w with
  | nil => intro Z hZ; exact hZ
  | cons l w ih =>
    intro Z hZ
    simp only [_root_.Formalism.FourierDecayAlt.Fr.ofWord] at hZ
    by_cases hl : l.plus = true
    · rw [if_pos hl] at hZ
      unfold _root_.Formalism.FourierDecayAlt.Fr.FrameData.plus at hZ
      exact ih Z (Set.mem_of_mem_inter_left hZ)
    · rw [if_neg hl] at hZ
      unfold _root_.Formalism.FourierDecayAlt.Fr.FrameData.minus at hZ
      exact ih Z (Set.mem_of_mem_inter_left hZ)

open MeasureTheory in
private lemma star_l0_sub_one_add_eq_m0_add {P : _root_.Formalism.FourierDecayAlt.M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (E : A) (Y : ℂ) (hYr : star Y = Y)
    (hstarD : _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel d.L) (hsnab : star d.L.nab = d.L.nabs)
    (hcE : Commute (star E) (d.L.ζ * d.L.ζbi * d.L.GGi)) :
    star (d.L.l0 (Y - 1) + d.L.ζb * d.L.ζi * d.L.GGi * E) =
      d.L.m0 Y + d.L.ζ * d.L.ζbi * d.L.GGi * star E := by
  obtain ⟨-, hsζb, hsζi, -, -, hsGGi⟩ := _root_.Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hstarD
  have hm0 : d.L.m0 Y = -d.L.nabs - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζ * d.L.GGi) := rfl
  have hl0 : d.L.l0 (Y - 1) = -d.L.nab - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζb * d.L.GGi) := by
    show -d.L.nab - algebraMap ℂ A (Y - 1 + 1 / 2) * (d.L.ζb * d.L.GGi) = _
    rw [show Y - 1 + 1 / 2 = Y - 1 / 2 by ring]
  have hsc : star (algebraMap ℂ A (Y - 1 / 2)) = algebraMap ℂ A (Y - 1 / 2) := by
    rw [← algebraMap_star_comm, star_sub, hYr]
    norm_num
  have hperm : d.L.GGi * d.L.ζbi * d.L.ζ = d.L.ζ * d.L.ζbi * d.L.GGi := by
    rw [_root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L), mul_assoc, _root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L),
      ← mul_assoc, _root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L)]
  rw [hl0, hm0]
  simp only [star_add, star_sub, star_neg, star_mul, hsnab, hsζb, hsζi, hsGGi, hsc]
  congr 1
  · congr 1
    rw [_root_.Formalism.FourierDecayAlt.P.RuleGD.fc d.L (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L) (_root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L)]
    exact (Algebra.commutes _ _).symm
  · rw [← mul_assoc d.L.GGi, hperm]
    exact hcE.eq

open MeasureTheory in
variable {P : _root_.Formalism.FourierDecayAlt.M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] in
variable {S : Type} [Fintype S] [DecidableEq S] in
variable [StarModule ℂ A] in

theorem _root_.GlobalTheory.HatNF.MShapeNF.mshape : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d →
    ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S), _root_.Formalism.FourierDecayAlt.Fr.admitted st w →
    ∀ Y ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv, star Y = Y → Y - 1 ∈ (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).inv →
    ∃ E : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0) ∧
      (_root_.Formalism.FourierDecayAlt.Fr.ofWord L st w).m L Y = _root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  intro P A _ _ _ _ d hd L st s ht S _ _ w hw Y hY hYr hY1
  obtain ⟨hκ, hE⟩ := _root_.GlobalTheory.HatNF.start_normalForm P A d hd L st s ht
  have hA : _root_.Formalism.FourierDecayAlt.TL.AHyp L st := ht.1
  have hst : _root_.Formalism.FourierDecayAlt.Fr.IsLevelStart L st := hA.start
  have hsame : _root_.GlobalTheory.HatNF.SameFns L d.L := ht.2.1
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, hTT⟩ := hsame
  have hstarD : _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel d.L := hd.2.1
  have hsnab : star d.L.nab = d.L.nabs := by
    unfold _root_.Formalism.FourierDecayAlt.Fr.IsStarLevel at hstarD
    exact hstarD.2.1
  have hrel : d.Rel := hd.2.2.1
  unfold _root_.Formalism.FourierDecayAlt.Q.NFData.Rel at hrel
  obtain ⟨-, hbm, -⟩ := _root_.GlobalTheory.HatNF.Den.hat_den P A d hd
  set B := _root_.GlobalTheory.HatNF.MShapeNF.bAlg d with hBdef
  have hBmem : ∀ x, x ∈ B ↔ x ∈ Submodule.span ℂ (_root_.GlobalTheory.HatNF.bmon d : Set A) := fun x => Iff.rfl
  have hB : ∀ x, x ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 ↔ x ∈ B := by
    intro x
    have hset : {x | ∃ b ∈ _root_.GlobalTheory.HatNF.bmon d, ∃ H : List A, H.length = 0 ∧ (∀ h ∈ H, h ∈ (∅ : Set A)) ∧
        x = b * d.L.Di ^ 0 * _root_.Formalism.FourierDecayAlt.TL.gI d.L ^ 0 * H.prod} = (_root_.GlobalTheory.HatNF.bmon d : Set A) := by
      ext x
      constructor
      · rintro ⟨b, hb, H, hH, -, rfl⟩
        rw [List.length_eq_zero_iff] at hH
        subst hH
        simpa using hb
      · intro hx
        exact ⟨x, hx, [], rfl, by simp, by simp⟩
    unfold _root_.GlobalTheory.HatNF.nfSpan
    rw [hset, hBmem]
  have hgen : ∀ x ∈ _root_.GlobalTheory.HatNF.bset d, x ∈ B := by
    intro x hx
    apply Submodule.subset_span
    unfold _root_.GlobalTheory.HatNF.bmon
    exact Submonoid.subset_closure hx
  have hκB : ∀ f, d.κ f ∈ B := by
    intro f
    apply hgen
    unfold _root_.GlobalTheory.HatNF.bset
    exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))
  have hζiB : d.L.ζi ∈ B := by
    apply hgen
    unfold _root_.GlobalTheory.HatNF.bset
    exact Or.inl (Or.inl (Or.inl (Or.inl (by simp))))
  have hstarB : ∀ x ∈ B, star x ∈ B := by
    intro x hx
    rw [hBmem] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ((hbm y hy).2.2.2)
    | zero => simp
    | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hcommB : ∀ x ∈ B, ∀ f ∈ d.L.fns, Commute x f := by
    intro x hx f hf
    rw [hBmem] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (hbm y hy).1 f hf
    | zero => exact Commute.zero_left f
    | add y z _ _ hy hz => exact hy.add_left hz
    | smul r y _ hy => exact hy.smul_left r
  have hEMmul : ∀ X Z : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) → (∀ i j, Z i j ∈ B) → ∀ i j, (X * Z) i j ∈ B := by
    intro X Z hX hZ i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hX i k) (hZ k j)
  have hEMsub : ∀ X Z : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) → (∀ i j, Z i j ∈ B) → ∀ i j, (X - Z) i j ∈ B := by
    intro X Z hX hZ i j
    rw [Matrix.sub_apply]
    exact Subalgebra.sub_mem _ (hX i j) (hZ i j)
  have hEMio : ∀ a ∈ B, ∀ i j, (_root_.Formalism.FourierDecayAlt.Wd.io a : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) i j ∈ B := by
    intro a ha i j
    by_cases h : i = j
    · subst h
      simpa [_root_.Formalism.FourierDecayAlt.Wd.io] using ha
    · simp [_root_.Formalism.FourierDecayAlt.Wd.io, Matrix.diagonal_apply_ne _ h]
  have hkκ : ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ → ∀ i j, ∃ f, d.κ f = γ i j := by
    intro γ hγ i j
    unfold _root_.Formalism.FourierDecayAlt.TL.kMat at hγ
    exact hκ _ (hγ i j)
  have hkB : ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ → ∀ i j, γ i j ∈ B := by
    intro γ hγ i j
    obtain ⟨f, hf⟩ := hkκ γ hγ i j
    rw [← hf]
    exact hκB f
  have hζf := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζ d.L
  have hζbif := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_ζbi d.L
  have hGGif := _root_.Formalism.FourierDecayAlt.P.RuleGD.m_GGi d.L
  have hfns : ∀ x ∈ d.L.fns, ∀ f, Commute (d.κ f) x := fun x hx f => hrel.2.1 f x (Or.inl hx)
  set c := d.L.ζ * d.L.ζbi * d.L.GGi with hc
  have hcκ : ∀ f, Commute (d.κ f) c := fun f =>
    ((hfns _ hζf f).mul_right (hfns _ hζbif f)).mul_right (hfns _ hGGif f)
  have hm0 : d.L.m0 Y = -d.L.nabs - algebraMap ℂ A (Y - 1 / 2) * (d.L.ζ * d.L.GGi) := rfl
  have hmκ : ∀ f, Commute (d.κ f) (d.L.m0 Y) := by
    intro f
    rw [hm0]
    exact (hrel.2.1 f _ (Or.inr (by simp))).neg_right.sub_right
      ((Algebra.commute_algebraMap_right _ _).mul_right ((hfns _ hζf f).mul_right (hfns _ hGGif f)))
  have hinv := mem_inv_of_mem_ofWord_inv (S := S) L st
  obtain ⟨E, hEmem, hEeq⟩ := hE (Y - 1) (hinv w _ hY1)
  have hEB : E ∈ B := (hB E).1 hEmem
  have hsEB : star E ∈ B := hstarB E hEB
  have hcE : Commute (star E) c := ((hcommB _ hsEB _ hζf).mul_right (hcommB _ hsEB _ hζbif)).mul_right
    (hcommB _ hsEB _ hGGif)
  have hs := star_l0_sub_one_add_eq_m0_add d E Y hYr hstarD hsnab hcE
  have hM0 : _root_.Formalism.FourierDecayAlt.Fr.FrameData.m L (st.frame : _root_.Formalism.FourierDecayAlt.Fr.FrameData S A) Y =
      _root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E) := by
    rw [_root_.Formalism.FourierDecayAlt.P.TLA.M2.frame_m L st Y, _root_.Formalism.FourierDecayAlt.P.TLA.M2.frame_l L st (Y - 1), _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_star, hEeq, hs, _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_add, _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_mul]
  have hJ := _root_.Formalism.FourierDecayAlt.P.m_shape_of_l_shape A S P.r L st w hA.starLev hst hw Y hY hYr hY1
  rw [hζ, hζbi, hGGi, hTT, hζi] at hJ
  let W : Submodule ℂ (_root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) :=
    { carrier := {Z | ∃ X : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, (∀ i j, X i j ∈ B) ∧ Z = _root_.Formalism.FourierDecayAlt.Wd.io c * X}
      add_mem' := by
        rintro _ _ ⟨X, hX, rfl⟩ ⟨Z, hZ, rfl⟩
        exact ⟨X + Z, fun i j => Subalgebra.add_mem _ (hX i j) (hZ i j), (Matrix.mul_add _ _ _).symm⟩
      zero_mem' := ⟨0, fun i j => Subalgebra.zero_mem _, (Matrix.mul_zero _).symm⟩
      smul_mem' := by
        rintro r _ ⟨X, hX, rfl⟩
        exact ⟨r • X, fun i j => Subalgebra.smul_mem _ (hX i j) r, (Matrix.mul_smul _ r X).symm⟩ }
  have hcomm : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ γ : _root_.Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A, _root_.Formalism.FourierDecayAlt.TL.kMat st γ →
      Commute (_root_.Formalism.FourierDecayAlt.Wd.io a) γ := by
    intro a ha γ hγ
    apply _root_.Formalism.FourierDecayAlt.P.TLA.M2.io_comm
    intro i j
    obtain ⟨f, hf⟩ := hkκ γ hγ i j
    rw [← hf]
    exact (ha f).symm
  have hW : _root_.Formalism.FourierDecayAlt.TL.dSpan st (_root_.Formalism.FourierDecayAlt.Fr.FrameData.m L (st.frame : _root_.Formalism.FourierDecayAlt.Fr.FrameData S A) Y) (_root_.Formalism.FourierDecayAlt.Wd.io c)
      (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.TT • d.L.ζi)) ≤ W := by
    unfold _root_.Formalism.FourierDecayAlt.TL.dSpan
    rw [Submodule.span_le]
    rintro Z (⟨α, β, γ, hα, hβ, hγ, rfl⟩ | ⟨γ, hγ, rfl | rfl⟩)
    · have hcβ := hcomm c hcκ β hβ
      have hcα := hcomm c hcκ α hα
      have hmβ := hcomm _ hmκ β hβ
      refine ⟨α * (_root_.Formalism.FourierDecayAlt.Wd.io (star E) * β - β * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) * γ,
        hEMmul _ _ (hEMmul _ _ (hkB α hα) (hEMsub _ _ (hEMmul _ _ (hEMio _ hsEB) (hkB β hβ))
          (hEMmul _ _ (hkB β hβ) (hEMio _ hsEB)))) (hkB γ hγ), ?_⟩
      have h1 : (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) * β -
          β * (_root_.Formalism.FourierDecayAlt.Wd.io (d.L.m0 Y) + _root_.Formalism.FourierDecayAlt.Wd.io c * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) =
          _root_.Formalism.FourierDecayAlt.Wd.io c * (_root_.Formalism.FourierDecayAlt.Wd.io (star E) * β - β * _root_.Formalism.FourierDecayAlt.Wd.io (star E)) := by
        rw [add_mul, mul_add, hmβ.eq, ← mul_assoc β, ← hcβ.eq]
        simp only [mul_sub, mul_assoc]
        abel
      rw [hM0, h1, ← mul_assoc α, ← hcα.eq]
      simp only [mul_assoc]
    · exact ⟨γ, hkB γ hγ, rfl⟩
    · exact ⟨_root_.Formalism.FourierDecayAlt.Wd.io (d.L.TT • d.L.ζi) * γ,
        hEMmul _ _ (hEMio _ (Subalgebra.smul_mem _ hζiB _)) (hkB γ hγ), mul_assoc _ _ _⟩
  obtain ⟨X, hX, hXeq⟩ := hW hJ
  refine ⟨_root_.Formalism.FourierDecayAlt.Wd.io (star E) + X,
    fun i j => (hB _).2 (Subalgebra.add_mem _ (hEMio _ hsEB i j) (hX i j)), ?_⟩
  rw [mul_add, ← add_assoc, ← hM0, ← hXeq]
  abel

end GlobalTheory.HatNF.MShapeNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_m_decomposition_self_adjoint : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, star Y = Y → Y - 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).m L Y = io (d.L.m0 Y) + io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  atlas_forward_decl GlobalTheory.HatNF.MShapeNF.mshape
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.LetterEntries

open Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.TLA

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [StarModule ℂ A] in

theorem gen_mem (d : Q.NFData P A) {T : Set A} {b X : A} (hb : b ∈ bmon d) (hX : X ∈ T) :
    b * d.L.Di * X ∈ nfSpan d T 1 0 1 :=
  Submodule.subset_span ⟨b, hb, [X], rfl, by simpa using hX, by simp⟩

omit [StarModule ℂ A] in

theorem bounded_induction (d : Q.NFData P A) (N : Submodule ℂ A) (hN : ∀ b ∈ bmon d, b ∈ N) {E : A}
    (hE : E ∈ nfSpan d ∅ 0 0 0) : E ∈ N := by
  refine (Submodule.span_le.mpr ?_ : nfSpan d ∅ 0 0 0 ≤ N) hE
  rintro x ⟨b, hb, H, hH, -, rfl⟩
  rw [List.length_eq_zero_iff] at hH
  subst hH
  simpa using hN b hb

omit [StarModule ℂ A] in
theorem bounded_mul_mem (d : Q.NFData P A) {T : Set A} {E b X : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hb : b ∈ bmon d)
    (hX : X ∈ T) : E * (b * d.L.Di * X) ∈ nfSpan d T 1 0 1 := by
  refine bounded_induction d ((nfSpan d T 1 0 1).comap (LinearMap.mulRight ℂ (b * d.L.Di * X))) ?_ hE
  intro c hc
  have := gen_mem d (mul_mem hc hb) hX
  simpa [mul_assoc] using this

omit [StarModule ℂ A] in
theorem bounded_comm (d : Q.NFData P A) {E f : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hf : ∀ b ∈ bmon d, Commute b f) :
    f * E = E * f := by
  have := bounded_induction d (LinearMap.ker (LinearMap.mulLeft ℂ f - LinearMap.mulRight ℂ f))
    (fun b hb => by simp [(hf b hb).eq]) hE
  simpa [sub_eq_zero] using this

variable {S : Type} [Fintype S] [DecidableEq S]

omit [StarModule ℂ A] [StarRing A] in
theorem io_mem {N : Submodule ℂ A} {a : A} (ha : a ∈ N) (e e' : Ix S) : (io a : SlopeTestRemainingChoices S A) e e' ∈ N := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact N.zero_mem

omit [StarModule ℂ A] [StarRing A] in
theorem col_mem {N : Submodule ℂ A} {s X k V W : A} {E : SlopeTestRemainingChoices S A} (h1 : s * (X * V + W) ∈ N)
    (h2 : ∀ e e', s * k * E e e' * V ∈ N) (e e' : Ix S) :
    (io s * ((io X + io k * E) * io V + io W) : SlopeTestRemainingChoices S A) e e' ∈ N := by
  have key : io s * ((io X + io k * E) * io V + io W) =
      (io (s * (X * V + W)) : SlopeTestRemainingChoices S A) + io (s * k) * E * io V := by
    simp only [io, map_mul, map_add]; noncomm_ring
  rw [key, Matrix.add_apply]
  refine N.add_mem (io_mem h1 e e') ?_
  have : (io (s * k) * E * io V : SlopeTestRemainingChoices S A) e e' = s * k * E e e' * V := by
    simp [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [this]
  exact h2 e e'

theorem letterCol_mem : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) →
    ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  intro P A _ _ _ _ d hd0 L st s hT S _ _ l w hA i e e'
  obtain ⟨hnd, hre, hpt, hpw⟩ := hA
  have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
  have hpw' := List.pairwise_cons.mp hpw
  have hAw : admitted st w :=
    ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
  obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
  have hd := hpw'.1
  have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
    ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
  have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
    ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
  have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
    ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
  have hr : star l.pt = l.pt := hre l (by simp)
  obtain ⟨-, hb, -⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd0
  obtain ⟨ep, epb, ec, eci, ecb, ecbi, eζ, eζi, eζb, eζbi, eG, eGi, -⟩ := hT.2.1
  have eT : L.Tprod l.pt = d.L.Tprod l.pt := by
    unfold LevelData.Tprod LevelData.Tl; rw [ep, ec, eci]
  have eTv : L.Tvprod l.pt = d.L.Tvprod l.pt := by
    unfold LevelData.Tvprod LevelData.Tvl; rw [epb, ecb, ecbi]
  have eA : L.Ar l.pt = d.L.Ar l.pt := by unfold LevelData.Ar; rw [eT]
  have eB : L.Br l.pt = d.L.Br l.pt := by unfold LevelData.Br; rw [eT]
  have eAv : L.Avr l.pt = d.L.Avr l.pt := by unfold LevelData.Avr; rw [eTv]
  have eBv : L.Bvr l.pt = d.L.Bvr l.pt := by unfold LevelData.Bvr; rw [eTv]
  have hβ : d.L.D * d.L.Dbi ∈ bmon d := Submonoid.subset_closure (by simp [bset])
  have i1 : 1 * d.L.Di * d.L.Dr = d.L.ζi := by
    rw [one_mul, LevelData.Di, mul_assoc, Dri_Dr, mul_one]
  have i2 : d.L.D * d.L.Dbi * d.L.Di * d.L.Drb = d.L.ζbi := by
    have : d.L.Di * d.L.D = 1 := by
      rw [LevelData.D, ← mul_assoc, ← one_mul d.L.Di, i1, d.L.ζi_ζ]
    rw [(hb _ hβ).2.1.eq, ← mul_assoc, this, one_mul, LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]
  have j1 : d.L.ζi * d.L.Ar l.pt = 1 * d.L.Di * d.L.Ahat l.pt := by
    rw [LevelData.Ahat, ← mul_assoc, i1]
  have j2 : d.L.ζbi * d.L.Avr l.pt = d.L.D * d.L.Dbi * d.L.Di * d.L.Ahatv l.pt := by
    rw [LevelData.Ahatv, ← mul_assoc, i2]
  have hA1 : d.L.Ahat l.pt ∈ hats d.L := by simp [hats]
  have hA2 : d.L.Ahatv l.pt ∈ hats d.L := by simp [hats]
  have hR1 : d.L.R0 l.pt ∈ hats d.L := by simp [hats]
  have hR2 : d.L.R0v l.pt ∈ hats d.L := by simp [hats]
  unfold TL.letterCol
  by_cases hp : l.plus
  · simp only [hp, if_true]
    fin_cases i
    · refine io_mem (a := TL.aP L l.pt) ?_ e e'
      rw [TL.aP, eζi, eA, j1]
      exact gen_mem d (one_mem _) hA1
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_l_decomposition_nf_span P A d hd0 L st s hT S w hAw l.pt m0 m1
      rw [hl, eζbi, eG, eA, eB, kapL]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d hβ hR1
        rwa [LevelData.R0, ← mul_assoc, ← mul_assoc, i2] at this
      · rw [ColumnLift.s1p, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j1]
        exact bounded_mul_mem d (hE f f') (one_mem _) hA1
  · simp only [hp, Bool.false_eq_true, if_false]
    fin_cases i
    · refine io_mem (a := TL.aM L l.pt) ?_ e e'
      rw [TL.aM, eζbi, eAv, j2]
      exact gen_mem d hβ hA2
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_m_decomposition_self_adjoint P A d hd0 L st s hT S w hAw l.pt m0 hr mm1
      rw [hl, eζi, eG, eAv, eBv]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d (one_mem _) hR2
        rwa [LevelData.R0v, ← mul_assoc, ← mul_assoc, i1] at this
      · rw [ColumnLift.s1m, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j2]
        exact bounded_mul_mem d (hE f f') hβ hA2

end GlobalTheory.HatNF.LetterEntries
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letterCol_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) → ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  atlas_forward_decl GlobalTheory.HatNF.LetterEntries.letterCol_mem
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [StarModule ℂ A] in

theorem word_one_mem_nfSpan (d : Q.NFData P A) (T : Set A) : (1 : A) ∈ nfSpan d T 0 0 0 :=
  Submodule.subset_span ⟨1, one_mem _, [], rfl, by simp, by simp⟩

omit [StarModule ℂ A] in

theorem word_letter_mem_nfSpan (d : Q.NFData P A) (T : Set A) {X : A} (hX : X ∈ T) : X ∈ nfSpan d T 0 0 1 :=
  Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩

theorem word_mul_mem_nfSpan (d : Q.NFData P A) (hd : HatHyp d) {n : ℕ} {x y : A}
    (hx : x ∈ nfSpan d (hats d.L) 1 0 1) (hy : y ∈ nfSpan d (hats d.L) n 0 n) :
    x * y ∈ nfSpan d (hats d.L) (n + 1) 0 (n + 1) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd (hats d.L)
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, H, hH, hT, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hH
    have ht : t ∈ hats d.L := hT t (by simp)
    have a1 := h2 0 (fun X hX => word_letter_mem_nfSpan d _ hX) n 0 n t ht y hy
    have a2 := (h1 _ _ _ _ a1).2.1
    have a3 := (h1 _ _ _ _ a2).1 b hb
    simpa [mul_assoc] using a3
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ ih ih' => rw [add_mul]; exact add_mem ih ih'
  | smul c x _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

end

theorem word_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  intro P A _ _ _ _ d hd L st s ht S _ _ w
  induction w with
  | nil =>
    intro _ e
    have : ((ofWord L st ([] : List (Letter ℂ S))).F * TL.bTA L []) = 1 := by
      simp [ofWord, Start.frame, TL.bTA, bT]
    rw [this, Matrix.one_apply]
    split_ifs
    · exact word_one_mem_nfSpan d _
    · exact zero_mem _
  | cons l w ih =>
    intro hA e
    have hAw : admitted st w := ⟨(List.nodup_cons.mp (by simpa only [List.map_cons] using hA.1)).2,
      fun l' h => hA.2.1 l' (by simp [h]), fun l' h => hA.2.2.1 l' (by simp [h]), (List.pairwise_cons.mp hA.2.2.2).2⟩
    rw [Formalism.FourierDecayAlt.P.word_recursion A S P.r L st l w ht.1 hA e, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun e' _ => ?_
    have h1 : ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * TL.letterCol L st l w i : SlopeTestRemainingChoices S A) e e') ∈
        nfSpan d (hats d.L) 1 0 1 := by
      rw [Matrix.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun e'' _ => ?_
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]; exact GlobalTheory.T.letterCol_mem_normalFormProductSpan P A d hd L st s ht S l w hA i e'' e'
      · rw [zero_mul]; exact zero_mem _
    exact word_mul_mem_nfSpan d hd h1 (ih hAw e')

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  atlas_forward_decl GlobalTheory.HatNF.word_mem_nfSpan
end
