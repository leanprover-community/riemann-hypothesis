import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Loc

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

private lemma mulVec_mem_spanLt' {n r : ℕ} {e : Fin r → Fin n → ℂ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ b : Fin r, (A - 1) *ᵥ e b ∈ spanLt e b.1) (a : ℕ) :
    ∀ y ∈ spanLt e a, A *ᵥ y ∈ spanLt e a := by
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.toLin' A) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.toLin'_apply]
    have hsplit : A *ᵥ e b = e b + (A - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit]
    refine add_mem (Submodule.subset_span ⟨b, hb, rfl⟩) ?_
    refine Submodule.span_mono (Set.image_mono ?_) (hA b)
    intro c hc
    exact lt_trans (show c.1 < b.1 from hc) (show b.1 < a from hb)
  intro y hy
  exact hle hy

private lemma inN_mul' {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : InN ε e z A) (hB : InN ε e z B) : InN ε e z (A * B) := by
  have key : ∀ x : Fin n → ℂ, (A * B - 1) *ᵥ x = A *ᵥ ((B - 1) *ᵥ x) + (A - 1) *ᵥ x := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ (hB.1.1 a)) (hA.1.1 a)
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ hB.1.2) hA.1.2
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ (hB.2 y hy)) (hA.2 y hy)

theorem ninf_mul {a b : X.B.I.Ginf} (ha : a ∈ X.NinfU u) (hb : b ∈ X.NinfU u) : a * b ∈ X.NinfU u := by
  intro v
  exact inN_mul' (ha v) (hb v)

private lemma mulVec_mem_spanLt_of_left_inv {n r : ℕ} {e : Fin r → Fin n → ℂ} {A Ai : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ b : Fin r, (A - 1) *ᵥ e b ∈ spanLt e b.1) (h2 : Ai * A = 1) (a : ℕ) :
    ∀ y ∈ spanLt e a, Ai *ᵥ y ∈ spanLt e a := by
  intro y hy
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.toLin' A).restrict (fun x hx => mulVec_mem_spanLt' hA a x hx)
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h := congrArg (fun w : spanLt e a => Ai *ᵥ (w : Fin n → ℂ)) hxx
    have hc : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = A *ᵥ (w : Fin n → ℂ) := fun w => rfl
    simp only [hc, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h
    exact Subtype.ext h
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨y, hy⟩
  have hwv : A *ᵥ (w : Fin n → ℂ) = y := congrArg Subtype.val hw
  have hw' : (w : Fin n → ℂ) = Ai *ᵥ y := by
    rw [← hwv, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← hw']
  exact w.2

private lemma inN_of_left_inv {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {A Ai : Matrix (Fin n) (Fin n) ℂ} (h2 : Ai * A = 1) (hA : InN ε e z A) : InN ε e z Ai := by
  have key : ∀ x : Fin n → ℂ, (Ai - 1) *ᵥ x = -(Ai *ᵥ ((A - 1) *ᵥ x)) := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h2]
    abel
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ (hA.1.1 a))
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ hA.1.2)
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ (hA.2 y hy))

private lemma uMat_expU_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  simp [uMat]

theorem ninf_inv {a : X.B.I.Ginf} (ha : a ∈ X.NinfU u) : a⁻¹ ∈ X.NinfU u := by
  intro v
  exact inN_of_left_inv (uMat_expU_inv_mul (a v)) (ha v)

theorem sinf_conj {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    a * n * a⁻¹ ∈ X.NinfU u := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Formalism.L2.SG.Pf.Sinf.levi X u ha
  have hmn : m * n * m⁻¹ ∈ X.NinfU u := ninf_mul X u (ninf_mul X u hm hn) (ninf_inv X u hm)
  have hc := Formalism.L2.SG.Pf.Sinf.conj_ninf X u hh hmn
  have e : h * m * n * (h * m)⁻¹ = h * (m * n * m⁻¹) * h⁻¹ := by group
  rw [e]
  exact hc

theorem sinf_nh {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F) :
    a v ∈ Formalism.L2.SG.Pf.WuDec.NHloc X u v := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Formalism.L2.SG.Pf.Sinf.levi X u ha
  have hc := Formalism.L2.SG.Pf.Sinf.conj_ninf X u hh hm
  refine ⟨h v * m v * (h v)⁻¹, hc v, h v, fun y hy => hh v y hy, ?_⟩
  show h v * m v = h v * m v * (h v)⁻¹ * h v
  group

end Loc

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem haar_conj (S T : Set G) (g : G) (hST : ∀ z, g * z * g⁻¹ ∈ T ↔ z ∈ S) {μ : Measure G}
    (h : SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ) :
    SigmaFinite (μ.map fun y => g * y * g⁻¹) ∧ (μ.map fun y => g * y * g⁻¹) ≠ 0 ∧
      (μ.map fun y => g * y * g⁻¹) Tᶜ = 0 ∧
      ∀ r ∈ T, (μ.map fun y => g * y * g⁻¹).map (fun x => r * x) = μ.map fun y => g * y * g⁻¹ := by
  obtain ⟨hσ, h0, hS, hinv⟩ := h
  have hm : ∀ x : G, Measurable (fun y : G => x * y * x⁻¹) := fun x =>
    (measurable_const_mul x).mul_const x⁻¹
  let E : G ≃ᵐ G :=
    { toFun := fun y => g * y * g⁻¹
      invFun := fun y => g⁻¹ * y * g
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      measurable_toFun := hm g
      measurable_invFun := (measurable_const_mul g⁻¹).mul_const g }
  have hE : (fun y : G => g * y * g⁻¹) = ⇑E := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]
    refine SigmaFinite.of_map (μ.map E) E.symm.measurable.aemeasurable ?_
    have hback : (μ.map E).map E.symm = μ := by
      rw [Measure.map_map E.symm.measurable E.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
    rw [hback]
    exact hσ
  · exact (Measure.map_ne_zero_iff (hm g).aemeasurable).mpr h0
  · rw [hE, MeasurableEquiv.map_apply]
    have hpre : ⇑E ⁻¹' Tᶜ = Sᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      exact not_congr (hST z)
    rw [hpre]
    exact hS
  · intro r hr
    have hs : g⁻¹ * r * g ∈ S := by
      rw [← hST]
      rw [show g * (g⁻¹ * r * g) * g⁻¹ = r by group]
      exact hr
    rw [Measure.map_map (measurable_const_mul r) (hm g)]
    have hcomp : (fun x : G => r * x) ∘ (fun y : G => g * y * g⁻¹) =
        (fun y : G => g * y * g⁻¹) ∘ (fun x : G => (g⁻¹ * r * g) * x) := by
      funext y
      simp only [Function.comp]
      group
    rw [hcomp, ← Measure.map_map (hm g) (measurable_const_mul _), hinv _ hs]

theorem haar_smul {S : Set G} {μ : Measure G}
    (h : SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ) {d : ℝ≥0∞} (h0 : d ≠ 0)
    (ht : d ≠ ⊤) :
    SigmaFinite (d • μ) ∧ d • μ ≠ 0 ∧ (d • μ) Sᶜ = 0 ∧ ∀ s ∈ S, (d • μ).map (fun x => s * x) = d • μ := by
  obtain ⟨hσ, h0', hS, hinv⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Formalism.L2.SG.NGPin.sf_smul μ ht
  · intro hz
    have h1 : (d • μ) Set.univ = 0 := by rw [hz]; simp
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact (mul_ne_zero h0 (Measure.measure_univ_ne_zero.mpr h0')) h1
  · rw [Measure.smul_apply, hS, smul_zero]
  · intro s hs
    rw [Measure.map_smul, hinv s hs]

end Gen

theorem eq_one_of_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (h0 : μ ≠ 0)
    {c : ℝ≥0∞} (h : μ = c • μ) : c = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, μ (spanningSets μ k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h0
    have hu : μ (⋃ k, spanningSets μ k) = 0 := measure_iUnion_null hcon
    rw [iUnion_spanningSets] at hu
    exact Measure.measure_univ_eq_zero.mp hu
  have htop : μ (spanningSets μ k) ≠ ⊤ := (measure_spanningSets_lt_top μ k).ne
  have hx : μ (spanningSets μ k) = c * μ (spanningSets μ k) := by
    have e1 := congrArg (fun m : Measure α => m (spanningSets μ k)) h
    simp only [Measure.smul_apply, smul_eq_mul] at e1
    exact e1
  have h3 : c * μ (spanningSets μ k) / μ (spanningSets μ k) =
      μ (spanningSets μ k) / μ (spanningSets μ k) := by rw [← hx]
  rwa [ENNReal.mul_div_cancel_right hk htop, ENNReal.div_self hk htop] at h3

private lemma inN_one' {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    InN ε e z 1 :=
  ⟨⟨fun a => by simp, by simp⟩, fun y _ => by simp⟩

section Loc

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem conj_loc_of {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F) {n : Formalism.REAL.UJ (X.B.I.ε v)}
    (hn : n ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u))) :
    a v * n * (a v)⁻¹ ∈
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) := by
  classical
  let n' : X.B.I.Ginf := Function.update 1 v n
  have hn' : n' ∈ X.NinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      have e : n' w = n := by simp [n']
      show InN _ _ _ (uMat (n' w))
      rw [e]
      exact hn
    · have e : n' w = 1 := by simp [n', Function.update_of_ne hw]
      show InN _ _ _ (uMat (n' w))
      rw [e]
      exact inN_one' _ _ _
  have h := sinf_conj X u ha hn' v
  have e : n' v = n := by simp [n']
  show InN _ _ _ (uMat (a v * n * (a v)⁻¹))
  rw [← e]
  exact h

end Loc

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Glob

variable {D : D7} (X : HidaSetting D)

def kst : ℝ≥0∞ := ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi)

theorem kst_pos : 0 < D.host.ka / (X.B.g : ℝ) / Real.pi := by
  have hg : (0 : ℝ) < (X.B.g : ℝ) := by
    rw [X.g_eq]
    exact_mod_cast Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    apply div_pos _ two_pos
    apply Real.rpow_pos_of_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka
    exact div_pos Real.pi_pos hv
  exact div_pos (div_pos hka hg) Real.pi_pos

theorem kst_ne_zero : kst X ≠ 0 := by
  unfold kst
  exact (ENNReal.ofReal_pos.mpr (kst_pos X)).ne'

theorem kst_ne_top : kst X ≠ ⊤ := by
  unfold kst
  exact ENNReal.ofReal_ne_top

private lemma smul_measure_ne_zero {α : Type*} [MeasurableSpace α] {c : ℝ≥0∞} {μ : Measure α} (hc : c ≠ 0)
    (hμ : μ ≠ 0) : c • μ ≠ 0 := by
  intro hz
  have h1 : (c • μ) Set.univ = 0 := by rw [hz]; simp
  rw [Measure.smul_apply, smul_eq_mul] at h1
  exact (mul_ne_zero hc (Measure.measure_univ_ne_zero.mpr hμ)) h1

theorem pin_pi (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hrep : IsPtRep X u u' w γ)
    (μ : Measure X.B.I.Ginf) (hH : IsHaarOnSet X.B.I (StInf X u u' γ) μ)
    (hm : μ.map (stCoord X u' w γ) = muStab X w) :
    ∃ m : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ v) (m v)) ∧
      (∀ v, (m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) =
        Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ))) ∧ μ = Measure.pi m := by
  classical
  have hsfk : SigmaFinite (kst X • (volume : Measure ℂ)) := Formalism.L2.SG.NGPin.sf_smul _ (kst_ne_top X)
  have hP := fun v => Formalism.L2.SG.NGPin.placeHaar_holds D X u u' w γ hrep v
  choose μv cv hμv hc0 hctop hmap using hP
  set K : ℝ≥0∞ := kst X ^ Fintype.card (FreeE w) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (kst_ne_zero X)
  have hKt : K ≠ ⊤ := ENNReal.pow_ne_top (kst_ne_top X)
  have hpiK : Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ)) =
      K • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) := by
    rw [Formalism.L2.SG.NGPin.pi_smul (fun _ : FreeE w => (volume : Measure ℂ)) (fun _ => kst X),
      Finset.prod_const, Finset.card_univ]
  have hd0 : ∀ v, K / cv v ≠ 0 := fun v => ENNReal.div_ne_zero.mpr ⟨hK0, hctop v⟩
  have hdt : ∀ v, K / cv v ≠ ⊤ := fun v => ENNReal.div_ne_top hKt (hc0 v)
  have hpv0 : Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun m : Measure (FreeE w → ℂ) => m Set.univ) h0
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp)) h1
  let m : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (K / cv v) • μv v
  have hmH : ∀ v, IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ v) (m v) := fun v =>
    haar_smul (hμv v) (hd0 v) (hdt v)
  have hmmap : ∀ v, (m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) =
      Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ)) := by
    intro v
    simp only [m]
    rw [Measure.map_smul, hmap v, smul_smul, ENNReal.div_mul_cancel (hc0 v) (hctop v), hpiK]
  have hae : ∀ v, AEMeasurable (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) (m v) := by
    intro v
    by_contra hn
    have h0 := Measure.map_of_not_aemeasurable hn
    rw [hmmap v, hpiK] at h0
    exact smul_measure_ne_zero hK0 hpv0 h0
  haveI : ∀ v, SigmaFinite (m v) := fun v => (hmH v).1
  haveI : ∀ v, SigmaFinite ((m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v)) := fun v => by
    rw [hmmap v]; infer_instance
  have hpimap : (Measure.pi m).map (stCoord X u' w γ) = muStab X w := by
    rw [Formalism.L2.SG.NGPin.stCoord_eq X u' w γ, Measure.pi_map_pi hae]
    simp only [hmmap]
    rfl
  refine ⟨m, hmH, hmmap, ?_⟩
  have hSt := Formalism.L2.SG.NGPin.stInf_eq_pi X u u' γ
  have hpiH : IsHaarOnSet X.B.I (StInf X u u' γ) (Measure.pi m) := by
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · intro h0
      have h1 := congrArg (fun μ' : Measure X.B.I.Ginf => μ' Set.univ) h0
      simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
      exact (Finset.prod_ne_zero_iff.mpr (fun v _ => Measure.measure_univ_ne_zero.mpr (hmH v).2.1)) h1
    · rw [hSt]
      have hsub : (Set.univ.pi (Formalism.L2.SG.NGPin.StV X u u' γ))ᶜ ⊆
          ⋃ v, Function.eval v ⁻¹' (Formalism.L2.SG.NGPin.StV X u u' γ v)ᶜ := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_univ_pi, not_forall] at hx
        obtain ⟨v, hv⟩ := hx
        exact Set.mem_iUnion.mpr ⟨v, hv⟩
      refine measure_mono_null hsub (measure_iUnion_null fun v => ?_)
      exact Measure.pi_eval_preimage_null _ (hmH v).2.2.1
    · intro s hs
      rw [hSt] at hs
      have hinv : ∀ v, (m v).map (fun y => s v * y) = m v := fun v => (hmH v).2.2.2 (s v) (hs v (Set.mem_univ v))
      haveI : ∀ v, SigmaFinite ((m v).map (fun y => s v * y)) := fun v => by rw [hinv v]; infer_instance
      have e : (fun x : X.B.I.Ginf => s * x) = fun x v => (fun y => s v * y) (x v) := rfl
      rw [e, Measure.pi_map_pi (fun v => (measurable_const_mul (s v)).aemeasurable)]
      simp only [hinv]
  have hclosed : IsClosed (StInf X u u' γ) := by
    rw [← Formalism.L2.SG.NGPin.coe_StG X u u' γ]
    exact Formalism.L2.SG.NGPin.isClosed_StG X u u' γ
  have hgrp : QPK.IsGrp (StInf X u u' γ) := by
    rw [← Formalism.L2.SG.NGPin.coe_StG X u u' γ]
    exact ⟨(Formalism.L2.SG.NGPin.StG X u u' γ).one_mem, fun a ha b hb => (Formalism.L2.SG.NGPin.StG X u u' γ).mul_mem ha hb,
      fun a ha => (Formalism.L2.SG.NGPin.StG X u u' γ).inv_mem ha⟩
  obtain ⟨c, hc0', hct', hμc⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (StInf X u u' γ) hclosed hgrp μ (Measure.pi m) hH hpiH
  have hS : muStab X w = c • muStab X w := by
    have e := congrArg (fun μ' : Measure X.B.I.Ginf => μ'.map (stCoord X u' w γ)) hμc
    simp only [Measure.map_smul] at e
    rw [hm, hpimap] at e
    exact e
  obtain ⟨K', hK'0, hK't, hK'⟩ := Formalism.L2.SG.NGPin.muStab_eq X w
  haveI : SigmaFinite (muStab X w) := by
    rw [hK']; exact Formalism.L2.SG.NGPin.sf_smul _ hK't
  have hne : muStab X w ≠ 0 := by
    rw [hK']
    refine smul_measure_ne_zero hK'0 ?_
    intro h1
    have h2 := congrArg (fun μ' : Measure (InfinitePlace X.B.I.F → FreeE w → ℂ) => μ' Set.univ) h1
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h2
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp))) h2
  have hc1 := eq_one_of_smul (muStab X w) hne hS
  rw [hμc, hc1, one_smul]

private lemma one_mem_Nset (k r : ℕ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨?_, fun a i _ => Matrix.one_apply, fun i j _ _ _ => Matrix.one_apply⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

end Glob

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Base

variable {D : D7} (X : HidaSetting D)

theorem root_base {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (τ : D.what₂.Tau) (hrep : IsPtRep X u u' w γ) (m : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hH : IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) m)
    (hm : m.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
      Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ))) :
    IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w)
      (trG (C.Q τ) (C.Qi τ) (γ (vOf X τ))) (m.map (Formalism.L2.SG.RealConjugatorData.cMr C γ τ)) := by
  have hst := Formalism.L2.SG.RootPatterns.stCoordV_comp (C := C) (u' := u') (w := w) (γ := γ) (τ := τ)
  have hZ := Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point (C := C) (u := u) (u' := u') (w := w) (γ := γ) (hrep := hrep) (τ := τ)
  have hmeasR : Measurable (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w)) :=
    GlobalTheory.Amp.RootMove.measurable_rootCoords _ _
  have hcm := (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γ τ)
  unfold IsRootMeasR
  refine ⟨1, (one_mem_Nset _ _), 1, (one_mem_Nset _ _), trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)), by simp, hZ,
    m.map (Formalism.L2.SG.RealConjugatorData.cMr C γ τ), ?_, ?_, ?_⟩
  · rw [hcm.map_apply]
    refine measure_mono_null ?_ hH.2.2.1
    intro y hy hyS
    exact hy ((Formalism.L2.SG.RealConjugatorData.stV_iff (C := C) (γ := γ) (τ := τ) (u := u) (u' := u') y).1 hyS)
  · rw [Measure.map_map hmeasR hcm.measurable]
    set E := MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)
      with hEdef
    have hg : Measurable (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) := hmeasR.comp hcm.measurable
    have e2 : m.map (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) =
        (m.map (E ∘ (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
          Formalism.L2.SG.RealConjugatorData.cMr C γ τ))).map E.symm := by
      rw [Measure.map_map E.symm.measurable (E.measurable.comp hg)]
      congr 1
    rw [e2]
    have e3 : E ∘ (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) = Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) := by
      rw [hst]
    rw [e3, hm]
    haveI : SigmaFinite (kst X • (volume : Measure ℂ)) := Formalism.L2.SG.NGPin.sf_smul _ (kst_ne_top X)
    have hmp0 := MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Formalism.L2.SG.RealObj.FreeE w => kst X • (volume : Measure ℂ)) (Formalism.L2.SG.RootPatterns.idxF τ w)
    have hmp := MeasureTheory.MeasurePreserving.symm _ hmp0
    rw [hmp.map_eq]
    rw [Formalism.L2.SG.NGPin.pi_smul (fun _ : ↥(Formalism.MainNotions.S.rootPat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) => (volume : Measure ℂ))
      (fun _ => kst X)]
    rw [← MeasureTheory.volume_pi]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    unfold kst
    rw [← ENNReal.ofReal_pow (kst_pos X).le]
    congr 2
    have hg : (X.B.g : ℝ) = gg D := by
      rw [X.g_eq]
      simp [gg]
    rw [hg]
    field_simp
  · simp [Measure.map_id']

end Base

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Main

variable {D : D7} (X : HidaSetting D)

theorem conj_loc (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F)
    (n : Formalism.REAL.UJ (X.B.I.ε v)) :
    a v * n * (a v)⁻¹ ∈
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) ↔
    n ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) := by
  constructor
  · intro h
    have h2 := conj_loc_of X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u ha) v h
    have e : a⁻¹ v * (a v * n * (a v)⁻¹) * (a⁻¹ v)⁻¹ = n := by
      rw [Pi.inv_apply]; group
    rwa [e] at h2
  · exact conj_loc_of X u ha v

theorem sinf_conj_iff (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (n : X.B.I.Ginf) :
    a * n * a⁻¹ ∈ X.NinfU u ↔ n ∈ X.NinfU u := by
  constructor
  · intro h
    have h2 := sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u ha) h
    have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
    rwa [e] at h2
  · exact sinf_conj X u ha

private lemma uMat_mul_flag_measures {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    uMat (g * h) = uMat g * uMat h := rfl

variable {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)

theorem trG_mul (x y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (x * y) = trG (C.Q τ) (C.Qi τ) x * trG (C.Q τ) (C.Qi τ) y := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  simp only [trG, uMat_mul_flag_measures, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

theorem trG_inv (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) x⁻¹ = (trG (C.Q τ) (C.Qi τ) x)⁻¹ := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
  symm
  apply Matrix.inv_eq_left_inv
  simp only [trG, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, ← Matrix.mul_assoc (uMat x⁻¹) (uMat x),
    uMat_expU_inv_mul, Matrix.one_mul, hQi]

theorem cMr_trG (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y) =
      trG (C.Q τ) (C.Qi τ) ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    trG (C.Q τ) (C.Qi τ) ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ))
  rw [trG, uMat_mul_flag_measures, uMat_mul_flag_measures, Formalism.L2.SG.RealConjugatorData.uMat_inv']
  simp only [Matrix.mul_assoc]

private lemma trG_mem_UH {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have hH : (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := (C.isT τ).2.2.1
  have hU : (uMat γ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := γ.2
  show (trG (C.Q τ) (C.Qi τ) γ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * trG (C.Q τ) (C.Qi τ) γ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [← hH]
  unfold trG
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul,
    ← Matrix.mul_assoc (C.Qi τ)ᴴ (C.Q τ)ᴴ, ← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one, Matrix.one_mul,
    ← Matrix.mul_assoc (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (uMat γ)]
  rw [← Matrix.mul_assoc (uMat γ)ᴴ (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ) (C.Q τ),
    ← Matrix.mul_assoc (uMat γ)ᴴ (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (uMat γ), hU]

end Main

theorem pinned_root : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (μR : Measure X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR s w μR → ∃ μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), μR = Measure.pi μl ∧ (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset s) μR ∧ ∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ)))))) := by
  intro D X Y θ C u u' s w μR h
  obtain ⟨γw, s0, s1, μw, hrep, hs0, hs1, hpt, hH, hm, hμR⟩ := h
  obtain ⟨m, hmH, hmmap, hμw⟩ := pin_pi X u u' w γw hrep μw hH hm
  haveI : ∀ v, SigmaFinite (m v) := fun v => (hmH v).1
  have hcjm : ∀ v, Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε v) => s0 v * y * (s0 v)⁻¹) := fun v =>
    (measurable_const_mul (s0 v)).mul_const _
  have hST : ∀ v, ∀ z, s0 v * z * (s0 v)⁻¹ ∈
      StSet (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v) ↔
      z ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro v z
    have e : (s.pt.1 v)⁻¹ * (s0 v * z * (s0 v)⁻¹) * s.pt.1 v = s1 v * ((γw v)⁻¹ * z * γw v) * (s1 v)⁻¹ := by
      rw [hpt]
      simp only [Pi.mul_apply, Pi.inv_apply]
      group
    show (s0 v * z * (s0 v)⁻¹ ∈ InfCut.JacobianCoordinates.NLoc _ _ _ ∧
      (s.pt.1 v)⁻¹ * (s0 v * z * (s0 v)⁻¹) * s.pt.1 v ∈ InfCut.JacobianCoordinates.NLoc _ _ _) ↔ _
    rw [e]
    exact and_congr (conj_loc X u hs0 v z) (conj_loc X u' hs1 v _)
  let μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (m v).map (fun y => s0 v * y * (s0 v)⁻¹)
  have hμlH : ∀ v, IsHaarLoc
      (StSet (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v))
      (μl v) := fun v => haar_conj _ _ (s0 v) (hST v) (hmH v)
  refine ⟨μl, ?_, hμlH, ?_, ?_⟩
  · rw [hμR, hμw]
    haveI : ∀ v, SigmaFinite ((m v).map (fun y => s0 v * y * (s0 v)⁻¹)) := fun v => (hμlH v).1
    have e : (fun y : X.B.I.Ginf => s0 * y * s0⁻¹) = fun y v => (fun z => s0 v * z * (s0 v)⁻¹) (y v) := rfl
    rw [e, Measure.pi_map_pi (fun v => (hcjm v).aemeasurable)]
  · rw [hμR]
    refine haar_conj (StInf X u u' γw) (Formalism.L2.SG.TermOp.Vanish.Rset s) s0 ?_ hH
    intro z
    have e : (s.pt.1)⁻¹ * (s0 * z * s0⁻¹) * s.pt.1 = s1 * (γw⁻¹ * z * γw) * s1⁻¹ := by
      rw [hpt]
      group
    show (s0 * z * s0⁻¹ ∈ X.NinfU u ∧ (s.pt.1)⁻¹ * (s0 * z * s0⁻¹) * s.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e]
    exact and_congr (sinf_conj_iff X u hs0 z) (sinf_conj_iff X u' hs1 _)
  · intro τ
    refine ⟨Formalism.MainNotions.S.ThB.ptLoc D τ w, ?_⟩
    have hb := root_base X C u u' w γw τ hrep (m (vOf X τ)) (hmH _) (hmmap _)
    have hz := Formalism.L2.SG.Pf.zTr C u τ
    have hz' := Formalism.L2.SG.Pf.zTr C u' τ
    have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
      rw [hz.2]
      exact Formalism.MainNotions.BridgeLemma.Tr_pos D u
    have hT' : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
      rw [hz'.2]
      exact Formalism.MainNotions.BridgeLemma.Tr_pos D u'
    have ha : trG (C.Q τ) (C.Qi τ) (s0 (vOf X τ)) ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) :=
      (Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u τ (s0 (vOf X τ))).2 (sinf_nh X u hs0 (vOf X τ))
    have ha' : trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)) ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u' τ) :=
      (Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u' τ (s1 (vOf X τ))).2 (sinf_nh X u' hs1 (vOf X τ))
    have hmove := GlobalTheory.Amp.RootMove.rootMeas_move D _ _ _ _ _ _ _ hz.1 hz'.1 hT hT'
      (trG_mem_UH C τ (γw (vOf X τ))) ha ha' hb
    have hg : trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ)) =
        trG (C.Q τ) (C.Qi τ) (s0 (vOf X τ)) * trG (C.Q τ) (C.Qi τ) (γw (vOf X τ)) *
          (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹ := by
      rw [hpt]
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [trG_mul X C τ, trG_mul X C τ, trG_inv X C τ]
    have hGm : Measurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) := by
      apply Continuous.measurable
      fun_prop
    have hcm := (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γw τ).measurable
    have hFeq : (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) =
        (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) ∘
          Formalism.L2.SG.RealConjugatorData.cMr C γw τ ∘ (fun y => (s0 (vOf X τ))⁻¹ * y * s0 (vOf X τ)) := by
      funext y
      simp only [Function.comp_apply]
      have e1 : (s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ) = s1 (vOf X τ) * ((γw (vOf X τ))⁻¹ *
          ((s0 (vOf X τ))⁻¹ * y * s0 (vOf X τ)) * γw (vOf X τ)) * (s1 (vOf X τ))⁻¹ := by
        rw [hpt]
        simp only [Pi.mul_apply, Pi.inv_apply]
        group
      rw [e1, trG_mul X C τ, trG_mul X C τ, trG_inv X C τ, ← cMr_trG X C τ γw _]
      rfl
    have hF : Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) := by
      rw [hFeq]
      exact hGm.comp (hcm.comp ((measurable_const_mul _).mul_const _))
    have hμ : (μl (vOf X τ)).map (fun y =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) =
        ((m (vOf X τ)).map (Formalism.L2.SG.RealConjugatorData.cMr C γw τ)).map
          (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) := by
      have hcomp : (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
          Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) ∘
            (fun y => s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹) =
          (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) ∘
            Formalism.L2.SG.RealConjugatorData.cMr C γw τ := by
        rw [hFeq]
        funext y
        simp only [Function.comp_apply]
        rw [show (s0 (vOf X τ))⁻¹ * (s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹) * s0 (vOf X τ) = y by group]
      show ((m (vOf X τ)).map (fun y => s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹)).map _ = _
      rw [Measure.map_map hF (hcjm _), Measure.map_map hGm hcm, hcomp]
    rw [hg, hμ]
    exact hmove

end GlobalTheory.Amp.PinRoot
end
end
end
end
end
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (μR : Measure X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR s w μR → ∃ μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), μR = Measure.pi μl ∧ (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset s) μR ∧ ∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ)))))) := by
  atlas_forward_decl GlobalTheory.Amp.PinRoot.pinned_root
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotExist

theorem bruhat_left (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (hν : ν ≠ 0) (j : H →* G)
    (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ h, b ((j h)⁻¹ * g) ∂ν = 1 := by
  classical
  let K : ℕ → Set G := compactCovering G
  have hK : ∀ n, IsCompact (K n) := isCompact_compactCovering G
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hK n).isClosed.measurableSet
  let φ : ℕ → G → ℝ≥0∞ := fun n => (K n).indicator 1
  have hφ : ∀ n, Measurable (φ n) := fun n => measurable_one.indicator (hKm n)
  have hjm : Measurable j := hj.continuous.measurable
  let F : ℕ → G → ℝ≥0∞ := fun n g => ∫⁻ h, φ n ((j h)⁻¹ * g) ∂ν
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    have : Measurable (fun p : G × H => φ n ((j p.2)⁻¹ * p.1)) :=
      (hφ n).comp ((hjm.comp measurable_snd).inv.mul measurable_fst)
    exact this.lintegral_prod_right'
  have key : ∀ n k g, F n ((j k)⁻¹ * g) = F n g := by
    intro n k g
    have := lintegral_mul_left_eq_self (μ := ν) (fun h => φ n ((j h)⁻¹ * g)) k
    simpa only [F, map_mul, _root_.mul_inv_rev, mul_assoc] using this
  have hpre : ∀ n g, MeasurableSet ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := fun n g =>
    (hjm.inv.mul_const g) (hKm n)
  have hFeq : ∀ n g, F n g = ν ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := by
    intro n g
    rw [← lintegral_indicator_one (hpre n g)]
    rfl
  have hFfin : ∀ n g, F n g ≠ ⊤ := by
    intro n g
    rw [hFeq]
    have hc : Topology.IsClosedEmbedding (fun h => (j h)⁻¹ * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp ((Homeomorph.inv G).isClosedEmbedding.comp hj)
    exact (hc.isCompact_preimage (hK n)).measure_lt_top.ne
  have hFpos : ∀ g, ∃ n, F n g ≠ 0 := by
    intro g
    by_contra hcon
    push Not at hcon
    have h0 : ν (⋃ n, (fun h => (j h)⁻¹ * g) ⁻¹' K n) = 0 :=
      measure_iUnion_null fun n => by rw [← hFeq]; exact hcon n
    rw [← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ] at h0
    exact hν (Measure.measure_univ_eq_zero.1 h0)
  obtain ⟨N, hN, hNinv, hNm⟩ : ∃ N : G → ℕ, (∀ g, F (N g) g ≠ 0) ∧ (∀ k g, N ((j k)⁻¹ * g) = N g) ∧
      Measurable (fun g => φ (N g) g * (F (N g) g)⁻¹) := by
    refine ⟨fun g => Nat.find (hFpos g), fun g => Nat.find_spec (hFpos g), ?_, ?_⟩
    · intro k g
      apply Nat.find_congr'
      intro n
      rw [key]
    · convert Measurable.find (p := fun n g => F n g ≠ 0) (f := fun n g => φ n g * (F n g)⁻¹)
        (fun n => (hφ n).mul (hFm n).inv)
        (fun n => ((hFm n) (measurableSet_singleton 0)).compl) hFpos using 4
  refine ⟨fun g => φ (N g) g * (F (N g) g)⁻¹, hNm, fun g => ?_⟩
  simp only [hNinv, key]
  have hm : Measurable fun h => φ (N g) ((j h)⁻¹ * g) := (hφ _).comp (hjm.inv.mul_const g)
  rw [lintegral_mul_const _ hm]
  exact ENNReal.mul_inv_cancel (hN g) (hFfin _ g)

theorem cutoff_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hi g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  have hν0 : ν ≠ 0 := fun h => h0 (by rw [← h2, h, Measure.map_zero])
  haveI : ν.IsHaarMeasure := GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν hν0
  obtain ⟨b, hb, h1⟩ := bruhat_left G R ν hν0 R.subtype hce
  refine ⟨b, hb, fun g => ?_⟩
  rw [← h2, hφ.lintegral_map]
  exact h1 g

theorem weil_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μG μ : Measure G) [SigmaFinite μG] [μG.IsMulLeftInvariant] [SigmaFinite μ] {b : G → ℝ≥0∞}
    (hb : Measurable b) (h2 : ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂(μG.withDensity b) := by
  have hinv : Measurable (Inv.inv : G → G) := measurable_inv
  have hf2 : Measurable fun p : G × G => f (p.2 * p.1) := hf.comp (measurable_snd.mul measurable_fst)
  rw [lintegral_withDensity_eq_lintegral_mul _ hb hf2.lintegral_prod_right']
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, b (s⁻¹ * x) * f x ∂μ ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_mul_const (f := fun s => b (s⁻¹ * x)) _ (hb.comp (hinv.mul_const x)), h2, one_mul]
    _ = ∫⁻ s, ∫⁻ x, b (s⁻¹ * x) * f x ∂μG ∂μ :=
        lintegral_lintegral_swap ((hb.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, b x * f (s * x) ∂μG ∂μ := by
        refine lintegral_congr fun s => ?_
        rw [← lintegral_mul_left_eq_self _ s]
        simp
    _ = ∫⁻ x, ∫⁻ s, b x * f (s * x) ∂μ ∂μG :=
        (lintegral_lintegral_swap ((hb.comp measurable_fst).mul hf2).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun s => f (s * x)) _ (hf.comp (measurable_mul_const x))]
        rfl

section Sub

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem spanLt_mono {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

def Pres (M : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a : ℕ, ∀ v ∈ spanLt e a, M *ᵥ v ∈ spanLt e a

theorem pres_of (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ b : Fin r, M *ᵥ e b ∈ spanLt e (b.1 + 1)) : Pres e M := by
  intro a v hv
  have : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    show Matrix.mulVecLin M (e c) ∈ spanLt e a
    rw [Matrix.mulVecLin_apply]
    exact spanLt_mono e (Nat.succ_le_of_lt hc) (h c)
  have h2 := this hv
  rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at h2
  exact h2

def Good (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ((∀ a : Fin r, M *ᵥ e a ∈ spanLt e a.1) ∧ M *ᵥ z ∈ spanLt e r) ∧
    ∀ y, (∀ a, hJ ε (e a) y = 0) → M *ᵥ y ∈ spanLt e r

variable {ε e z}

theorem Good.pres {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Pres e M :=
  pres_of e M fun b => spanLt_mono e (Nat.le_succ _) (hM.1.1 b)

theorem Good.pres_mul {P M : Matrix (Fin n) (Fin n) ℂ} (hP : Pres e P) (hM : Good ε e z M) :
    Good ε e z (P * M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [← Matrix.mulVec_mulVec]
  · exact hP _ _ (hM.1.1 a)
  · exact hP _ _ hM.1.2
  · exact hP _ _ (hM.2 y hy)

theorem Good.add {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) (hM' : Good ε e z M') :
    Good ε e z (M + M') := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.add_mulVec]
  · exact add_mem (hM.1.1 a) (hM'.1.1 a)
  · exact add_mem hM.1.2 hM'.1.2
  · exact add_mem (hM.2 y hy) (hM'.2 y hy)

theorem Good.neg {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Good ε e z (-M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.neg_mulVec]
  · exact neg_mem (hM.1.1 a)
  · exact neg_mem hM.1.2
  · exact neg_mem (hM.2 y hy)

theorem good_zero : Good ε e z (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> rw [Matrix.zero_mulVec] <;> exact zero_mem _

theorem pres_of_good {g : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) : Pres e g := by
  refine pres_of e g fun b => ?_
  have e1 : g *ᵥ e b = (g - 1) *ᵥ e b + e b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [e1]
  exact add_mem (spanLt_mono e (Nat.le_succ _) (h.1.1 b)) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩)

theorem pres_inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (hP : Pres e g) : Pres e g' := by
  intro a v hv
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.mulVecLin g).restrict (fun x hx => hP a x hx)
  have hf : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = g *ᵥ (w : Fin n → ℂ) := fun w => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hxy
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  have : g' *ᵥ v = w := by
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hw
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this.symm
  rw [this]
  exact w.2

theorem Good.inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h1 : g' * g = 1) :
    Good ε e z (g' - 1) := by
  have e1 : g' - 1 = -(g' * (g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [e1]
  exact (Good.pres_mul (pres_inv h1 (pres_of_good h)) h).neg

theorem Good.mul {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h' : Good ε e z (g' - 1)) :
    Good ε e z (g * g' - 1) := by
  have e1 : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
  rw [e1]
  exact ((Good.pres_mul h.pres h').add h).add h'

variable (ε e z)

def nSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := NLoc ε e z
  one_mem' := by
    show Good ε e z (uMat (1 : Formalism.REAL.UJ ε) - 1)
    have : uMat (1 : Formalism.REAL.UJ ε) - 1 = 0 := sub_self _
    rw [this]
    exact good_zero
  mul_mem' := fun {x y} hx hy => Good.mul hx hy
  inv_mem' := fun {x} hx => Good.inv hx (Units.inv_mul (x : (Matrix (Fin n) (Fin n) ℂ)ˣ))

theorem isClosed_nLoc : IsClosed (NLoc ε e z) := by
  have hW : ∀ a, IsClosed ((spanLt e a : Set (Fin n → ℂ))) := fun a => Submodule.closed_of_finiteDimensional _
  have hc : ∀ (v : Fin n → ℂ) (a : ℕ), IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ v ∈ spanLt e a} :=
    fun v a => (hW a).preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  have hM : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} := by
    simp only [InN, InS, Set.setOf_and, Set.setOf_forall]
    exact ((isClosed_iInter fun a => hc _ _).inter (hc _ _)).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => hc _ _)
  exact hM.preimage (Units.continuous_val.comp continuous_subtype_val)

variable (z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε)

def stSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := StSet (NLoc ε e z) (NLoc ε e z') γ
  one_mem' := ⟨(nSub ε e z).one_mem, by
    have : γ⁻¹ * 1 * γ = 1 := by group
    rw [this]; exact (nSub ε e z').one_mem⟩
  mul_mem' := fun {x y} hx hy => ⟨(nSub ε e z).mul_mem hx.1 hy.1, by
    have : γ⁻¹ * (x * y) * γ = (γ⁻¹ * x * γ) * (γ⁻¹ * y * γ) := by group
    rw [this]; exact (nSub ε e z').mul_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨(nSub ε e z).inv_mem hx.1, by
    have : γ⁻¹ * x⁻¹ * γ = (γ⁻¹ * x * γ)⁻¹ := by group
    rw [this]; exact (nSub ε e z').inv_mem hx.2⟩

theorem isClosed_stSub : IsClosed (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) := by
  have h1 : (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) =
      NLoc ε e z ∩ (fun y => γ⁻¹ * y * γ) ⁻¹' NLoc ε e z' := rfl
  have h2 : Continuous (fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ) :=
    (continuous_mul_right γ).comp (continuous_mul_left γ⁻¹)
  rw [h1]
  exact (isClosed_nLoc ε e z).inter ((isClosed_nLoc ε e z').preimage h2)

end Sub

theorem quot_exists : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, ∃ νv, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) νv) ∧ ∃ ν, IsQuotMeasS X.B.I (Measure.pi μl) ν := by
  intro D X u u' γ μl hμ
  have hloc : ∀ v, ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧
      ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂(μl v) = 1 := by
    intro v
    haveI := (hμ v).1
    exact cutoff_left (stSub (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (rv X.B.I v (X.zR u')) (γ v)) (μl v) (isClosed_stSub _ _ _ _ _) (hμ v).2.1 (hμ v).2.2.1
      (fun s hs => (hμ v).2.2.2 s hs)
  choose b hb h1 using hloc
  haveI : ∀ v, SigmaFinite (μl v) := fun v => (hμ v).1
  refine ⟨fun v => ⟨(Formalism.REAL.muG _).withDensity (b v), fun f hf => weil_of_cutoff _ _ (hb v) (h1 v) f hf⟩,
    (Formalism.L2.SG.ProjRows.muInf X.B.I).withDensity (fun x => ∏ v, b v (x v)),
    fun f hf => weil_of_cutoff _ _ ?_ ?_ f hf⟩
  · exact Finset.measurable_prod _ fun v _ => (hb v).comp (measurable_pi_apply v)
  · intro g
    have := GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun v s => b v (s⁻¹ * g v))
      fun v => (hb v).comp (measurable_inv.mul_const _)
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [this]
    simp [h1]

end GlobalTheory.QuotExist
end
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, ∃ νv, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) νv) ∧ ∃ ν, IsQuotMeasS X.B.I (Measure.pi μl) ν := by
  atlas_forward_decl GlobalTheory.QuotExist.quot_exists
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  atlas_forward_decl GlobalTheory.AmpLift.amp_lift
end
