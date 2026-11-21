import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShift
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUCentre

lemma card_lt_add_card_gt {n : ℕ} (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ((univ.filter fun b => lam b < lam a).card : ℝ) + ((univ.filter fun b => lam a < lam b).card : ℝ) + 1 = n := by
  have h1 : (univ.filter fun b => lam b ≠ lam a) = univ.erase a := by
    ext b; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun h e => h (e ▸ rfl), fun h e => h (hinj e)⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b => lam b ≠ lam a)
    (fun b => lam b < lam a)
  have h3 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => lam b < lam a) = univ.filter fun b => lam b < lam a := by
    ext b; simp only [mem_filter, mem_univ, true_and]; exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  have h4 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => ¬ lam b < lam a) = univ.filter fun b => lam a < lam b := by
    ext b; simp only [mem_filter, mem_univ, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨h.ne', h.le⟩⟩
  rw [h3, h4, h1, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin] at h2
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ a).elim0)
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [← h2] at this
  push_cast at this
  linarith

lemma card_split {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    ((univ.filter fun b => P b ∧ Q b).card : ℝ) + ((univ.filter fun b => P b ∧ ¬ Q b).card : ℝ) =
      ((univ.filter P).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := univ.filter P) Q
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact_mod_cast h

lemma lowCh_shift_int {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsParU lam) (c : ℝ) (a : Fin n) :
    ∃ k : ℤ, lowCh ε (fun b => lam b - c) a = (k : ℝ) - c := by
  obtain ⟨m0, hm0⟩ := hlam.2 a
  have hN : rhoNh ε (fun b => lam b - c) a = rhoNh ε lam a := by
    simp only [rhoNh, sub_lt_sub_iff_right]
  have hC : rhoCh ε (fun b => lam b - c) a = rhoCh ε lam a := by
    simp only [rhoCh, sub_lt_sub_iff_right]
  have hsum := card_lt_add_card_gt lam hlam.1 a
  have s1 := card_split (fun b => lam b < lam a) (fun b => ε b = ε a)
  have s2 := card_split (fun b => lam a < lam b) (fun b => ε b = ε a)
  refine ⟨m0 + ((univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card : ℤ)
    + ((univ.filter fun b => lam a < lam b ∧ ε b = ε a).card : ℤ), ?_⟩
  have e : lowCh ε (fun b => lam b - c) a
      = lam a - c + rhoNh ε (fun b => lam b - c) a - rhoCh ε (fun b => lam b - c) a := rfl
  rw [e, hN, hC]
  simp only [rhoNh, rhoCh]
  push_cast
  simp only [ne_eq] at *
  linarith

lemma scalar_as_torus {n : ℕ} (a0 : Fin n) (z : ℂ) (hz : z ^ n = 1) :
    ∃ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) = z ∧
      ∑ a, (if a = a0 then t - n * t else t) = 0 ∧
      z • (1 : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun a => Complex.exp ((((if a = a0 then t - n * t else t : ℝ)) : ℂ) * Complex.I)) := by
  have hn : n ≠ 0 := fun h => (h ▸ a0).elim0
  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp this
  set t := Complex.arg z
  have ht : Complex.exp ((t : ℂ) * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hnorm] at this; simpa using this
  have ht' : Complex.exp (((t - n * t : ℝ) : ℂ) * Complex.I) = z := by
    push_cast
    rw [sub_mul, Complex.exp_sub, mul_assoc, Complex.exp_nat_mul, ht, hz, div_one]
  refine ⟨t, ht, ?_, ?_⟩
  · have e : ∀ a : Fin n, (if a = a0 then t - n * t else t) = t - (if a = a0 then n * t else 0) := by
      intro a; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h0 : i = a0
      · simp only [h0, diagonal_apply_eq, if_true, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]; exact ht'.symm
      · simp [h0, ht]
    · simp [hij]

theorem centre_acts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) →
    IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v,
    π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  intro n hn ε H _ _ π' lam m hpar hsum hHC z hz v
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  let a0 : Fin n := ⟨0, hn⟩
  obtain ⟨t, ht, hθsum, hdiag⟩ := scalar_as_torus a0 z hz
  obtain ⟨hirr, _, ⟨S0, hS0, _⟩, _⟩ := hHC
  obtain ⟨hΛsum, _, _, _, ⟨v0, _, hv0, hwt⟩, _⟩ := hS0
  obtain ⟨k, hk⟩ := lowCh_shift_int ε lam hpar ((m : ℝ) / n) a0
  set Λ := lowCh ε (fun a => lam a - (m : ℝ) / n)

  have hscal : ∑ a, Λ a * (if a = a0 then t - n * t else t) = -(n : ℝ) * t * k + t * m := by
    have e : ∀ a : Fin n, Λ a * (if a = a0 then t - n * t else t) = Λ a * t - (if a = a0 then Λ a0 * (n * t) else 0) := by
      intro a; split_ifs with h
      · subst h; ring
      · ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, ← Finset.sum_mul, hΛsum, zero_mul]
    rw [hk]; field_simp; ring
  have key : π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 = z ^ m • v0 := by
    rw [hdiag, hwt _ hθsum, hscal]
    congr 1
    have e2 : (((-(n : ℝ) * t * k + t * m : ℝ)) : ℂ) * Complex.I
        = ((-((n : ℤ) * k) : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((m : ℤ) : ℂ) * ((t : ℂ) * Complex.I) := by
      push_cast; ring
    rw [e2, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, ht, _root_.zpow_neg, _root_.zpow_mul, zpow_natCast, hz,
      _root_.one_zpow, inv_one, one_mul]

  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).mp this
  have hzSU : z • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
    refine ⟨?_, ?_⟩
    · show (z • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * Jm ε * (z • 1) = Jm ε
      have hc : z * star z = 1 := by
        rw [Complex.star_def, Complex.mul_conj', hnorm]; simp
      rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, hc, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, det_one, mul_one, hz]
  have hrep := hirr.2.2.1.1.2
  set f : H →L[ℂ] H := π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) - z ^ m • ContinuousLinearMap.id ℂ H
  have hmem : ∀ w, w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) ↔ π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) w = z ^ m • w := by
    intro w
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, f, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  have hclosed : IsClosed ((LinearMap.ker (f : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := ContinuousLinearMap.isClosed_ker f
  have hstab : ∀ g ∈ SUset ε, ∀ w ∈ LinearMap.ker (f : H →ₗ[ℂ] H), π' g w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) := by
    intro g hg w hw
    rw [hmem] at hw ⊢
    have hcomm : z • (1 : Matrix (Fin n) (Fin n) ℂ) * g = g * (z • 1) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have h1 := hrep _ hzSU g hg
    have h2 := hrep g hg _ hzSU
    rw [hcomm] at h1
    calc π' (z • 1) (π' g w) = ((π' (z • 1)).comp (π' g)) w := rfl
      _ = (π' g) (π' (z • 1) w) := by rw [← h1, h2]; rfl
      _ = z ^ m • π' g w := by rw [hw, map_smul]
  rcases hirr.2.2.2.1 (LinearMap.ker (f : H →ₗ[ℂ] H)) hclosed hstab with h | h
  · exact absurd (by rw [← Submodule.mem_bot ℂ, ← h, hmem]; exact key) hv0
  · exact (hmem v).mp (h ▸ Submodule.mem_top)

end GlobalTheory.SUCentre
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_central_action : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) → IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  atlas_forward_decl GlobalTheory.SUCentre.centre_acts
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUExt

variable {n : ℕ}

lemma one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show Formalism.REAL.inUJ ε 1
  simp [Formalism.REAL.inUJ]

lemma mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  change Formalism.REAL.inUJ ε a at ha1
  change Formalism.REAL.inUJ ε b at hb1
  show Formalism.REAL.inUJ ε (a * b)
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha1, hb1]

lemma ne_zero_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma central_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hgz : z⁻¹ • g ∈ SUset ε) (hgw : w⁻¹ • g ∈ SUset ε) :
    z ^ m • π' (z⁻¹ • g) = w ^ m • π' (w⁻¹ • g) := by
  have hz0 := ne_zero_of_norm_one hz
  have hw0 := ne_zero_of_norm_one hw
  set ζ := z * w⁻¹ with hζ
  have hkey : w⁻¹ • g = (ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) * (z⁻¹ • g) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
    congr 1
    rw [hζ]; field_simp
  have hζn : ζ ^ n = 1 := by
    have h1 := congrArg Matrix.det hkey
    rw [hgw.2, Matrix.det_mul, hgz.2, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h1
    simpa using h1.symm
  have hζnorm : ‖ζ‖ = 1 := by rw [hζ, norm_mul, norm_inv, hz, hw]; simp
  have hζ1 : ζ • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε :=
    ⟨((GlobalTheory.T.unitary_to_special_unitary_local n hn ε).2.1 ζ hζnorm 1 (one_mem_SUset ε)).1,
      by rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, hζn, mul_one]⟩
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hkey, hrep.1.2 _ hζ1 _ hgz,
    ContinuousLinearMap.comp_apply, hc ζ hζn, smul_smul]
  congr 1
  rw [hζ, mul_zpow, _root_.inv_zpow, mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero m hw0), mul_one]

open Classical in

def extRep (ε : Fin n → Bool) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  if h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε then h.choose ^ m • π' (h.choose⁻¹ • g) else 0

lemma extRep_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hz : ‖z‖ = 1) (hg : z⁻¹ • g ∈ SUset ε) :
    extRep ε m π' g = z ^ m • π' (z⁻¹ • g) := by
  have h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε := ⟨z, hz, hg⟩
  rw [extRep, dif_pos h]
  exact central_eq hn m π' hrep hc h.choose_spec.1 hz h.choose_spec.2 hg

theorem extends_to_U : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (SUset ε) π' →
    (∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v) →
    ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsURepOn (UJset ε) π := by
  intro n hn ε H _ _ m π' hrep hc
  have hS := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have hE : Ext ε m π' (extRep ε m π') := by
    intro z hz g hg
    have hg' : z⁻¹ • (z • g) ∈ SUset ε := by
      rwa [smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
    rw [extRep_eq hn m π' hrep hc hz hg', smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
  refine ⟨extRep ε m π', hE, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · have h1 := hE 1 (by simp) 1 (one_mem_SUset ε)
    rw [one_smul] at h1
    rw [h1, _root_.one_zpow, one_smul, hrep.1.1]
  · intro a ha b hb
    obtain ⟨z, hz, a₀, ha₀, rfl, -⟩ := hS.1 a ha
    obtain ⟨w, hw, b₀, hb₀, rfl, -⟩ := hS.1 b hb
    have hab : z • a₀ * w • b₀ = (z * w) • (a₀ * b₀) := smul_mul_smul_comm z a₀ w b₀
    rw [hab, hE _ (by rw [norm_mul, hz, hw, one_mul]) _ (mul_mem_SUset ha₀ hb₀), hE z hz a₀ ha₀,
      hE w hw b₀ hb₀, hrep.1.2 a₀ ha₀ b₀ hb₀]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul,
      mul_zpow]
    rw [mul_comm (w ^ m)]
  · intro g hg v
    obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hS.1 g hg
    rw [hE z hz g₀ hg₀, ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, hz, _root_.one_zpow, one_mul,
      hrep.2.1 g₀ hg₀ v]
  · intro v g hg
    obtain ⟨U, ζ, hUo, hgU, hζc, hζ⟩ := hS.2.2 g hg
    have hζc' : ContinuousOn ζ (UJset ε ∩ U) := hζc.mono Set.inter_subset_right
    have hne : ∀ x ∈ UJset ε ∩ U, ζ x ≠ 0 := fun x hx => ne_zero_of_norm_one (hζ x hx.2 hx.1).1
    have h1 : ContinuousOn (fun x => ζ x ^ m) (UJset ε ∩ U) :=
      hζc'.zpow₀ m (fun x hx => Or.inl (hne x hx))
    have h2 : ContinuousOn (fun x => (ζ x)⁻¹ • x) (UJset ε ∩ U) :=
      (hζc'.inv₀ hne).smul continuousOn_id
    have h3 : ContinuousOn (fun x => π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) :=
      (hrep.2.2 v).comp h2 (fun x hx => (hζ x hx.2 hx.1).2)
    have hs : ContinuousOn (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) := h1.smul h3
    have heq : Set.EqOn (fun x => extRep ε m π' x v) (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v)
        (UJset ε ∩ U) := by
      intro x hx
      simp only
      rw [extRep_eq hn m π' hrep hc (hζ x hx.2 hx.1).1 (hζ x hx.2 hx.1).2,
        ContinuousLinearMap.smul_apply]
    exact (continuousWithinAt_inter (hUo.mem_nhds hgU)).1 ((hs.congr heq) g ⟨hg, hgU⟩)

end GlobalTheory.SUExt

end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_special_unitary_rep : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (SUset ε) π' → (∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v) → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsURepOn (UJset ε) π := by
  atlas_forward_decl GlobalTheory.SUExt.extends_to_U
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCentral

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_det_real : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) := by
  have h : (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) (σ i) i

theorem norm_det_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ‖g.det‖ = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det * (Jm ε).det = 1 := by rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]
  have hJ0 : (Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det := by linear_combination h
    exact mul_right_cancel₀ hJ0 this
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  have h4 : Complex.normSq g.det = 1 := by exact_mod_cast h3
  have h5 : ‖g.det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h4
  have := norm_nonneg g.det
  nlinarith

theorem inUJ_smul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) {c : ℂ} (hc : ‖c‖ = 1) :
    inUJ ε (c • g) := by
  unfold inUJ at *
  have hc2 : star c * c = 1 := by
    have : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    rw [Complex.normSq_eq_conj_mul_self] at this; exact this
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hg, mul_comm, hc2, one_smul]

theorem norm_eq_one_of_pow {w : ℂ} {k : ℕ} (hk : k ≠ 0) (h : ‖w‖ ^ k = 1) : ‖w‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg w) hk).1 h

theorem smooth_of_central : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  intro n hn ε m f f' hf hS g₀ hg₀
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  set d₀ := g₀.det with hd₀def
  have hd₀ : ‖d₀‖ = 1 := norm_det_of_inUJ hg₀
  have hd₀ne : d₀ ≠ 0 := by intro h; rw [h, norm_zero] at hd₀; exact zero_ne_one hd₀
  set z₀ := Complex.exp (Complex.log d₀ / n) with hz₀def
  have hz₀n : z₀ ^ n = d₀ := by
    rw [hz₀def, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (Complex.log d₀ / n) = Complex.log d₀ := by field_simp
    rw [this, Complex.exp_log hd₀ne]
  have hz₀ne : z₀ ≠ 0 := Complex.exp_ne_zero _
  have hz₀norm : ‖z₀‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hz₀n, hd₀])
  set L : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => Complex.log (x.det / d₀) with hLdef
  set ζ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀ * Complex.exp (L x / n) with hζdef
  set ζi : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀⁻¹ * Complex.exp (-(L x / n)) with hζidef
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.det / d₀ ∈ Complex.slitPlane} with hUdef
  have hUo : IsOpen U := Complex.isOpen_slitPlane.preimage ((contDiff_det_real.continuous).div_const _)
  have hg₀U : g₀ ∈ U := by
    show g₀.det / d₀ ∈ Complex.slitPlane
    rw [← hd₀def, div_self hd₀ne]; exact Complex.one_mem_slitPlane
  have hL : ContDiffOn ℝ ∞ L U := by
    intro x hx
    have h1 : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det / d₀) x :=
      (contDiff_det_real.div_const d₀).contDiffAt
    have h2 : ContDiffAt ℝ ∞ Complex.log (x.det / d₀) := (Complex.contDiffAt_log hx).restrict_scalars ℝ
    exact (h2.comp x h1).contDiffWithinAt
  have hζi : ContDiffOn ℝ ∞ ζi U := contDiffOn_const.mul ((hL.div_const _).neg.cexp)
  have hζ : ContDiffOn ℝ ∞ ζ U := contDiffOn_const.mul ((hL.div_const _).cexp)
  have hh : ContDiffOn ℝ ∞ (fun x => ζi x • x) U := hζi.smul contDiffOn_id
  have hζζi : ∀ x, ζ x * ζi x = 1 := by
    intro x
    simp only [hζdef, hζidef]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hz₀ne, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hζne : ∀ x, ζ x ≠ 0 := fun x => left_ne_zero_of_mul_eq_one (hζζi x)
  have hζn : ∀ x ∈ U, ζ x ^ n = x.det := by
    intro x hx
    have hx0 : x.det / d₀ ≠ 0 := Complex.slitPlane_ne_zero hx
    simp only [hζdef]
    rw [mul_pow, hz₀n, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (L x / n) = L x := by field_simp
    rw [this]
    simp only [hLdef]
    rw [Complex.exp_log hx0]
    field_simp
  have hζig₀ : ζi g₀ = z₀⁻¹ := by
    simp only [hζidef, hLdef]
    rw [← hd₀def, div_self hd₀ne, Complex.log_one, zero_div, neg_zero, Complex.exp_zero, mul_one]
  have hinvnorm : ‖z₀⁻¹‖ = 1 := by rw [norm_inv, hz₀norm, inv_one]
  have hg₁ : z₀⁻¹ • g₀ ∈ SUset ε := by
    refine ⟨inUJ_smul hg₀ hinvnorm, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz₀n, ← hd₀def, inv_mul_cancel₀ hd₀ne]
  obtain ⟨U', F', hU'o, hg₁U', hF', hF'eq⟩ := hS _ hg₁
  have hzpow : ContDiffOn ℝ ∞ (fun x => ζ x ^ m) U := by
    intro x hx
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simpa only [zpow_natCast] using (hζ x hx).pow k
    · refine (((hζ x hx).pow k).inv (pow_ne_zero k (hζne x))).congr (fun y _ => ?_) ?_ <;>
        simp [_root_.zpow_neg]
  refine ⟨U ∩ (fun x => ζi x • x) ⁻¹' U', fun x => ζ x ^ m * F' (ζi x • x),
    hh.continuousOn.isOpen_inter_preimage hUo hU'o, ⟨hg₀U, ?_⟩, ?_, ?_⟩
  · show ζi g₀ • g₀ ∈ U'
    rw [hζig₀]; exact hg₁U'
  · exact (hzpow.mono Set.inter_subset_left).mul
      (hF'.comp (hh.mono Set.inter_subset_left) fun x hx => hx.2)
  · intro x hx hxU
    have hxdet : ‖x.det‖ = 1 := norm_det_of_inUJ hxU
    have hnorm : ‖ζ x‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hζn x hx.1, hxdet])
    have hζi_eq : ζi x = (ζ x)⁻¹ := eq_inv_of_mul_eq_one_right (hζζi x)
    have hinorm : ‖ζi x‖ = 1 := by rw [hζi_eq, norm_inv, hnorm, inv_one]
    have hdet0 : x.det ≠ 0 := by intro h; rw [h, norm_zero] at hxdet; exact zero_ne_one hxdet
    have hmem : ζi x • x ∈ SUset ε := by
      refine ⟨inUJ_smul hxU hinorm, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, hζi_eq, inv_pow, hζn x hx.1, inv_mul_cancel₀ hdet0]
    calc f x = f (ζ x • (ζi x • x)) := by rw [smul_smul, hζζi, one_smul]
      _ = ζ x ^ m * f' (ζi x • x) := hf _ hnorm _ hmem
      _ = ζ x ^ m * F' (ζi x • x) := by rw [hF'eq _ hx.2 hmem]

end GlobalTheory.SmoothCentral
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_on_group_of_special : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  atlas_forward_decl GlobalTheory.SmoothCentral.smooth_of_central
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Local

variable {n : ℕ}

theorem trace_traceFreeMatrixUnit_eq_zero (a b : Fin n) : (E0 a b).trace = 0 := by
  have hn : (n : ℂ) ≠ 0 := by
    have : 0 < n := Fin.pos a
    exact_mod_cast this.ne'
  unfold E0
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  by_cases h : a = b
  · subst h
    simp [hn]
  · simp [h, Matrix.trace_single_eq_of_ne _ _ _ h]

theorem trace_theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε).trace = 0 := by
  rw [Matrix.trace_mul_cycle, Formalism.REAL.Jm_mul_self, Matrix.one_mul, Matrix.trace_conjTranspose, hZ, star_zero]

theorem trace_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart1 ε Z).trace = 0 := by
  unfold cpart1
  rw [Matrix.trace_smul, Matrix.trace_sub, trace_theta ε Z hZ, hZ, sub_zero, smul_zero]

theorem trace_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart2 ε Z).trace = 0 := by
  unfold cpart2
  rw [Matrix.trace_smul, Matrix.trace_add, trace_theta ε Z hZ, hZ, add_zero, smul_zero]

theorem mul_exp_mem (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    (hg : g ∈ SUset ε) (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ SUset ε := by
  refine ⟨indefinite_unitary_mul_mem ε hg.1 (exp_indefinite_unitary_holds n ε X hX t), ?_⟩
  rw [Matrix.det_mul, hg.2, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, h0, smul_zero, Complex.exp_zero, one_mul]

theorem rd_congr (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g ∈ SUset ε, G₁ g = G₂ g) (hg : g ∈ SUset ε) :
    Rd X G₁ g = Rd X G₂ g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (mul_exp_mem ε hX h0 hg t)

theorem matrix_unit_action_congr : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n),
    (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  intro n ε G₁ G₂ a b h g hg
  obtain ⟨h1, h2, -⟩ := complex_parts_mem_lie_algebra_holds n ε (E0 a b)
  unfold Ec
  rw [rd_congr ε h1 (trace_cpart1 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg, rd_congr ε h2 (trace_cpart2 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg]

end GlobalTheory.DSSU.Local
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n), (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  atlas_forward_decl GlobalTheory.DSSU.Local.matrix_unit_action_congr
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralLetter

variable {n : ℕ}

theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix (Fin n) (Fin n) ℂ)) = Complex.exp c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem inG_imag (ε : Fin n → Bool) (s : ℝ) :
    inG ε (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold inG
  simp [Matrix.conjTranspose_smul]

theorem Rd_central (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hG : ∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x)
    (s : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) (hx : inUJ ε x) :
    Rd (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) G x = (m : ℂ) * (s * Complex.I) * G x := by
  unfold Rd
  have h1 : (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • (((s : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)))))
      = fun t : ℝ => Complex.exp ((t : ℂ) * ((m : ℂ) * (s * Complex.I))) * G x := by
    funext t
    rw [smul_smul, exp_smul_one, Matrix.mul_smul, Matrix.mul_one, hG _ _ x hx, ← Complex.exp_int_mul]
    · congr 2; ring
    · rw [← mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [h1]
  have h2 : HasDerivAt (fun t : ℂ => Complex.exp (t * ((m : ℂ) * (s * Complex.I))) * G x)
      ((m : ℂ) * (s * Complex.I) * G x) ((0 : ℝ) : ℂ) := by
    have := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const ((m : ℂ) * (s * Complex.I))).cexp).mul_const (G x)
    simpa using this
  exact h2.comp_ofReal.deriv

theorem cpart1_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart1 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = cpart1 ε Z := by
  unfold cpart1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal]
  congr 1
  abel

theorem cpart2_add_real (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    cpart2 ε (Z + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      cpart2 ε Z + ((((-r : ℝ)) : ℂ) * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold cpart2
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Jm_mul_self, Complex.star_def, Complex.conj_ofReal,
    add_add_add_comm, smul_add, ← add_smul, smul_smul]
  congr 2
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε G → (∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x) → ∀ (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ), inUJ ε x → Eab ε a b G x = Ec ε (E0 a b) G x + (if a = b then (m : ℂ) / n else 0) * G x := by
  intro n _ ε m G hs hG a b x hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = (if a = b then (n : ℂ)⁻¹ else 0) :=
    ⟨if a = b then (n : ℝ)⁻¹ else 0, by split_ifs <;> simp⟩
  have e : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) = E0 a b + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hr, E0, sub_add_cancel]
  have hm : (if a = b then (m : ℂ) / n else 0) = m * r := by
    rw [hr]; split_ifs <;> simp [div_eq_mul_inv]
  unfold Eab
  rw [e, hm]
  unfold Ec
  rw [cpart1_add_real, cpart2_add_real,
    (right_derivative_linear n ε G G _ _ 0 0 x hs hs (complex_parts_mem_lie_algebra_holds n ε (E0 a b)).2.1 (inG_imag ε (-r)) hx).1,
    Rd_central ε m G hG (-r) x hx]
  push_cast
  linear_combination (-(m : ℂ) * r * G x) * Complex.I_sq

end GlobalTheory.CentralLetter

end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnitDeriv_eq_traceFree_add_degree : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε G → (∀ z : ℂ, ‖z‖ = 1 → ∀ x : Matrix (Fin n) (Fin n) ℂ, inUJ ε x → G (z • x) = z ^ m * G x) → ∀ (a b : Fin n) (x : Matrix (Fin n) (Fin n) ℂ), inUJ ε x → Eab ε a b G x = Ec ε (E0 a b) G x + (if a = b then (m : ℂ) / n else 0) * G x := by
  atlas_forward_decl GlobalTheory.CentralLetter.main
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.TraceBinom

variable {R : Type} [Ring R] {n : ℕ}

theorem pow_succ_apply_path (M : Matrix (Fin n) (Fin n) R) (m : ℕ) (i j : Fin n) :
    (M ^ (m + 1)) i j = ∑ a : Fin m → Fin n,
      (List.ofFn fun l : Fin (m + 1) =>
        M ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.castSucc)
          ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.succ)).prod := by
  induction m generalizing i with
  | zero => simp; rfl
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]
    dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
    simp only [← Fin.cons_snoc_eq_snoc_cons, ← Fin.succ_castSucc, Fin.cons_succ,
      Fin.castSucc_zero, Fin.cons_zero]

theorem sum_cycWord_eq_trace (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map fun p => M p.1 p.2).prod = trace (M ^ (k + 1)) := by
  rw [Matrix.trace]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, pow_succ_apply_path]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [cycWord, List.map_ofFn]
  congr 2
  funext l
  simp only [Function.comp_apply]
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]
  congr 1
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp
  · have e : finRotate (k + 1) l.castSucc = l.succ := by
      ext
      simp [Fin.val_add_one_of_lt (Fin.castSucc_lt_last l)]
    rw [e, Fin.cons_succ, Fin.snoc_castSucc]

theorem trace_add_algebraMap_pow [Algebra ℂ R] (M : Matrix (Fin n) (Fin n) R) (c : ℂ) (k : ℕ) :
    trace ((M + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) ^ (k + 1)) =
      algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1),
        algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * trace (M ^ (j + 1)) := by
  rw [Commute.add_pow (Algebra.commute_algebraMap_right c M), Finset.sum_range_succ', trace_add, trace_sum,
    add_comm]
  congr 1
  · rw [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← map_pow, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.algebraMap_matrix_apply, if_true]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hjk : k + 1 - (j + 1) = k - j := by omega
    have e : M ^ (j + 1) * algebraMap ℂ (Matrix (Fin n) (Fin n) R) c ^ (k + 1 - (j + 1)) *
        (((k + 1).choose (j + 1) : ℕ) : Matrix (Fin n) (Fin n) R) =
        (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) • M ^ (j + 1) := by
      rw [hjk, ← map_pow, ← map_natCast (algebraMap ℂ (Matrix (Fin n) (Fin n) R)), mul_assoc, ← map_mul,
        ← Algebra.commutes, ← Algebra.smul_def, mul_comm (c ^ (k - j))]
    rw [e, trace_smul, Algebra.smul_def]

theorem trace_binomial : ∀ (R : Type) [Ring R] [Algebra ℂ R] (n : ℕ) (T : Fin n → Fin n → R) (c : ℂ) (k : ℕ), ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0)).prod = algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1), algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod := by
  intro R _ _ n T c k
  have hA : (fun p : Fin n × Fin n => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0) =
      fun p => (Matrix.of T + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) p.1 p.2 := by
    funext p
    simp [Matrix.algebraMap_matrix_apply]
  have hT : ∀ j : ℕ, ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod =
      trace (Matrix.of T ^ (j + 1)) := fun j => sum_cycWord_eq_trace (Matrix.of T) j
  rw [hA, sum_cycWord_eq_trace, trace_add_algebraMap_pow]
  simp_rw [hT]

end GlobalTheory.TraceBinom
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_shifted_cyclic_word_expansion : ∀ (R : Type) [Ring R] [Algebra ℂ R] (n : ℕ) (T : Fin n → Fin n → R) (c : ℂ) (k : ℕ), ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0)).prod = algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1), algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod := by
  atlas_forward_decl GlobalTheory.TraceBinom.trace_binomial
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.GelfCentral

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem smoothOnG_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) : SmoothOnG ε (G₁ + G₂) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h₁ g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := h₂ g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgJ
  simp [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

theorem smoothOnG_smul {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (h : SmoothOnG ε G) : SmoothOnG ε (c • G) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h g₀ hg₀
  refine ⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, ?_⟩
  intro g hg hgJ
  simp [hfF g hg hgJ]

theorem smoothOnG_zero (ε : Fin n → Bool) : SmoothOnG ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  intro g₀ _
  exact ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem inUJ_smul {ε : Fin n → Bool} {z : ℂ} (hz : ‖z‖ = 1) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : inUJ ε (z • x) := by
  unfold inUJ at *
  have h1 : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]; norm_num
  have h2 : z * star z = 1 := by rw [mul_comm]; exact h1
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx, h1, h2, one_smul]

def Cent (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ x, inUJ ε x → G (z • x) = z ^ m * G x

theorem rd_congr {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, inUJ ε x → G₁ x = G₂ x) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Rd X G₁ x = Rd X G₂ x := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))

theorem ec_congr {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, inUJ ε x → G₁ x = G₂ x) (Z : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Ec ε Z G₁ x = Ec ε Z G₂ x := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  unfold Ec
  rw [rd_congr h h1 hx, rd_congr h h2 hx]

theorem rd_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : Cent ε m (Rd X G) := by
  intro z hz x hx
  unfold Rd
  have e : (fun t : ℝ => G (z • x * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => z ^ m * G (x * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [Matrix.smul_mul]
    exact h z hz _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))
  rw [e]
  exact deriv_const_mul_field _

theorem ec_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Cent ε m (Ec ε Z G) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  intro z hz x hx
  unfold Ec
  rw [rd_cent h h1 z hz x hx, rd_cent h h2 z hz x hx]
  ring

theorem ec_smooth {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : SmoothOnG ε G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : SmoothOnG ε (Ec ε Z G) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  have s1 := rdSmooth_of right_derivative_extends n ε G _ h h1
  have s2 := rdSmooth_of right_derivative_extends n ε G _ h h2
  have e : Ec ε Z G = Rd (cpart1 ε Z) G + Complex.I • Rd (cpart2 ε Z) G := by
    funext g; simp [Ec]
  rw [e]
  exact smoothOnG_add s1 (smoothOnG_smul Complex.I s2)

theorem rd_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Rd X (G₁ + G₂) x = Rd X G₁ x + Rd X G₂ x := by
  have := (right_derivative_linear n ε G₁ G₂ X X 1 1 x h₁ h₂ hX hX hx).2.2
  have e : (G₁ + G₂) = fun h => G₁ h + (1 : ℂ) * G₂ h := by funext h; simp
  rw [e, this, one_mul]

theorem rd_smul {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (X x : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (c • G) x = c * Rd X G x := by
  show deriv (fun t : ℝ => c * G (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    c * deriv (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • X))) 0
  exact deriv_const_mul_field c

theorem ec_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) (Z : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Ec ε Z (G₁ + G₂) x = Ec ε Z G₁ x + Ec ε Z G₂ x := by
  obtain ⟨c1, c2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  unfold Ec
  rw [rd_add h₁ h₂ c1 hx, rd_add h₁ h₂ c2 hx]
  ring

theorem ec_smul {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (Z x : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z (c • G) x = c * Ec ε Z G x := by
  unfold Ec
  rw [rd_smul, rd_smul]
  ring

def V (ε : Fin n → Bool) (m : ℤ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {G | SmoothOnG ε G ∧ Cent ε m G}
  add_mem' := by
    rintro G₁ G₂ ⟨s1, c1⟩ ⟨s2, c2⟩
    refine ⟨smoothOnG_add s1 s2, fun z hz x hx => ?_⟩
    simp only [Pi.add_apply, c1 z hz x hx, c2 z hz x hx]
    ring
  zero_mem' := ⟨smoothOnG_zero ε, fun z hz x hx => by simp⟩
  smul_mem' := by
    rintro c G ⟨s, cG⟩
    refine ⟨smoothOnG_smul c s, fun z hz x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, cG z hz x hx]
    ring

open Classical in

def trunc (ε : Fin n → Bool) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun x => if inUJ ε x then G x else 0

theorem trunc_of {ε : Fin n → Bool} (G : Matrix (Fin n) (Fin n) ℂ → ℂ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : trunc ε G x = G x := by
  simp [trunc, hx]

theorem trunc_not {ε : Fin n → Bool} (G : Matrix (Fin n) (Fin n) ℂ → ℂ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : ¬ inUJ ε x) : trunc ε G x = 0 := by
  simp [trunc, hx]

theorem trunc_mem {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hs : SmoothOnG ε G)
    (hc : Cent ε m G) : trunc ε G ∈ V ε m := by
  refine ⟨fun g₀ hg₀ => ?_, fun z hz x hx => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hs g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => by rw [trunc_of G hgJ, hfF g hg hgJ]⟩
  · rw [trunc_of G hx, trunc_of G (inUJ_smul hz hx), hc z hz x hx]

def T (ε : Fin n → Bool) (m : ℤ) (a b : Fin n) : Module.End ℂ (V ε m) where
  toFun G := ⟨trunc ε (Ec ε (E0 a b) G.1), trunc_mem (ec_smooth G.2.1 _) (ec_cent G.2.2 _)⟩
  map_add' G₁ G₂ := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply]
    by_cases hx : inUJ ε x
    · rw [trunc_of _ hx, trunc_of _ hx, trunc_of _ hx]
      exact ec_add G₁.2.1 G₂.2.1 _ hx
    · rw [trunc_not _ hx, trunc_not _ hx, trunc_not _ hx, add_zero]
  map_smul' c G := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases hx : inUJ ε x
    · rw [trunc_of _ hx, trunc_of _ hx]
      exact ec_smul c _ x
    · rw [trunc_not _ hx, trunc_not _ hx, mul_zero]

theorem T_apply {ε : Fin n → Bool} {m : ℤ} (a b : Fin n) (G : V ε m) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : ((T ε m a b G : V ε m) : Matrix (Fin n) (Fin n) ℂ → ℂ) x = Ec ε (E0 a b) G.1 x :=
  trunc_of _ hx

def Sop (ε : Fin n → Bool) (m : ℤ) (p : Fin n × Fin n) : Module.End ℂ (V ε m) :=
  T ε m p.1 p.2 + if p.1 = p.2 then algebraMap ℂ (Module.End ℂ (V ε m)) ((m : ℂ) / n) else 0

theorem eword_eval (hn : 1 ≤ n) (ε : Fin n → Bool) (m : ℤ) (w : List (Fin n × Fin n)) (G : V ε m) :
    ∀ x, inUJ ε x → Eword ε w G.1 x = (((w.map (Sop ε m)).prod G : V ε m) : _ → ℂ) x := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    generalize hH : (w.map (Sop ε m)).prod G = H at ih ⊢
    show Eab ε p.1 p.2 (Eword ε w G.1) x = _
    have e2 : Eab ε p.1 p.2 (Eword ε w G.1) x = Eab ε p.1 p.2 H.1 x := ec_congr ih _ hx
    rw [e2, GlobalTheory.T.matrixUnitDeriv_eq_traceFree_add_degree n hn ε m H.1 H.2.1 H.2.2 p.1 p.2 x hx]
    unfold Sop
    rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, T_apply _ _ _ hx]
    by_cases h : p.1 = p.2
    · rw [if_pos h, if_pos h, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    · rw [if_neg h, if_neg h, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply, zero_mul]

theorem ewordS_eval (ε : Fin n → Bool) (m : ℤ) (w : List (Fin n × Fin n)) (G : V ε m) :
    ∀ x, inUJ ε x → EwordS ε w G.1 x =
      (((w.map (fun p => T ε m p.1 p.2)).prod G : V ε m) : _ → ℂ) x := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    generalize hH : (w.map (fun p => T ε m p.1 p.2)).prod G = H at ih ⊢
    show Ec ε (E0 p.1 p.2) (EwordS ε w G.1) x = _
    rw [ec_congr ih _ hx, T_apply _ _ _ hx]

theorem gelfS_eval (ε : Fin n → Bool) (m : ℤ) (j : ℕ) (G : V ε m) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : gelfS ε j G.1 x = (((∑ a : Fin (j + 1) → Fin n,
      ((cycWord a).map (fun p => T ε m p.1 p.2)).prod) G : V ε m) : _ → ℂ) x := by
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => ewordS_eval ε m _ G x hx

theorem gelf_eval (hn : 1 ≤ n) (ε : Fin n → Bool) (m : ℤ) (k : ℕ) (G : V ε m)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) :
    gelf ε k G.1 x = ((m : ℂ) / n) ^ (k + 1) * n * G.1 x + ∑ j ∈ range (k + 1),
      ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j G.1 x := by
  have e1 : gelf ε k G.1 x = (((∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (Sop ε m)).prod) G : V ε m) :
      _ → ℂ) x := by
    rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => eword_eval hn ε m _ G x hx
  have hL := GlobalTheory.T.prod_shifted_cyclic_word_expansion (Module.End ℂ (V ε m)) n (T ε m) ((m : ℂ) / n) k
  rw [e1]
  unfold Sop
  rw [hL]
  simp only [gelfS_eval ε m _ G hx, LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply,
    Module.End.mul_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

theorem ewordS_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    (w : List (Fin n × Fin n)) : Cent ε m (EwordS ε w G) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ec_cent ih _

theorem ewordS_SU {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ SUset ε, G₁ g = G₂ g) (w : List (Fin n × Fin n)) :
    ∀ g ∈ SUset ε, EwordS ε w G₁ g = EwordS ε w G₂ g := by
  induction w with
  | nil => exact h
  | cons p w ih => exact GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup n ε _ _ p.1 p.2 ih

theorem gelf_central : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f ∧ ∀ (k : ℕ) (z : ℂ), ‖z‖ = 1 → ∀ g ∈ SUset ε, gelf ε k f (z • g) = z ^ m * (((m : ℂ) / n) ^ (k + 1) * n * f' g + ∑ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j f' g) := by
  intro n hn ε m f f' hff' hs'
  have hsm : SmoothOnG ε f := GlobalTheory.T.smooth_on_group_of_special n hn ε m f f' hff' hs'
  refine ⟨hsm, ?_⟩
  have hcent : Cent ε m f := by
    intro z hz x hx
    obtain ⟨w, hw, g₀, hg₀, rfl, -⟩ := (GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 x hx
    rw [smul_smul, hff' (z * w) (by rw [norm_mul, hz, hw, one_mul]) g₀ hg₀, hff' w hw g₀ hg₀, mul_zpow]
    ring
  have hfg : ∀ g ∈ SUset ε, f g = f' g := fun g hg => by
    simpa using hff' 1 (by simp) g hg
  intro k z hz g hg
  have hgU : inUJ ε g := hg.1
  have hx : inUJ ε (z • g) := inUJ_smul hz hgU
  have e := gelf_eval hn ε m k ⟨f, hsm, hcent⟩ hx
  simp only at e
  rw [e]
  have hgS : ∀ j, gelfS ε j f (z • g) = z ^ m * gelfS ε j f' g := by
    intro j
    simp only [gelfS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ewordS_cent hcent _ z hz g hgU, ewordS_SU hfg _ g hg]
  simp only [hgS, hff' z hz g hg, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.GelfCentral
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f ∧ ∀ (k : ℕ) (z : ℂ), ‖z‖ = 1 → ∀ g ∈ SUset ε, gelf ε k f (z • g) = z ^ m * (((m : ℂ) / n) ^ (k + 1) * n * f' g + ∑ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j f' g) := by
  atlas_forward_decl GlobalTheory.GelfCentral.gelf_central
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.InfCharExt

variable {n : ℕ}

theorem kset_sub_ujset (ε : Fin n → Bool) : ∀ g ∈ Kset ε, g ∈ UJset ε := by
  intro g hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Jm ε * g = Jm ε
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc]
  rw [show gᴴ = star g from rfl, h1, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ext_eq_on_su {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) : ∀ g ∈ SUset ε, π g = π' g := by
  intro g hg
  have := hE 1 (by simp) g hg
  simpa using this

theorem kfin_to_kfinS {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) {v : H} (hv : IsKFin ε π v) : IsKFinS ε π' v := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S, hS, hvS, ?_⟩
  intro g hg x hx
  have hgS : g ∈ SUset ε := ⟨kset_sub_ujset ε g hg.1, hg.2⟩
  rw [← ext_eq_on_su hE g hgS]
  exact hst g hg.1 x hx

theorem coeff_shift {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) (v w : H) :
    ∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, (fun g => ⟪w, π g v⟫_ℂ) (z • g) = z ^ m * (fun g => ⟪w, π' g v⟫_ℂ) g := by
  intro z hz g hg
  simp only
  rw [hE z hz g hg, ContinuousLinearMap.smul_apply, inner_smul_right]

end GlobalTheory.InfCharExt

theorem GlobalTheory.infChar_of_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π →
    ∀ χ : Fin n → ℂ, HasInfCharS ε χ π' → HasInfChar ε (fun a => χ a + (m : ℂ) / n) π := by
  intro n hn ε H _ _ m π' π hE χ hχ v w hv hw
  have hv' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hv
  have hw' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hw
  obtain ⟨hsm, heig⟩ := hχ v w hv' hw'
  obtain ⟨hG1, hG2⟩ := GlobalTheory.T.gelfand_operator_extension n hn ε m (fun g => ⟪w, π g v⟫_ℂ) (fun g => ⟪w, π' g v⟫_ℂ)
    (GlobalTheory.InfCharExt.coeff_shift hE v w) hsm
  refine ⟨hG1, ?_⟩
  intro k g hg
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
  obtain ⟨hval, hval0, -⟩ := GlobalTheory.T.gelfand_values_shift n χ
  rw [hG2 k z hz g₀ hg₀, GlobalTheory.InfCharExt.coeff_shift hE v w z hz g₀ hg₀, hval]
  conv_rhs => rw [Finset.sum_range_succ', hval0]
  have hS : ∀ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) *
      gelfS ε j (fun g => ⟪w, π' g v⟫_ℂ) g₀ =
      ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k + 1 - (j + 1)) * gelfVal χ (j + 1) *
        ⟪w, π' g₀ v⟫_ℂ := by
    intro j _
    rw [heig j g₀ hg₀, Nat.add_sub_add_right]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
  ring
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ χ : Fin n → ℂ, HasInfCharS ε χ π' → HasInfChar ε (fun a => χ a + (m : ℂ) / n) π := by
  atlas_forward_decl GlobalTheory.infChar_of_ext
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SURestrict

variable {n : ℕ}

theorem one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show inUJ ε 1
  simp [inUJ]

theorem mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  have ha1' : aᴴ * Jm ε * a = Jm ε := ha1
  have hb1' : bᴴ * Jm ε * b = Jm ε := hb1
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha1', hb1']

theorem Kset_sub_UJset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').mp hu
  show gᴴ * Jm ε * g = Jm ε
  calc gᴴ * Jm ε * g = gᴴ * (g * Jm ε) := by rw [Matrix.mul_assoc, hc]
    _ = (star g * g) * Jm ε := by rw [← Matrix.mul_assoc]; rfl
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem KS_sub_SUset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ KS ε) :
    g ∈ SUset ε := ⟨Kset_sub_UJset hg.1, hg.2⟩

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_on_SU {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : Ext ε m π' π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

theorem restrict_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (IsURepOn (UJset ε) π → IsURepOn (SUset ε) π') ∧ (IsIrredOn (UJset ε) π ↔ IsIrredOn (SUset ε) π') ∧ (∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S) ∧ ∀ v, IsKFin ε π v ↔ IsKFinS ε π' v := by
  intro n hn ε H _ _ m π' π he
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have heq : ∀ g ∈ SUset ε, π g = π' g := fun g hg => eq_on_SU he hg
  have hSU : ∀ g ∈ SUset ε, g ∈ UJset ε := fun g hg => hg.1

  have hstab : ∀ S : Submodule ℂ H, (∀ g ∈ UJset ε, ∀ v ∈ S, π g v ∈ S) ↔
      (∀ g ∈ SUset ε, ∀ v ∈ S, π' g v ∈ S) := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g hg]; exact h g (hSU g hg) v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ hg₀ v hv)
  have hK : ∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g (KS_sub_SUset hg)]; exact h g hg.1 v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, hiff⟩ := hsplit g (Kset_sub_UJset hg)
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ (hiff.mp hg) v hv)
  refine ⟨?_, ?_, hK, ?_⟩
  · rintro ⟨⟨h1, hmul⟩, hiso, hcont⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← heq 1 (one_mem_SUset ε)]; exact h1
    · intro a ha b hb
      rw [← heq _ (mul_mem_SUset ha hb), ← heq a ha, ← heq b hb]
      exact hmul a (hSU a ha) b (hSU b hb)
    · intro g hg v
      rw [← heq g hg]; exact hiso g (hSU g hg) v
    · intro v
      exact ((hcont v).mono (fun g hg => hSU g hg)).congr (fun g hg => by simp only [heq g hg])
  · constructor
    · intro h S hS hst
      exact h S hS ((hstab S).mpr hst)
    · intro h S hS hst
      exact h S hS ((hstab S).mp hst)
  · intro v
    constructor
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mp hs⟩
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mpr hs⟩

end GlobalTheory.SURestrict
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_preserves_properties : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (IsURepOn (UJset ε) π → IsURepOn (SUset ε) π') ∧ (IsIrredOn (UJset ε) π ↔ IsIrredOn (SUset ε) π') ∧ (∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S) ∧ ∀ v, IsKFin ε π v ↔ IsKFinS ε π' v := by
  atlas_forward_decl GlobalTheory.SURestrict.restrict_main
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_iff_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → IsURepOn (UJset ε) π → (IsSqIntOn ε π ↔ IsSqIntS ε π') := by
  first | exact @GlobalTheory.SqIntSU.sqInt_iff | exact GlobalTheory.SqIntSU.sqInt_iff | (intros; apply GlobalTheory.SqIntSU.sqInt_iff <;> assumption)
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUWt

variable {n : ℕ}

abbrev dgm (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

lemma star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

lemma dgm_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) : dgm θ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    exact star_exp_mul (θ a)
  · simp only [dgm, Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma Kset_sub_UJset (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]

lemma KS_sub_SUset (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KS ε) : k ∈ SUset ε :=
  ⟨Kset_sub_UJset ε hk.1, hk.2⟩

lemma dgm_det (θ : Fin n → ℝ) : (dgm θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

lemma dgm_mem_KS (ε : Fin n → Bool) (θ : Fin n → ℝ) (h : ∑ a, θ a = 0) : dgm θ ∈ KS ε :=
  ⟨dgm_mem_Kset ε θ, by rw [dgm_det, h]; simp⟩

lemma dgm_split (θ : Fin n → ℝ) (t : ℝ) :
    dgm θ = Complex.exp ((t : ℂ) * Complex.I) • dgm (fun a => θ a - t) := by
  simp only [dgm]
  rw [← Matrix.diagonal_smul]
  congr 1
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_exp_I (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

lemma star_mul_self_of_norm {w : ℂ} (h : ‖w‖ = 1) : star w * w = 1 := by
  rw [Complex.star_def, Complex.conj_mul', h]; simp

lemma norm_det_of_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ‖k.det‖ = 1 := by
  have hu := hk.1
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  have h1 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Complex.star_def,
    Complex.conj_mul'] at h1
  have h2 : ‖k.det‖ ^ 2 = 1 := by exact_mod_cast h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

lemma Kset_decomp (hn : 1 ≤ n) (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g ∈ KS ε, k = z • g := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq k.det (show 0 < n by omega)
  have hzn : ‖z‖ = 1 := by
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_det_of_Kset hk]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact zero_ne_one hzn
  refine ⟨z, hzn, z⁻¹ • k, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hu := hk.1
    rw [Matrix.mem_unitaryGroup_iff'] at hu ⊢
    rw [star_smul, smul_mul_smul_comm, hu, star_mul_self_of_norm (by rw [norm_inv, hzn, inv_one]), one_smul]
  · rw [smul_mul_assoc, hk.2, mul_smul_comm]
  · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz, inv_mul_cancel₀]
    rw [← hz]; exact pow_ne_zero _ hz0
  · rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma ext_eq {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (he : Ext ε m π' π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma pi_dgm (he : Ext ε m π' π) (θ : Fin n → ℝ) (t : ℝ) (h : ∑ a, (θ a - t) = 0) :
    π (dgm θ) = Complex.exp (((t * m : ℝ) : ℂ) * Complex.I) • π' (dgm fun a => θ a - t) := by
  rw [dgm_split θ t, he _ (norm_exp_I t) _ (KS_sub_SUset ε (dgm_mem_KS ε _ h)), ← Complex.exp_int_mul]
  congr 2
  push_cast; ring

lemma sum_eq_of_wt (he : Ext ε m π' π) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0) (hw : IsWtOn (Kset ε) π μ v) :
    ∑ a, μ a = (m : ℝ) := by
  have h0 : π' (dgm fun _ : Fin n => (0 : ℝ)) v = v := by
    have h1 := hw (fun _ => 0) (dgm_mem_Kset ε _)
    rw [ext_eq he (KS_sub_SUset ε (dgm_mem_KS ε _ (by simp)))] at h1
    simpa using h1
  by_contra hne
  have hd : ∑ a, μ a - (m : ℝ) ≠ 0 := sub_ne_zero.2 hne
  set t : ℝ := Real.pi / (∑ a, μ a - m) with ht
  have h2 := hw (fun _ => t) (dgm_mem_Kset ε _)
  rw [pi_dgm he (fun _ => t) t (by simp)] at h2
  simp only [sub_self] at h2
  rw [ContinuousLinearMap.smul_apply, h0] at h2
  have h4 := smul_left_injective ℂ hv h2
  have h5 : Complex.exp (((∑ a, μ a * t - t * m : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show ((∑ a, μ a * t - t * m : ℝ) : ℂ) * Complex.I =
        ((∑ a, μ a * t : ℝ) : ℂ) * Complex.I - ((t * m : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_sub, ← h4, div_self (Complex.exp_ne_zero _)]
  have h6 : ∑ a, μ a * t - t * m = Real.pi := by
    rw [← Finset.sum_mul, ht]; field_simp
  rw [h6, Complex.exp_pi_mul_I] at h5
  norm_num at h5

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma wt_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (μ : Fin n → ℝ) (v : H) (hv : v ≠ 0) :
    IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v := by
  constructor
  · intro hw
    refine ⟨sum_eq_of_wt he hv hw, fun θ hθ => ?_⟩
    have h1 := hw θ (dgm_mem_Kset ε θ)
    rw [ext_eq he (KS_sub_SUset ε (dgm_mem_KS ε θ hθ))] at h1
    show π' (dgm θ) v = _
    rw [h1]
    congr 4
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hθ, mul_zero, sub_zero]
  · rintro ⟨hs, hw⟩ θ _
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    set t : ℝ := (∑ a, θ a) / n with ht
    have hz : ∑ a, (θ a - t) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]
      field_simp
      ring
    have h2 := hw (fun a => θ a - t) hz
    simp only at h2
    show π (dgm θ) v = _
    rw [pi_dgm he θ t hz, ContinuousLinearMap.smul_apply, h2, smul_smul, ← Complex.exp_add]
    have key : ∑ a, (μ a - (m : ℝ) / n) * (θ a - t) = ∑ a, μ a * θ a - t * m := by
      have : ∑ a, (μ a - (m : ℝ) / n) * (θ a - t) =
          ∑ a, μ a * θ a - t * ∑ a, μ a - (m : ℝ) / n * ∑ a, (θ a - t) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        congr 1; funext a; ring
      rw [this, hs, hz]; ring
    rw [key]
    congr 2
    push_cast; ring

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

lemma above_shift (P : Fin n → Fin n → Prop) (μ Λ : Fin n → ℝ) (d : ℝ) :
    Above P (fun a => μ a - d) (fun a => Λ a - d) ↔ Above P μ Λ := by
  unfold Above
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h; funext a; have := congrFun h a
    simp only [Pi.add_apply, Finset.sum_apply] at this ⊢; linarith
  · intro h; funext a; have := congrFun h a
    simp only [Pi.add_apply, Finset.sum_apply] at this ⊢; linarith

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma stable_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (S : Submodule ℂ H) :
    Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
  constructor
  · intro h g hg v hv
    rw [← ext_eq he (KS_sub_SUset ε hg)]
    exact h g hg.1 v hv
  · intro h k hk v hv
    obtain ⟨z, hz, g, hg, rfl⟩ := Kset_decomp hn ε hk
    rw [he z hz g (KS_sub_SUset ε hg), ContinuousLinearMap.smul_apply]
    exact S.smul_mem _ (h g hg v hv)

lemma ktype_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H) :
    IsKTypeU ε lam π Λ S ↔
      ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum : ∀ ν : Fin n → ℝ, ∑ a, (ν a - (m : ℝ) / n) = ∑ a, ν a - m := by
    intro ν
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hst : ∀ S' : Submodule ℂ H, Stable (Kset ε) π S' ↔ Stable (KS ε) π' S' := stable_iff hn he
  simp only [IsKTypeU, IsKTypeS, sub_lt_sub_iff_right, hst]
  constructor
  · rintro ⟨hfd, hS, hirr, ⟨v, hvS, hv0, hvw⟩, hab⟩
    have hΛ := (wt_iff hn he Λ v hv0).1 hvw
    refine ⟨hΛ.1, by rw [hsum, hΛ.1, sub_self], hfd, hS, hirr, ⟨v, hvS, hv0, hΛ.2⟩, ?_⟩
    intro μ' w hμ' hwS hw0 hww
    have h1 : IsWtOn (Kset ε) π (fun a => μ' a + (m : ℝ) / n) w := by
      rw [wt_iff hn he _ w hw0]
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_add_distrib, hμ', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn0, zero_add]
      · simpa using hww
    have h2 := hab _ w hwS hw0 h1
    rw [← above_shift _ _ _ ((m : ℝ) / n)] at h2
    simpa using h2
  · rintro ⟨hΛs, -, hfd, hS, hirr, ⟨v, hvS, hv0, hvw⟩, hab⟩
    refine ⟨hfd, hS, hirr, ⟨v, hvS, hv0, (wt_iff hn he Λ v hv0).2 ⟨hΛs, hvw⟩⟩, ?_⟩
    intro μ w hwS hw0 hww
    obtain ⟨hμs, hμw⟩ := (wt_iff hn he μ w hw0).1 hww
    have h3 := hab _ w (by rw [hsum, hμs, sub_self]) hwS hw0 hμw
    exact (above_shift _ _ _ _).1 h3

end

end GlobalTheory.SUWt

open GlobalTheory.SUWt in

theorem GlobalTheory.SUWt.wt_ktype_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → (IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v)) ∧ ∀ (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H), IsKTypeU ε lam π Λ S ↔ ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  intro n hn ε H _ _ m π' π he
  exact ⟨fun μ v hv => wt_iff hn he μ v hv, fun lam Λ c S => ktype_iff hn he lam Λ c S⟩
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weights_of_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → (IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v)) ∧ ∀ (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H), IsKTypeU ε lam π Λ S ↔ ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  atlas_forward_decl GlobalTheory.SUWt.wt_ktype_ext
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem rhoNh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoNh ε (fun a => lam a - c) = rhoNh ε lam := by
  funext a
  simp only [rhoNh, sub_lt_sub_iff_right]

theorem rhoCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoCh ε (fun a => lam a - c) = rhoCh ε lam := by
  funext a
  simp only [rhoCh, sub_lt_sub_iff_right]

theorem lowCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    lowCh ε (fun a => lam a - c) = fun a => lowCh ε lam a - c := by
  funext a
  simp only [lowCh, rhoNh_sub_const, rhoCh_sub_const, Pi.add_apply, Pi.sub_apply]
  ring

theorem exists_sum_eq_int (hn : 1 ≤ n) (lam : Fin n → ℝ) (hU : IsParU lam) :
    ∃ m : ℤ, ∑ a, lam a = (m : ℝ) := by
  choose k hk using hU.2
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self n
  refine ⟨(t : ℤ) + ∑ a, k a, ?_⟩
  have hlam : ∀ a, lam a = ((n : ℝ) - 1) / 2 + (k a : ℝ) := fun a => by linarith [hk a]
  have hcast : (n : ℝ) * ((n : ℝ) - 1) = 2 * (t : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) ht
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one] at this
    linarith
  simp only [hlam, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  linarith

theorem extension_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  intro n hn ε H _ _ π' lam hU
  obtain ⟨m, hm⟩ := exists_sum_eq_int hn lam hU
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨m, hm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.sum_sub_distrib, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro a b h
    exact hU.1 (by simpa using h)
  · intro a b
    obtain ⟨ka, hka⟩ := hU.2 a
    obtain ⟨kb, hkb⟩ := hU.2 b
    exact ⟨ka - kb, by push_cast; linarith⟩
  · intro hS
    obtain ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩ := hS
    have hcent := GlobalTheory.T.harish_chandra_central_action n hn ε H π' lam m hU hm ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩
    obtain ⟨π, hext, hrepU⟩ := GlobalTheory.T.extend_special_unitary_rep n hn ε H m π' hrep hcent
    refine ⟨π, hext, ?_⟩
    obtain ⟨-, hirrIff, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H m π' π hext
    have hsqIff := GlobalTheory.T.square_integrable_iff_extension n hn ε H m π' π hext hrepU
    have hinfU := GlobalTheory.T.infinitesimal_character_extension n hn ε H m π' π hext _ hinf
    obtain ⟨-, hKT⟩ := GlobalTheory.T.weights_of_extension n hn ε H m π' π hext
    have hlow := lowCh_sub_const ε lam ((m : ℝ) / n)
    have hsumLow : ∑ a, lowCh ε lam a = (m : ℝ) := by
      have h0 := hS0.1
      rw [hlow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h0
      field_simp at h0
      linarith
    have hKTlow : ∀ S : Submodule ℂ H, IsKTypeU ε lam π (lowCh ε lam) S ↔
        IsKTypeS ε (fun a => lam a - (m : ℝ) / n) π' (lowCh ε (fun a => lam a - (m : ℝ) / n)) S := by
      intro S
      rw [hKT lam (lowCh ε lam) ((m : ℝ) / n) S, hlow]
      exact ⟨fun h => h.2, fun h => ⟨hsumLow, h⟩⟩
    refine ⟨⟨hcomp, hnt, hrepU, hirrIff.2 hirr, hsqIff.2 hsq⟩, ?_, ⟨S0, (hKTlow S0).2 hS0, fun S hS => huniq S ((hKTlow S).1 hS)⟩, ?_⟩
    · convert hinfU using 2 with a
      push_cast
      field_simp
      ring
    · intro μ S hμS
      obtain ⟨-, hμS'⟩ := (hKT lam μ ((m : ℝ) / n) S).1 hμS
      obtain ⟨c, hc, heq⟩ := habove _ S hμS'
      refine ⟨c, fun a b hab => by simpa using hc a b hab, ?_⟩
      funext a
      have := congrFun heq a
      rw [hlow] at this
      simp only [Pi.add_apply] at this ⊢
      linarith

end GlobalTheory.SUtoU

end
end
