import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizPole

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem X_pow_eq : (X : K⟦X⟧) ^ e = E K l e - l := by rw [E]; ring

theorem E_ne_zero : E K l e ≠ 0 := (isUnit_E (K := K) l e).ne_zero

theorem pow_mul_EN (j : ℕ) (f : K⟦X⟧) :
    E K l e ^ j * (E K l e * N K f) =
      E K l e * N K (E K l e ^ j * f) - (j : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * (E K l e ^ j * f) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  cases j with
  | zero => simp
  | succ j => simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem N_pow_mul (j : ℕ) (G : K⟦X⟧) :
    N K (E K l e ^ (j + 1) * G) =
      E K l e ^ (j + 1) * N K G + ((j + 1 : ℕ) : K⟦X⟧) * E K l e ^ j * ((e : K⟦X⟧) * X ^ e) * G := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem EN_xiExt (D : BKDat O K l e a ι η H) (w : Vec K a ι) :
    D.EN (D.xiExt w) = D.xiExt (fun τ i => E K l e * N K (w τ i)) := by
  rw [PhiMod.EN_apply, PhiMod.conn_xiExt]
  exact (D.xiExt_smul_tot (fun _ => E K l e) _).symm

theorem N_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : N K f ∈ Rpi O K l e :=
  N_mem (derivative_mem_R l hf)

theorem C_mem_Rpi (c : K) : C c ∈ Rpi O K l e := HasK.C_mem c

theorem cast_ne (j : ℕ) : (((j + 1) * e * l : ℕ) : K) ≠ 0 :=
  natCast_ne_zero' l (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero j) (NeZero.ne e))
    (Fact.out : l.Prime).ne_zero)

theorem C_inv_mul (j : ℕ) : C ((((j + 1) * e * l : ℕ) : K))⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = 1 := by
  have h : (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = C ((((j + 1) * e * l : ℕ) : K)) := by
    rw [map_natCast]; push_cast; ring
  rw [h, ← map_mul, inv_mul_cancel₀ (cast_ne j), map_one]

theorem neg_step (D : BKDat O K l e a ι η H) (p : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, E K l e ^ (p + 1) * D.xiExt.symm v τ i ∈ Rpi O K l e) (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧
      ∀ τ i, E K l e ^ p * D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  set c : K := (((p + 1) * e * l : ℕ) : K) with hc
  refine ⟨v - c⁻¹ • D.EN v, ?_, ?_, fun τ i => ?_⟩
  · rw [sub_sub_cancel]; exact D.Man.smul_mem _ hN
  · rw [map_sub, map_smul]; exact sub_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · obtain ⟨w, rfl⟩ := D.xiExt.surjective v
    have hco : D.xiExt.symm (D.xiExt w - c⁻¹ • D.EN (D.xiExt w)) τ i =
        w τ i - C c⁻¹ * (E K l e * N K (w τ i)) := by
      rw [EN_xiExt, ← map_smul, ← map_sub, LinearEquiv.symm_apply_apply]
      simp [smul_eq_C_mul]
    rw [hco]
    have hF := hv τ i
    rw [LinearEquiv.symm_apply_apply] at hF
    have h2 := pow_mul_EN (l := l) (e := e) (p + 1) (w τ i)
    have h1 := C_inv_mul (K := K) (l := l) (e := e) p
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    have key : E K l e * (E K l e ^ p * (w τ i - C c⁻¹ * (E K l e * N K (w τ i)))) =
        E K l e * (C c⁻¹ * (((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i) -
          N K (E K l e ^ (p + 1) * w τ i))) := by
      rw [← mul_assoc, ← pow_succ']
      linear_combination (-C c⁻¹) * h2 + (C c⁻¹ * ((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i)) * hX + (-(E K l e ^ (p + 1) * w τ i)) * h1
    rw [mul_left_cancel₀ E_ne_zero key]
    exact mul_mem (C_mem_Rpi _) (sub_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hF)
      (N_mem_Rpi hF))

theorem neg_all (D : BKDat O K l e a ι η H) (p : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, E K l e ^ p * D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ ∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  induction p with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, fun τ i => by simpa using hv τ i⟩
  | succ p ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3⟩ := neg_step D p v hv hN
    obtain ⟨v₂, h4, h5, h6⟩ := ih v₁ h3 h2
    refine ⟨v₂, ?_, h5, h6⟩
    have := add_mem h1 h4
    rwa [sub_add_sub_cancel] at this

theorem pos_step (D : BKDat O K l e a ι η H) (j : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e)
    (hG : ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v τ i) = E K l e ^ j * G)
    (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ (j + 1) * G := by
  set c : K := (((j + 1) * e * l : ℕ) : K) with hc
  obtain ⟨w, rfl⟩ := D.xiExt.surjective v
  simp only [LinearEquiv.symm_apply_apply] at hv hG
  have hco : ∀ τ i, D.xiExt.symm (D.xiExt w + c⁻¹ • D.EN (D.xiExt w)) τ i =
      w τ i + c⁻¹ • (E K l e * N K (w τ i)) := fun τ i => by
    rw [EN_xiExt, ← map_smul, ← map_add, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨D.xiExt w + c⁻¹ • D.EN (D.xiExt w), ?_, ?_, fun τ i => ?_, fun τ i => ?_⟩
  · rw [sub_add_cancel_left]; exact neg_mem (D.Man.smul_mem _ hN)
  · rw [map_add, map_smul]; exact add_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · rw [hco, smul_eq_C_mul]
    exact add_mem (hv τ i) (mul_mem (C_mem_Rpi _) (mul_mem (E_mem l e _) (N_mem_Rpi (hv τ i))))
  · obtain ⟨G, hGm, hGe⟩ := hG τ i
    rw [hco]
    refine ⟨C c⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * G + N K G), mul_mem (C_mem_Rpi _)
      (add_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hGm) (N_mem_Rpi hGm)), ?_⟩
    have h3 := N_pow_mul (l := l) (e := e) j G
    have h1 := C_inv_mul (K := K) (l := l) (e := e) j
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    rw [map_add, Derivation.map_smul, hGe, ← mul_assoc, ← pow_succ', h3, smul_eq_C_mul]
    linear_combination (C c⁻¹ * ((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * E K l e ^ j * G) * hX +
      (-(E K l e ^ j * G)) * h1

theorem pos_all (D : BKDat O K l e a ι η H) (j : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ j * G := by
  induction j with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, hv, fun τ i => ⟨_, N_mem_Rpi (hv τ i), by simp⟩⟩
  | succ j ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3, h4⟩ := ih v hv hN
    obtain ⟨v₂, h5, h6, h7, h8⟩ := pos_step D j v₁ h3 h4 h2
    refine ⟨v₂, ?_, h6, h7, h8⟩
    have := add_mem h1 h5
    rwa [sub_add_sub_cancel] at this

theorem one_div_lt : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact one_div_lt_one_div_of_lt he (by nlinarith)

theorem init (D : BKDat O K l e a ι η H) (n : ℕ) (v : Vec K a ι) (hv : v ∈ divE l e n D.Man) :
    ∀ τ i, E K l e ^ (n + H) * D.xiExt.symm v τ i ∈ Rpi O K l e := by
  have h1 : E K l e ^ (n + H) • v ∈ D.ext (Rpi O K l e) := by
    rw [add_comm, pow_add, mul_smul]
    exact D.smul_mem_ext_of_basis (fun i => D.lower _ (D.bas_mem_M i)) (A_le_Rpi l e) (D.mem_Man.1 hv)
  have h2 := (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt
    (E K l e ^ (n + H) • D.xiExt.symm v)).1 (by
      have := D.xiExt_smul_tot (fun _ => E K l e ^ (n + H)) (D.xiExt.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ h1)
  exact fun τ i => mem_tot.1 h2 τ i

theorem fin (D : BKDat O K l e a ι η H) (r : Vec K a ι) (hr : ∀ τ i, r τ i ∈ Rpi O K l e) :
    E K l e ^ η • D.xiExt r ∈ D.Man :=
  D.mem_Man.2 (D.smul_mem_Mext (A_le_Rpi l e)
    ((GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt r).2 (mem_tot.2 fun τ i => hr τ i)))

theorem taylor (f : K⟦X⟧) (hf : f ∈ Rpi O K l e) (B : ℕ) :
    ∃ g ∈ invL l (A O K), ∃ r ∈ Rpi O K l e, f - g = E K l e ^ B * r := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (idE O K l e) B (toHat O K l e ⟨f, hf⟩))
  obtain ⟨r, hr, h⟩ := (evalₐ_toHat_eq_iff l e B ⟨f, hf⟩ g).1 hg.symm
  exact ⟨g, g.2, r, hr, h⟩

theorem eulerDerivation_eisensteinPow_final_bound {f g r G : K⟦X⟧} (m B : ℕ) (hB : m + 1 ≤ B) (hg : g ∈ invL l (A O K))
    (hr : r ∈ Rpi O K l e) (hG : G ∈ Rpi O K l e) (hf : N K f = E K l e ^ m * G)
    (hfg : f - g = E K l e ^ B * r) :
    ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K g = E K l e ^ m * h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  have hX := X_pow_eq (K := K) (l := l) (e := e)
  set h' := G - (E K l e ^ (d + 1) * N K r +
    ((m + d + 1 : ℕ) : K⟦X⟧) * E K l e ^ d * ((e : K⟦X⟧) * X ^ e) * r) with hh'
  have hgf : g = f - E K l e ^ (m + d + 1) * r := by rw [show m + d + 1 = m + 1 + d by omega, ← hfg]; ring
  have hN : N K g = E K l e ^ m * h' := by
    rw [hgf, map_sub, hf, N_pow_mul, hh']
    ring
  have hh'R : h' ∈ Rpi O K l e := sub_mem hG (add_mem (mul_mem (pow_mem (E_mem l e _) _) (N_mem_Rpi hr))
    (mul_mem (mul_mem (mul_mem (natCast_mem _ _) (pow_mem (E_mem l e _) _))
      (mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _))) hr))
  obtain ⟨k, hk⟩ : N K g ∈ invL l (A O K) := N_mem (derivative_mem_away _ (fun _ => derivative_mem_A) hg)
  have hk' : (l : K⟦X⟧) ^ k * N K g ∈ A O K := by simpa using hk
  refine ⟨(l : K⟦X⟧) ^ k * h', mem_A_of_E_pow_mul_mem l e m
    (mul_mem (pow_mem (natCast_mem _ _) _) hh'R) ?_, k, ?_⟩
  · rw [hN] at hk'; convert hk' using 1; ring
  · rw [hN]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D n v hv hN m
  obtain ⟨v₁, h1, h2, h3⟩ := neg_all D (n + H) v (init D n v hv) hN
  obtain ⟨v₂, h4, -, h6, h7⟩ := pos_all D m v₁ h3 h2
  choose G hGm hGe using h7
  choose g hg r hr hfg using fun (τ : ZMod a) (i : ι) => taylor (D.xiExt.symm v₂ τ i) (h6 τ i) (m + 1 + η)
  refine ⟨g, mem_tot.2 fun τ i => hg τ i, ?_, fun τ i =>
    eulerDerivation_eisensteinPow_final_bound m (m + 1 + η) (by omega) (hg τ i) (hr τ i) (hGm τ i) (hGe τ i) (hfg τ i)⟩
  have e0 : D.xiExt.symm v₂ - g = (fun _ : ZMod a => E K l e ^ (m + 1 + η)) • r :=
    funext fun τ => funext fun i => by simpa using hfg τ i
  have e1 : v₂ - D.xiExt g = E K l e ^ (m + 1) • (E K l e ^ η • D.xiExt r) := by
    rw [smul_smul, ← pow_add]
    have := D.xiExt_smul_tot (fun _ : ZMod a => E K l e ^ (m + 1 + η)) r
    rw [← e0, map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : v - D.xiExt g = (v - v₁) + (v₁ - v₂) + (v₂ - D.xiExt g) := by abel
  rw [e2, e1]
  exact add_mem (add_mem h1 h4) (D.smul_mem_Man (pow_mem (E_mem l e _) _) (fin D r hr))

end GlobalTheory.HorizPole
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  atlas_forward_decl GlobalTheory.HorizPole.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiPole

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) :=
  GlobalTheory.MemLoc.ULaws.iota_aB C w

private theorem aB_alg (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) w) = Per.aB l w :=
  GlobalTheory.MemLoc.ULaws.iota_injective C (by rw [C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris, ι_aB])

private theorem toB_tmul (C : GlobalTheory.MemLoc.Core l) {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O)
    (w : Per.Ainf l) : toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w :=
  congrArg (fun y : Per.Bcris l => (o ⊗ₜ[ℤ_[l]] y : OB l O)) (aB_alg C w)

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem smul_TWincl_mem_filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {n : ℤ} {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l n) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ filT C T n := by
  unfold filT
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul C o w, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add, mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add, smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.XiPole

open GlobalTheory.BKGal.XiPole in

theorem GlobalTheory.BKGal.XiPole.jB_single_mem_filT : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R C i

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩

  obtain ⟨-, -, -, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε _ hEps hδl
  obtain ⟨z, hz⟩ := hK4 (inclL t ϖ D.toPhiMod (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
  rw [← inclL_smul_coord] at hz
  have hB := R.cmp _ z hz
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η) with hm
  have e1 : (fun j => toB l O (m * (Pi.single i (1 : OA l O) : ι → OA l O) j)) = toB l O m • (Pi.single i (1 : OB l O)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e1, map_smul] at hB
  have htm : toB l O m = (1 : O) ⊗ₜ[ℤ_[l]] Per.aB l (muOf ε ^ η) := toB_tmul C _ _

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [← aB_alg C]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  set d : Per.Bcris l := ((hμu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ η with hd
  have hdm : d * Per.aB l (muOf ε ^ η) = 1 := by
    rw [hd, map_pow, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  clear_value d
  have hjB : R.jB (Pi.single i 1) = ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z := by
    rw [← hB, smul_smul, htm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdm,
      ← Algebra.TensorProduct.one_def, one_smul]

  have hν : IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (GlobalTheory.MemLoc.TiedUnif.theta_piOne hE)
  obtain ⟨v', hv'⟩ := hν.exists_right_inv
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hUval : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hιμ : C.ι (Per.aB l (muOf ε)) = (U : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) := by
    rw [ι_aB, hUval, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ (GlobalTheory.MemLoc.TiedUnif.mu_eq ε))
  have h1 : C.ι d * (C.ι (Per.aB l (muOf ε))) ^ η = 1 := by
    rw [← map_pow, ← map_mul, ← map_pow, hdm, map_one]
  rw [hιμ] at h1
  have hpq : ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η = 1 := by
    rw [show ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) =
      ((U : Per.BdR l) * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε) * v') by
      rw [map_mul]; ring, Units.mul_inv, hv', map_one, one_mul, one_pow]
  have hU : ((U ^ (-(η : ℤ)) : (Per.BdR l)ˣ) : Per.BdR l) = ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ η := by
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hdF : C.ι d ∈ Per.FilD l (-(η : ℤ)) := by
    refine (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE _ _).2 ⟨v' ^ η, ?_⟩
    rw [← hUdef, hU, map_pow]
    calc C.ι d = C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η := by
          rw [hpq, mul_one]
      _ = (C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε))) ^ η) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v') ^ η := by
          rw [mul_pow _ _ η, mul_assoc]
      _ = _ := by rw [h1, one_mul, mul_pow]
  rw [hjB]
  exact smul_TWincl_mem_filT C T hdF z
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jB_single_mem_filT' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  atlas_forward_decl GlobalTheory.BKGal.XiPole.jB_single_mem_filT
end

section
section
section
open scoped Formalism.Per

namespace Bridge.FilZeroMul

theorem mul_mem_div_self {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (N : Submodule R A) {x y : A} (hx : x ∈ N / N) (hy : y ∈ N / N) : x * y ∈ N / N := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx hy ⊢
  intro z hz
  rw [mul_assoc]
  exact hx _ (hy z hz)

theorem mul_mem_filD_zero (l : ℕ) [Fact l.Prime] {x y : Formalism.Per.BdR l}
    (hx : x ∈ Formalism.Per.FilD l 0) (hy : y ∈ Formalism.Per.FilD l 0) : x * y ∈ Formalism.Per.FilD l 0 :=
  mul_mem_div_self (Reformulated.AutPerF.BdR.filNat l (Formalism.Per.OC l) 0) hx hy

end Bridge.FilZeroMul

theorem Bridge.mul_mem_filtration_zero : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O : Type} [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) {x y : GlobalTheory.BKReal.OB l O}, x ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → x * y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 := by
  intro l _ O _ _ C x y hx hy
  unfold GlobalTheory.BKGal.XiFil.filO at hx hy ⊢
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨a * b, ?_, ?_⟩
  · rw [map_mul]
    exact Bridge.FilZeroMul.mul_mem_filD_zero l ha hb
  · simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil.ImageFil

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem mul_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x y : OB l O} (hx : x ∈ filO O C 0)
    (hy : y ∈ filO O C 0) : x * y ∈ filO O C 0 := by
  first | exact Bridge.mul_mem_filtration_zero | exact Bridge.mul_mem_filtration_zero .. | (intros; apply Bridge.mul_mem_filtration_zero <;> assumption)

theorem toOB_mem_filO (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul o w =>
    have h : toOB l O (o ⊗ₜ w) = o • ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [h]
    refine Submodule.smul_mem _ o (Submodule.subset_span ⟨acrisToBcris l w, ?_, rfl⟩)
    rw [mem_FilD_zero_iff]
    exact ⟨C.j w, C.ι_j w⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem pow_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x : OB l O} (hx : x ∈ filO O C 0) (n : ℕ) :
    x ^ n ∈ filO O C 0 := by
  induction n with
  | zero =>
    rw [pow_zero, ← map_one (toOB l O)]
    exact toOB_mem_filO C 1
  | succ n ih => rw [pow_succ]; exact mul_mem_filO_zero C ih hx

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  simpa using (GlobalTheory.RingBasics.isUnit_l (l := l)).map (algebraMap (Per.AinfP l) (Per.BdRp l))

theorem exists_inv_l_mem (C : GlobalTheory.MemLoc.Core l) : ∃ r ∈ filO O C 0, r * (l : OB l O) = 1 := by
  obtain ⟨β, hβ⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_left_inv
  obtain ⟨z, hz⟩ := (isUnit_l_BdRp (l := l)).exists_left_inv
  refine ⟨(1 : O) ⊗ₜ β, Submodule.subset_span ⟨β, ?_, rfl⟩, ?_⟩
  · rw [mem_FilD_zero_iff]
    refine ⟨z, ?_⟩
    have h1 : C.ι β * ((l : ℕ) : Per.BdR l) = 1 := by rw [← map_natCast C.ι, ← map_mul, hβ, map_one]
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) z * ((l : ℕ) : Per.BdR l) = 1 := by
      rw [← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_mul, hz, map_one]
    calc C.ι β = C.ι β * (((l : ℕ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) z) := by
          rw [mul_comm ((l : ℕ) : Per.BdR l), h2, mul_one]
      _ = algebraMap (Per.BdRp l) (Per.BdR l) z := by rw [← mul_assoc, h1, one_mul]
  · rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : Per.Bcris l) from
      (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hβ]
    rfl

variable {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem iSl_mem_filO (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (p : invL l (S O K e)) :
    ϖ.iSl O K p ∈ filO O C 0 := by
  obtain ⟨f, n, hf⟩ := p
  have h1 : (l : invL l (S O K e)) ^ n * ⟨f, n, hf⟩ = ⟨_, le_away _ _ hf⟩ := Subtype.ext (by simp)
  have h2 := congrArg (ϖ.iSl O K) h1
  rw [map_mul, map_pow, map_natCast, ϖ.iSl_of_mem O K hf] at h2
  obtain ⟨r, hr, hrl⟩ := exists_inv_l_mem (O := O) C
  have h3 : ϖ.iSl O K ⟨f, n, hf⟩ = r ^ n * toOB l O (ϖ.iS O K ⟨_, hf⟩) := by
    rw [← h2, ← mul_assoc, ← mul_pow, hrl, one_pow, one_mul]
  rw [h3]
  exact mul_mem_filO_zero C (pow_mem_filO_zero C hr n) (toOB_mem_filO C _)

end GlobalTheory.BKGal.XiFil.ImageFil

namespace GlobalTheory.BKGal.XiFil

open GlobalTheory.BKGal.XiFil.ImageFil in

theorem iB_mem_filO_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)), ϖ.iB t K f ∈ filO O C 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ C f
  rw [PiSys.iB, glue_apply]
  refine Submodule.sum_mem _ fun τ _ => mul_mem_filO_zero C ?_ (iSl_mem_filO K ϖ C (f τ))
  rw [idem, constB, AlgHom.comp_apply]
  exact toOB_mem_filO C _

end GlobalTheory.BKGal.XiFil
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_lattice_filtration_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)), ϖ.iB t K f ∈ filO O C 0 := by
  atlas_forward_decl GlobalTheory.BKGal.XiFil.iB_mem_filO_zero
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]
  simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add, map_add]; exact add_mem (h i) (h' i)
  | smul o w _ h =>
    rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1
  rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O), (∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) → toOB l O x ∈ filO O C m := by
  atlas_forward_decl GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K → (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  atlas_forward_decl GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

namespace GlobalTheory.BKGal.TaylorFil

theorem dpowFil : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ), C.j (dpow x hx n) ∈ Per.FilP l n := by
  intro l _ C x hx n
  have hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x :=
    (congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans
      ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans
        (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))
  have h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]
    simp
  have h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k := by
    intro k
    induction k with
    | zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1
    | succ k ih =>
      rw [pow_succ]
      have := (GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)
      simpa using this
  have h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n := by
    have h4 := congrArg C.j (factorial_mul_dpow x hx n)
    rw [map_mul, map_natCast, map_pow, hj] at h4
    rw [mul_comm, h4, ← alg_mem_FilD_iff, map_pow]
    exact h2 n
  have hu : IsUnit (n.factorial : Per.BdRp l) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h5 := Ideal.mul_mem_right v _ h3
  rwa [mul_assoc, hv, mul_one] at h5

end GlobalTheory.BKGal.TaylorFil

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem pow_mem_filO {C : GlobalTheory.MemLoc.Core l} {x : OB l O} (hx : x ∈ filO O C 1) (j : ℕ) :
    x ^ j ∈ filO O C j := by
  induction j with
  | zero => simpa using toOB_mem_filO_zero (O := O) C 1
  | succ j ih => rw [pow_succ]; simpa using mul_mem_filO ih hx

variable (O K) in

theorem iS_E_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) :
    toOB l O (ϖ.iS O K (EIn l e _)) ∈ filO O C 1 := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add, map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  have h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l) := by
    have : EIn l e (S O K e) = uIn _ ^ e + (l : S O K e) := Subtype.ext (by simp [E])
    rw [this, map_add, map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add, map_pow,
      map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm
  have h2 := dpowFil l C _ hE 1
  rw [dpow_one] at h2
  rw [h1]
  simpa using toOB_tmul_mem_filO (O := O) h2

variable (O) in

theorem muDiv_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    toOB l O (ϖ.muDiv a O g i) ∈ filO O C i :=
  toOB_tmul_mem_filO (dpowFil l C _ _ i)

theorem gal_iSl_sub_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (g : ↥(GK (ϖ.field a)))
    (p : invL l (S O K e)) (hp : (p : K⟦X⟧) ∈ invL l (A O K))
    (hN : ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (p : K⟦X⟧) = E K l e ^ m * h) :
    galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p ∈ filO O C m := by
  obtain ⟨h, hh, k, hk⟩ := hN
  obtain ⟨s, hs⟩ := hp
  set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def
  have hp₀A : p₀ ∈ A O K := by simpa [p₀] using hs
  let q : S O K e := ⟨p₀, A_le_S l e hp₀A⟩
  have hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩ := Subtype.ext (by simp [p₀])
  have hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q) := by
    rw [← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]
  set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef
  have hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D := by
    have h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p) := by
      rw [map_mul, map_pow, map_natCast]
    rw [mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]
  refine mem_filO_of_pow_mul (s := s) ?_
  rw [hD]
  refine mem_filO_of_pow_mul (s := k) ?_
  have hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D) := by
    rw [map_mul, map_pow, map_natCast]
  rw [hk']
  have hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h' := by
    intro i hi
    obtain ⟨h', hh', he⟩ := GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow l e O K (p : K⟦X⟧) h k m hh hk i hi
    refine ⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩
    have h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p := by
      have h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s) := by simp
      rw [hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    rw [h4, mul_left_comm, he]
    ring
  refine GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_
  obtain ⟨M₀, hM⟩ := ϖ.taylor_S a O K g q r
  obtain ⟨w, hw⟩ := hM (max M₀ 1) (le_max_left _ _)
  have hM1 : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
      ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
        ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]
    congr 1
    rw [PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]
    congr 1
    exact Subtype.ext (by simp [descN])
  refine ⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
    ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩
  · rw [h0] at hw
    rw [hDdef]
    linear_combination (l : OCr l O) ^ k * hw
  · rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)
    obtain ⟨h', hh', he⟩ := hdesc i hi1
    have h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
        ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩ := by
      rw [← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using he)
    rw [mul_left_comm, h2, map_mul, map_mul, map_pow]
    have h5 := mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i)))
      (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))
    rw [← mul_assoc]
    exact filO_anti (by omega) h5

end Main

theorem gal_iB_sub_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg
  have key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m := fun τ =>
    gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)
  rw [PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ :=
    (galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))
  rw [map_mul, hid, ← mul_sub]
  have h6 := mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)
  rw [zero_add] at h6
  exact h6

end GlobalTheory.BKGal.TaylorFil
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galOB_iB_sub_iB_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  atlas_forward_decl GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.XiDecomp

theorem toBcris_xiExt_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P w hwS hw hd
  have hsum : (⟨P.xiExt w, hw⟩ : P.MMl) = ∑ j, (⟨(fun τ => w τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => hwS τ j) (hd j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt w = _
    rw [Submodule.coe_sum]
    conv_lhs => rw [eq_sum_bas w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => w τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext1 k
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end GlobalTheory.XiDecomp
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  atlas_forward_decl GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in

theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by
    rw [GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine GlobalTheory.T.galOB_iB_sub_iB_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (GlobalTheory.T.jB_single_mem_filT' l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_value_galois_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  atlas_forward_decl GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T), TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) → w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | exact GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | (intros; apply GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  first | exact @GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | exact GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | (intros; apply GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_E_pow_basis_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  first | exact @GlobalTheory.BKGal.HatVal.coord_E_pow_basis | exact GlobalTheory.BKGal.HatVal.coord_E_pow_basis | (intros; apply GlobalTheory.BKGal.HatVal.coord_E_pow_basis <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R σ c hc
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  refine ⟨fun j τ => ⟨E K l e ^ η * σ.1 τ j, mem_tot.1 hσM τ j⟩, fun j τ => rfl, ?_⟩
  set ej : ι → Vec K a ι := fun j _ => Pi.single j 1 with hej
  have hejM : ∀ j, ej j ∈ D.M := fun j => mem_tot.2 fun τ => mem_vecs.2 fun i => by
    simp only [hej]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : ∀ j, E K l e ^ H • ej j ∈ D.L := fun j => D.lower _ (hejM j)
  have hcol : ∀ j τ i, (D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ) i = E K l e ^ H * D.mxInv τ i j := by
    intro j τ i
    simp only [hej, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply]
  have hℓ : ∀ j i τ, E K l e ^ H * D.mxInv τ i j ∈ A O K := fun j i τ => by
    rw [← hcol]; exact D.mem_extc_iff.1 (mem_tot.1 (hL j) τ) i
  set ℓ : ι → ι → ZMod a → A O K := fun j i τ => ⟨_, hℓ j i τ⟩ with hℓdef
  have hcj : ∀ j, c j = fun i => ϖ.iTot t K (ℓ j i) := by
    intro j
    apply inclL_injective t ϖ D.toPhiMod
    rw [hc j]
    have hv : E K l e ^ H • ej j ∈ ME D.toPhiMod := mem_ME_of_mem_L (hL j)
    have h1 := toW_of_mx t ϖ D.toPhiMod ⟨_, hv⟩ (ℓ j) (fun τ => by
      have h2 : (fun i => ((ℓ j i τ : A O K) : K⟦X⟧)) = D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ :=
        funext fun i => (hcol j τ i).symm
      change (E K l e ^ H • ej j) τ = D.mx τ *ᵥ fun i => ((ℓ j i τ : A O K) : K⟦X⟧)
      rw [h2, Matrix.mulVec_mulVec, D.mx_mul_mxInv, Matrix.one_mulVec])
    rw [← inclL_apply] at h1
    rw [← h1]
    ext1 i
    rw [toW_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej i) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) =
          fun τ => ⟨(((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ : K⟦X⟧),
            le_away _ _ (((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ).2⟩ :=
        funext fun τ => Subtype.ext (by simp [hej, EIn])
      rw [h3, ϖ.iW_of_mem t K]
      simp only [map_pow, ϖ.iTot_E t K, Pi.single_eq_same, mul_one]
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej j) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) = 0 :=
        funext fun τ => Subtype.ext (by simp [hej, Pi.single_eq_of_ne h])
      rw [h3, map_zero, Pi.single_eq_of_ne h, mul_zero]
  have hB : ∀ f : ZMod a → A O K, toB l O (ϖ.iTot t K f) =
      ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (A_le_S l e (f τ).2)⟩) := fun f => by
    rw [toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
  have hE : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) =
      toB l O (ϖ.iTot t K (fun _ => EIn l e _)) := by rw [ϖ.iTot_E t K]
  rw [← LinearEquiv.map_smul]
  simp only [← LinearEquiv.map_smul, ← map_sum]
  congr 1
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, toBcris_apply, hE, hcj, hB, ← map_pow, ← map_mul,
    ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
    AddSubmonoidClass.coe_finsetSum, hℓdef]
  change (E K l e) ^ (H + η) * (D.mxInv τ *ᵥ σ.1 τ) i = ∑ j, E K l e ^ η * σ.1 τ j * (E K l e ^ H * D.mxInv τ i j)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  atlas_forward_decl GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

namespace GlobalTheory.BKGal.HatVal

theorem value_mul_E_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hy b₂ hval c hc Y hY
  obtain ⟨m, c', hu, hmc, hmb⟩ := hval
  set E0 : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hE0
  have hEW : ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) = inclO l O E0 := by
    rw [hE0, ← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  have hYi : ∀ i, inclO l O (ϖ.iTot t K (Y i)) = inclO l O E0 ^ η * toW t ϖ D.toPhiMod ⟨y, hy⟩ i := by
    intro i
    rw [← ϖ.iW_of_mem t K, toW_apply, ← hEW, ← map_pow, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp [hY, EIn]
  set S : ι → OA l O := fun i => ∑ j, ϖ.iTot t K (Y j) * c j i with hSdef
  have hS : inclL t ϖ D.toPhiMod S = inclO l O (E0 ^ (H + η)) • toW t ϖ D.toPhiMod ⟨y, hy⟩ := by
    have h1 : S = ∑ j, fun i => ϖ.iTot t K (Y j) * c j i := by
      funext i; simp [hSdef, Finset.sum_apply]
    rw [h1, map_sum]
    simp only [inclL_smul_coord, hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hYi i, pow_add]
    simp only [map_mul, map_pow]
    ring
  have hkey : (fun i => m * S i) = fun i => E0 ^ (H + η) * c' i := by
    apply inclL_injective t ϖ D.toPhiMod
    rw [inclL_smul_coord, inclL_smul_coord, hS, ← hmc, smul_smul, smul_smul, mul_comm]
  have h2 := congrArg (fun v : ι → OA l O => R.jB fun i => toB l O (v i)) hkey
  have hL : (fun i => toB l O (m * S i)) = toB l O m • ∑ j, toB l O (ϖ.iTot t K (Y j)) • fun i => toB l O (c j i) := by
    funext i
    simp [hSdef, Finset.sum_apply, Finset.mul_sum, map_sum]
  have hR : (fun i => toB l O (E0 ^ (H + η) * c' i)) = toB l O E0 ^ (H + η) • fun i => toB l O (c' i) := by
    funext i
    simp
  rw [hL, hR, map_smul, map_smul, ← hmb, map_sum] at h2
  simp only [map_smul] at h2
  rw [smul_smul, mul_comm, ← smul_smul] at h2
  exact (hu.smul_left_cancel).1 h2.symm

end GlobalTheory.BKGal.HatVal
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  atlas_forward_decl GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.BKGal.HatVal

open GlobalTheory.BKGal.HatVal in

theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by
    conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]
    conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_hat_value_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  atlas_forward_decl GlobalTheory.BKGal.value_hat_mem_filZero
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.FilStable.fil_zero_stable | exact GlobalTheory.BKGal.FilStable.fil_zero_stable | (intros; apply GlobalTheory.BKGal.FilStable.fil_zero_stable <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

theorem GlobalTheory.BKGal.sub_sub_xi_mem_Man : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ σ : D.MMl, D.conn σ.1 = D.zeta y → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), σ.1 - y - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ ι _ _ η H D y hyY hMon σ hσ m
  have hyM : E K l e ^ η • y ∈ D.M := mem_divE.1 hyY.1
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  have hv : σ.1 - y ∈ divE l e η D.Man := by
    rw [mem_divE, smul_sub]
    exact sub_mem (D.Mext_mono (invL_S_le_Rpi l e) hσM) (D.M_le_Man hyM)
  have hEN : D.EN (σ.1 - y) ∈ D.Man := by
    have h0 : D.EN y - E K l e • D.zeta y ∈ D.Man := by
      rw [← D.cls_eq_zero_iff, ← D.Mon_apply]; exact hMon
    have h1 : D.EN (σ.1 - y) = -(D.EN y - E K l e • D.zeta y) := by
      rw [map_sub, D.EN_apply σ.1, hσ]; abel
    rw [h1]; exact neg_mem h0
  exact GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole O K l e a ι η H D η _ hv hEN m

theorem GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon hy σ hσinv hconn b₂ hb₂ g hg C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  obtain ⟨m₀, hxi⟩ := GlobalTheory.T.xi_value_galois_sub_mem_filZero l a e O K t ϖ hl2 ι η H D T R
  obtain ⟨w, hw, hr, hN⟩ := GlobalTheory.BKGal.sub_sub_xi_mem_Man l a e O K ι η H D y hyY hMon σ hconn m₀
  have hwM : D.xiExt w ∈ D.MMl :=
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 w).2 (D.Mext_mono (away_mono (A_le_S l e) rfl) hw)
  set ξw : D.MMl := ⟨D.xiExt w, hwM⟩ with hξw
  have hr' : (σ - ξw).1 - y ∈ D.Man := by
    have : (σ - ξw).1 - y = σ.1 - y - D.xiExt w := by
      rw [Submodule.coe_sub, hξw]; abel
    rw [this]; exact hr
  have h3 := GlobalTheory.T.breuilKisin_hat_value_mem_filZero l a e O K t ϖ hl2 ι η H D T R (σ - ξw) y hy hr' b₂ hb₂ C
  have h4 := GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable l O K T g C _ h3
  have h2 := hxi w hw hN hwM g hg C
  have key : R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ = R.jB (toBcris t ϖ D.toPhiMod ξw) +
      (R.jB (toBcris t ϖ D.toPhiMod (σ - ξw)) - b₂) := by
    rw [map_sub, map_sub]; abel
  rw [key, map_add]
  convert add_mem h2 (sub_mem h4 h3) using 1
  abel

end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  atlas_forward_decl GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero
end
