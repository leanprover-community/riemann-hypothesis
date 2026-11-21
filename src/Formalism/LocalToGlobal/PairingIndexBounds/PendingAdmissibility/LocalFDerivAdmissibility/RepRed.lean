import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_subst {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.2 hs
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero hs']
    · simp
    · rw [map_pow, h0 s, zero_pow hs]

theorem cc_expS {ι : Type} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries.constantCoeff (expS p f) = 1 := by
  show expS p f 0 = 1
  simp [expS]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

theorem cc_logX {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]

theorem hasSubst_logX {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)




end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_resV {ι κ R : Type} [Semiring R] (f : κ → ι) (Th : MvPowerSeries ι R) :
    MvPowerSeries.constantCoeff (resV f Th) = MvPowerSeries.constantCoeff Th := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain f 0) Th = _
  rw [Finsupp.mapDomain_zero]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem subst_C_mul' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (c : R)
    (f : MvPowerSeries σ R) : MvPowerSeries.subst a (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul ha, MvPowerSeries.smul_eq_C_mul]

theorem K1gen_C_mul {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1)
    (h : ExtensionGeneratorCondition p K1 R1 be Th) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) := by
  unfold ExtensionGeneratorCondition at h ⊢
  obtain ⟨Ph, U, hTh, hU, h1, h2, h3⟩ := h
  refine ⟨Ph, MvPowerSeries.C c * U, ?_, ?_, h1, h2, h3⟩
  · rw [hTh]
    ring
  · intro n
    have key : inParamK p K1 (MvPowerSeries.C c * U) = MvPowerSeries.C c * inParamK p K1 U := by
      unfold inParamK
      exact subst_C_mul' (hasSubst_logX K1) c U
    rw [key, MvPowerSeries.coeff_C_mul]
    exact R1.mul_mem hc (hU n)

theorem K1gen_C_mul_iff {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1) (hc' : c⁻¹ ∈ R1)
    (hc0 : c ≠ 0) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) ↔ ExtensionGeneratorCondition p K1 R1 be Th := by
  constructor
  · intro h'
    have h2 := K1gen_C_mul hc' h'
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at h2
  · exact K1gen_C_mul hc

theorem adm_two_pendant_iff (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E.toCEmb
    adm2b D X (pendT X E hfin hst hLT pos F) ↔
      ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
        ∀ φ : Frm X j La La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
          (thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La'))) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La'),
      (pendT X E hfin hst hLT pos F).ThA j La La' φ = MvPowerSeries.C (chiN X ℂ_[p] hfin j La) *
        thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
          (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')) := by
    intro j La La' φ
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  constructor
  · intro h j hj La La' hL hL' φ
    have h1 := h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ) at h1
    rw [key] at h1
    refine (K1gen_C_mul_iff ?_ ?_ ?_).1 h1
    · show ‖_‖ ≤ 1; rw [hn]
    · show ‖_‖ ≤ 1; rw [norm_inv, hn, inv_one]
    · intro h0; have := hn j La; rw [h0, norm_zero] at this; exact zero_ne_one this
  · intro h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ)
    rw [key]
    refine K1gen_C_mul ?_ (h j hj La La' hL hL' φ)
    show ‖_‖ ≤ 1; rw [hn]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend
open scoped Kronecker Matrix

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem latAt_smul (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup) (v : X.Pl) :
    X.latAt v j ((X.Lv.lev j c).smul γ L) =
      (X.latAt v j L).map ((Matrix.mulVecLin (gamAt X j c γ v : Matrix _ _ (X.G.P.Qq v))).restrictScalars (X.G.P.W v)) := by
  cases j <;> rfl

theorem map_map_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (A : GL (Fin k) Qq)
    (M : Submodule W (Fin k → Qq)) :
    (M.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = M := by
  rw [← Submodule.map_comp]
  have hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W).comp
      ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp [Matrix.mulVec_mulVec]
  rw [hid, Submodule.map_id]

def frmMove (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') : Frm X j (La.1, L0) La' where
  g := fun v => (gamAt X j La.1 γ v)⁻¹ * φ.g v
  g' := φ.g'
  hg := fun v => by
    have h1 := φ.hg v
    rw [h, latAt_smul] at h1
    show X.latAt v j L0 = _
    rw [Units.val_mul, ← colSpan_mul, ← h1, map_map_inv]
  hg' := φ.hg'

def frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') : Frm X j La La' where
  g := fun v => gamAt X j La.1 γ v * φ0.g v
  g' := φ0.g'
  hg := fun v => by
    have h1 := φ0.hg v
    change X.latAt v j L0 = _ at h1
    rw [h, latAt_smul, h1, colSpan_mul, Units.val_mul]
  hg' := φ0.hg'

theorem frmMove_frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup}
    (γ : (X.Lv.lev j La.1).Γ) (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') :
    frmMove X γ h (frmBack X γ h φ0) = φ0 := by
  cases φ0 with
  | mk g g' hg hg' =>
    unfold frmMove frmBack
    congr 1
    funext v
    exact inv_mul_cancel_left _ _

theorem subst_invF_actS (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (z : X.ZA j) :
    MvPowerSeries.subst (invF Kc φ) (actS X Kc j (gamAt X j La.1 γ) z) = invF Kc (frmMove X γ h φ) z := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  rcases z with ⟨v, s, a, b⟩
  have hQ : Qi Kc (frmMove X γ h φ) v s = Qi Kc φ v s := by
    unfold Qi
    rfl
  have hm : ∀ A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v),
      mAt X Kc j v s (A * B) = mAt X Kc j v s A * mAt X Kc j v s B := by
    intro A B
    unfold mAt
    rw [Matrix.map_mul, Matrix.submatrix_mul_equiv]
  simp only [actS, invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hI, map_sum]
  simp_rw [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hI]
  simp only [invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ab' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rcases ab' with ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, hQ]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  unfold Pi
  try dsimp only [frmMove]
  by_cases ho : IsOddPos s
  · simp only [if_pos ho]
    rw [Units.val_mul, hm, Matrix.mul_apply]
  · simp only [if_neg ho, Matrix.transpose_apply]
    rw [mul_inv_rev, inv_inv, Units.val_mul, hm, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem thA_SA (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (f : MvPowerSeries (X.ZA j) Kc) :
    thA Kc φ (SA X Kc j (gamAt X j La.1 γ) f) = thA Kc (frmMove X γ h φ) f := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  have hA : MvPowerSeries.HasSubst (actS X Kc j (gamAt X j La.1 γ)) := by apply hasSubst_actS
  unfold thA SA
  rw [MvPowerSeries.subst_comp_subst_apply hA hI]
  congr 1
  funext z
  exact subst_invF_actS X Kc γ h φ z

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

def RepresentativeCondition (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) be (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

theorem adm_two_pendant_iff_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm2b D X (pendT X E hfin hst hLT pos F) ↔ RepresentativeCondition X E hfin (beLT hLT) pos F := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  rw [adm_two_pendant_iff]
  constructor
  · intro H
    dsimp only [RepresentativeCondition]
    intro j hj R hR La' hLa' φ
    have hlat : (X.Pj j).IsLatTup R.2 := repOf_lat (Lv := X.Lv) hfin j R hR
    have key := H j hj R La' hlat hLa'
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j R.1 R.2 hlat
    set δ := delt X hfin j R.1 R.2 with hδ
    obtain ⟨L2, _, huniq⟩ := repOf_ex (Lv := X.Lv) hfin j R.1 R.2 hlat
    have e1 : R.2 = L2 := huniq R.2 ⟨hR, 1, by rw [lsmul_one]⟩
    have e2 : L1 = L2 := huniq L1 ⟨hL1, δ, hL1'⟩
    have hS : (X.Lv.lev j R.1).smul δ⁻¹ R.2 = R.2 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul, e2, e1]
    have hh : R.2 = (X.Lv.lev j R.1).smul δ ((X.Lv.lev j R.1).smul δ⁻¹ R.2) := by
      rw [lsmul_lsmul_inv]
    have key2 : ∀ ψ : Frm X j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
        (thA ℂ_[p] ψ (thFOf X pos F j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La')) := by
      intro ψ
      have h := key (frmBack X δ hh ψ)
      rw [thA_SA X ℂ_[p] δ hh] at h
      have hr : frmMove X δ hh (frmBack X δ hh ψ) = ψ := by
        cases ψ
        simp only [frmMove, frmBack, inv_mul_cancel_left]
      rw [hr] at h
      exact h
    rw [hS] at key2
    exact key2 φ
  · intro H j hj La La' hLa hLa' φ
    dsimp only [RepresentativeCondition] at H
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j La.1 La.2 hLa
    set δ := delt X hfin j La.1 La.2 with hδ
    have hS : (X.Lv.lev j La.1).smul δ⁻¹ La.2 = L1 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul]
    have hh : La.2 = (X.Lv.lev j La.1).smul δ ((X.Lv.lev j La.1).smul δ⁻¹ La.2) := by
      rw [lsmul_lsmul_inv]
    rw [thA_SA X ℂ_[p] δ hh φ]
    have hrep : (La.1, (X.Lv.lev j La.1).smul δ⁻¹ La.2) ∈ repOf X.Lv hfin j := by
      rw [hS]
      exact hL1
    exact H j hj _ hrep La' hLa' (frmMove X δ hh φ)

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end
