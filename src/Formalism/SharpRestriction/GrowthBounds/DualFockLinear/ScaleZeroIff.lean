import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRAddRight

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti flat_lam tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem HL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HL (O := O) ι σ (flW d) (colSpan W ℓ) ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d (fun s => la_tw ι σ s.val ℓ) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => extO O ι σ s.val (colSpan W ℓ)) ↔ _
  rw [Hten_flW, tensor_lattice_twist_eq hS m (vecE n') d (fun x => x) ℓ hℓ]
  rfl

theorem HLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HLe p ι σ w (flW d) e ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O d (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => LeAt p ι σ w s.val e) ↔ _
  have := hS.frac_O
  have e1 : (fun x : Fin n' => H0 O m (letterWt m (d x) (vecE n' x)) (LeAt p ι σ w x.val e)) =
      fun s => nablaLTw O Kf m (letterWt m (d s) (vecE n' s))
        (la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  rw [Hten_flW, e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (i : ℤ)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale (algebraMap O Kf w ^ i) (Re p ι σ w r (flW d) e.dual)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW d) e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun s => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun s : Fin n' => la_tw ι σ s.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun s => ((la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun s => dualM hS s.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale c (HL (O := O) ι σ (flW d) (colSpan W ((ℓ⁻¹).transpose)))) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale c (dualLat O Kf (HL (O := O) ι σ (flW d) (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val ℓ) (fun s => la_tw_det _ _ _ _ hℓ) u y0
    ((HL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun s : Fin n' => la_tw ι σ s.val ((ℓ⁻¹).transpose)) = fun s => ((la_tw ι σ s.val ℓ)⁻¹).transpose :=
    funext fun s => la_tw_invT s.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul map_Pol mem_Pol
  dE invT_mul_D w_ne p_eq pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

theorem Aa_dual2 {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  have hMt : IsUnit ((M⁻¹).transpose).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]; exact hM.ringInverse
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hMt, Matrix.transpose_one]
  · simp only [Aa, if_true]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem subst_Lin (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (r : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) d) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    map (kapR hS) (subst p n' O w n' r g F) = (algebraMap O Kf w ^ Avec (vecE n') d) •
      Lin (fun x => Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x))
        (Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have hF' := (pol_iff hS _ _ _).1 hF
  have h1 : map (kapR hS) (subst p n' O w n' r g F) =
      Lin (Bm ι σ w φ r (vecE n') (fun x => x) g) (map (kapR hS) F) :=
    lift_eq hS φ hφ r (LLT n') (fun x => x) (fun _ => rfl) g hg F
  have hB : Bm ι σ w φ r (vecE n') (fun x => x) g = fun x => (if vecE n' x then algebraMap O Kf w else 1) •
      (Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹ * Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (vecE n') (fun x => x) hmat hh g hg x
  rw [h1, hB, Lin_smul _ _ _ hF', Lin_comp]
  congr 1
  unfold Avec
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro x _
  split_ifs <;> simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem pair_formula (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) (κ : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (hgv : IsGLW gv)
    (hb : IsUnit (hmat * ((matQ φ g)⁻¹).transpose).det)
    (hrel : ((matQ φ gv)⁻¹).transpose =
      ((hmat * ((matQ φ g)⁻¹).transpose)⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq))
    (Θ Θv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hmat Θ) (hΘv : IsTrueTheta hS d (flW d) (vecE n') 1 Θv)
    (F Fv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)))
        (subst p n' O w n' r gv (Fv : MvPolynomial (TV n' (m + 1)) (KK O))) /
          (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  let P : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F.1),
      Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)⟩
  let Q : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))⁻¹)
      (map (kapR hS) Fv.1), Lin_Pol _ _ ((pol_iff hS _ _ _).1 Fv.2)⟩
  have eF : Θ F = thK P := Subtype.ext (by rw [hΘ F, hthK]; rfl)
  have eFv : Θv Fv = thK Q := Subtype.ext (by rw [hΘv Fv, hthK]; rfl)
  have hdual : ∀ s : Fin n', Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) 1 gv s) *
      (Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) hmat g s)).transpose = 1 := by
    intro s
    have e1 : Mx ι σ w φ r (fun x => x) 1 gv s = ((Mx ι σ w φ r (fun x => x) hmat g s)⁻¹).transpose := by
      unfold Mx
      rw [Matrix.one_mul, hrel]
      exact dualM hS s.val r _ hb
    rw [e1]
    exact Aa_dual2 _ _ (Mx_det (w_ne hS) φ r (fun x => x) hmat hh g hg s)
  have hL : be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      (p : Kf) ^ Ar r (flW (m := m) d) * (((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
        fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) := by
    unfold be
    rw [eF, eFv, map_smul, smul_eq_mul, TY_apply]
  rw [hL, map_div₀, map_mul, map_pow, map_natCast, map_natCast, fock_eq_fockR, ← fockR_map,
    subst_Lin hS φ hφ r hmat hh g hg F.1 F.2, subst_Lin hS φ hφ r 1 h1d gv hgv Fv.1 Fv.2, tsact_smul_left,
    tsact_smul_right, fockR_Lin_dual _ _ hdual, flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d), zpow_natCast,
    p_eq hS]
  show _ = _ * (_ * (_ * fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf))) / _
  ring

theorem exists_gv (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) {k : ℕ} (X : Matrix (Fin k) (Fin k) Qq)
    (h : colSpan W X = colSpan W (1 : Matrix (Fin k) (Fin k) Qq)) :
    ∃ gv : Matrix (Fin k) (Fin k) (WF p n'), IsGLW gv ∧ matQ φ gv = X := by
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have h1 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => X i c) =
      (1 : Matrix (Fin k) (Fin k) Qq).mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [← h]
    exact Submodule.subset_span ⟨c, rfl⟩
  have h2 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) =
      X.mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [h]
    exact Submodule.subset_span ⟨c, rfl⟩
  choose Y hY using h1
  choose Y' hY' using h2
  let Cm : Matrix (Fin k) (Fin k) W := fun i c => Y c i
  let Cm' : Matrix (Fin k) (Fin k) W := fun i c => Y' c i
  have hX : X = Cm.map (algebraMap W Qq) := by
    ext i c
    have := congrFun (hY c) i
    rw [Matrix.one_mulVec] at this
    exact this
  have hprod : Cm * Cm' = 1 := by
    apply Matrix.map_injective hinj
    show (Cm * Cm').map (algebraMap W Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq)
    rw [Matrix.map_mul, ← hX, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i c
    have := congrFun (hY' c) i
    rw [Matrix.mul_apply]
    exact this.symm
  have hdet : IsUnit Cm.det := by
    have : Cm.det * Cm'.det = 1 := by rw [← Matrix.det_mul, hprod, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  refine ⟨(φ.symm : W →+* WF p n').mapMatrix Cm, ?_, ?_⟩
  · unfold IsGLW
    rw [← RingHom.map_det]
    exact hdet.map _
  · rw [hX]
    ext a c
    simp [matQ, RingHom.mapMatrix_apply, Matrix.map_apply]

end

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_Pol dE invT_mul_D dual_edgeBasis dual_edge edgeBasis latDual_colSpan w_ne p_eq pQ_ne
  kapR kapR_alg pol_iff inWj_iff pol_of_map)
open Formalism.L2.G.Model.TS

theorem scale_zero_iff {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] (c : Kf) (M : Submodule O X) (x : X) : x ∈ scale (c ^ (0 : ℤ)) M ↔ x ∈ M := by
  rw [mem_scale]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x, h, by simp⟩

section

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

set_option maxHeartbeats 1600000 in

theorem realAt_gen (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hm1 : 1 ≤ m) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1) (d : Fin n' → ℕ) (cP κ : ℕ)
    (hMD : MultDiv O p κ (k := m + 1) d)
    (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e)
    (htgt : e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))
    (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
    (hhm : IsUnit hm.det) (hg : IsGLW g) (hbasis : IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hm Θ) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∃ gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW gv ∧
    ∀ (o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O)), HasMultideg sig d → InWj w sig 0 →
      Realisable p n' w n' r gv cP o sig →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) d)),
        T ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW d) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW d) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW d) e')) ∧
        ∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
          Θ F ∈ Re p ι σ w r (flW d) e →
          ∃ z : O, be p r (flW d) (Θ F) T =
            kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) sig /
              (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) + algebraMap O Kf (w ^ cP * z) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  have h1T : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)⁻¹).transpose = 1 := by simp
  set b := hm * ((matQ φ g)⁻¹).transpose with hbdef
  have htg : e.tgt = colSpan W (b * lb_D (m + 1) r ((p : ℕ) : Qq)) := hbasis.2.2
  obtain ⟨gv, hgv, hgvX⟩ := exists_gv hS φ (b * lb_D (m + 1) r ((p : ℕ) : Qq)) (by rw [← htg, htgt])
  have hrel : ((matQ φ gv)⁻¹).transpose = (b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq) := by
    rw [hgvX]
    exact invT_mul_D b hbasis.1 r _ (pQ_ne hS)
  have hbv : IsEdgeBasis p r e.dual (1 * ((matQ φ gv)⁻¹).transpose) := by
    rw [Matrix.one_mul, hrel]
    exact dual_edgeBasis p r (pQ_ne hS) e b hbasis
  obtain ⟨Θv, ⟨hv1, hv2⟩, hv3⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) 1 h1d
  obtain ⟨Θ', ⟨_, h2'⟩, h3'⟩ := theta_exists p n' W Qq O Kf ι σ j w hS φ hφ m r (vecE n') d (flW d) hr1 hr2
    (isFlat_flW d) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun F => Subtype.ext ((hΘ F).trans (h3' F).symm)
  subst hΘeq
  obtain ⟨thK, hthK⟩ := exists_thK Kf hm1 d
  obtain ⟨hE1, _, hE3⟩ := edgePlane p n' W Qq O Kf ι σ j w hS φ hφ m r 1 h1d
  refine ⟨gv, hgv, ?_⟩
  intro o sig hmd hint hreal
  obtain ⟨Ff, hA, hmdF, hsym, hoth⟩ := hreal
  let F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) := ⟨Ff, hmdF d hmd⟩
  set cc : Kf := (p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) with hcc
  refine ⟨TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F'), ?_, ?_, ?_, ?_⟩
  · rw [htgt]
    apply FD_HL thK hS hm1 hthK κ hMD 1 h1d
    rw [h1T]
    exact mem_scale.2 ⟨Θv F', (hv1 F').1 hA, rfl⟩
  · rw [← scale_zero_iff (algebraMap O Kf w)]
    apply FD_edge thK hS hm1 hthK κ hMD r e b hbasis
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) gv
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + 0) := by
      intro mm
      obtain ⟨c1, hc1⟩ := hsym mm
      obtain ⟨c2, hc2⟩ := hint mm
      refine ⟨c2 + w ^ cP * c1, ?_⟩
      have e1 : coeff mm (subst p n' O w n' r gv Ff) =
          coeff mm (subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig) +
            algebraMap O (KK O) (w ^ o) * coeff mm sig := by
        rw [coeff_sub, coeff_C_mul]
        ring
      show coeff mm (subst p n' O w n' r gv Ff) = _
      rw [e1, hc1, hc2, ← map_mul, ← map_add]
      congr 1
      ring
    have h2 := (hv2 gv hgv e.dual hbv F' (o + 0)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o 0 _ h2
  · intro e' he' htg' hne
    obtain ⟨b', hb'⟩ := edgeBasis hS m r e' he'
    apply FD_edge thK hS hm1 hthK κ hMD r e' b' hb'
    have hd' := dual_edge hS m r e' he'
    have hd := dual_edge hS m r e he
    have hsrc : e'.dual.src = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) := by
      show latDual e'.tgt = _
      rw [htg', htgt, latDual_colSpan _ h1d, h1T]
    obtain ⟨g', hg', hbg'⟩ := hE1 e'.dual hd'.1 hsrc
    have hpl : ratPlane p n' r g' ≠ ratPlane p n' r gv := by
      intro hEq
      have h5 : e'.dual = e.dual := (hE3 g' gv e'.dual e.dual hg' hgv hbg' hbv).2 hEq
      apply hne
      rw [← hd'.2, h5, hd.2]
    have h1 : InWjRg p n' O w r (flatLetters (vecE n')) g'
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + cP) := hoth g' hg' hpl
    have h2 := (hv2 g' hg' e'.dual hbg' F' (o + cP)).1 h1
    exact scale_shift (algebraMap O Kf w) hw o cP _ h2
  · intro F hF
    have hpf := pair_formula thK hS φ hφ r hr1 hr2 hthK κ hm hhm g gv hg hgv hbasis.1 hrel Θ Θv hΘ hv3 F F'

    have hF0 : InWjRg p n' O w r (flatLetters (vecE n')) g (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) 0 :=
      (h2' g hg e hbasis F 0).2 (by
        have : ((0 : ℕ) : ℤ) = 0 := rfl
        rw [this, scale_zero_iff]
        exact hF)
    obtain ⟨G0, hG0⟩ := (inWj_iff hS _ 0).1 hF0
    rw [pow_zero, one_smul] at hG0
    have hG0' : map (kapR hS) (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O))) =
        map (algebraMap O Kf) G0 := hG0
    have hG0P : G0 ∈ Pol O (m + 1) d := by
      apply pol_of_map hS
      rw [← hG0', subst_Lin hS φ hφ r hm hhm g hg F.1 F.2]
      exact Submodule.smul_mem _ _ (Lin_Pol _ _ (Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)))
    obtain ⟨E, hE⟩ := (inWj_iff hS _ (o + cP)).1 hsym
    obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD G0 hG0P E
    refine ⟨z, ?_⟩
    set SF := subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)) with hSF
    set Rr := subst p n' O w n' r gv Ff - C (algebraMap O (KK O) (w ^ o)) * sig with hRr
    have e1 : subst p n' O w n' r gv (F' : MvPolynomial (TV n' (m + 1)) (KK O)) =
        algebraMap O (KK O) (w ^ o) • sig + Rr := by
      rw [hRr, smul_eq_C_mul]
      show subst p n' O w n' r gv Ff = _
      ring
    have e2 : be p r (flW d) (Θ F) (TY thK cc ((algebraMap O Kf w ^ (-(o : ℤ))) • Θv F')) =
        algebraMap O Kf w ^ (-(o : ℤ)) * be p r (flW d) (Θ F) (TY thK cc (Θv F')) := by
      simp only [be, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e3 : kapR hS (fock SF Rr) = algebraMap O Kf w ^ (o + cP) *
        fockR (map (algebraMap O Kf) G0) (map (algebraMap O Kf) E) := by
      rw [fock_eq_fockR, ← fockR_map, hG0', hE, tsact_smul_right]
    rw [e2, hpf, e1, fock_eq_fockR, fockR_add_right, tsact_smul_right, ← fock_eq_fockR, ← fock_eq_fockR]
    have e4 : kapR hS ((p : KK O) ^ κ * (algebraMap O (KK O) (w ^ o) * fock SF sig + fock SF Rr) /
        (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) =
        algebraMap O Kf w ^ o * kapR hS ((p : KK O) ^ κ * fock SF sig / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf w ^ (o + cP) * algebraMap O Kf z := by
      rw [← hz]
      simp only [map_div₀, map_mul, map_add, map_pow, map_natCast, kapR_alg, e3]
      ring
    rw [e4, zpow_neg, zpow_natCast, map_mul, map_pow, pow_add]
    field_simp

end

theorem realStep (C CLa : ℝ) : RealStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  exact realAt_gen hSet.1 φ hφ (by omega) r (by omega) (by omega) (dT TT lam0) _ _
    (multDiv_kapFl O p (dvrOfStd hSet).p_mem (dT TT lam0)) e he htgt hm g hhm hg hbasis Θ hΘ

theorem restReal (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestReal D CLa Ck Crk Cdeg :=
  fun _ => ⟨1, one_pos, fun C _ => realStep C CLa⟩

theorem restFlat_of_Xi (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 :=
  restFlat_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hXi (restReal D CLa Ck Crk Cdeg)

end Formalism.MainNotions.TestSideCounting
end
end
