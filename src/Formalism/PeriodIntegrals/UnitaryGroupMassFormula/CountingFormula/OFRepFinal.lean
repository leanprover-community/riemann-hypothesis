import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnipotentIntegralPreservesLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichLApply
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalTheoryWindows
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TransMemUnipotentIntegral

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) one_ne_zero hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fixedOK_of_rows (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ what₂) : FixedOK D F0 Λ := by
  obtain ⟨hE, hz, hrr, -⟩ := hR
  obtain ⟨-, ⟨hlat, hunim, -, -⟩, hx⟩ := hrr.1 Λ hΛ
  refine ⟨hlat, hunim, hE, ?_, (D.cOf u)⁻¹, inv_ne_zero (D.cOf_ne u), ?_⟩
  · unfold XLam at hx
    intro a
    have hmem : F0.e a ∈ XS D F0 := by
      unfold XS
      clear hrr hz hunim hlat hΛ what₂ hE hx
      apply Submodule.subset_span
      refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
      unfold ddS
      have hne : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
        Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
      have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
        have := a.isLt
        omega
      rw [hk, zpow_neg, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ hne))]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hx] at hmem
    exact hmem.1
  · rw [hz]
    rfl

theorem orbitReps_of (hN : UnipotentIntegralIsGroup) (hRk : RankG) (hG : GoodEZ) (h1 : Stage1) (h2 : Stage2) (hK : FinK) :
    OrbitReps := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hF := fixedOK_of_rows D u F0 what₂ hR hΛ
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F1, hF1⟩ := hne
    have hGZ : GZ (Tn u) (Tn u') Z ≠ 0 := by
      have h := hF1.1.2.2
      rw [gz_eq, hF1.2.2.2.2] at h
      exact h
    obtain ⟨R, hRm⟩ := hRk D (Tn u) (Tn u') Z hGZ
    obtain ⟨Wf, hWf, hW⟩ := h1 D (Tn u') F0 Λ hF Z R hRm
    obtain ⟨Af, hAf, hAx⟩ := h2 D (Tn u') F0 Λ hF Z R hRm Wf hWf
    refine ⟨{x | Good D (Tn u') F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af},
      hK D (Tn u') F0 Λ hF Z R hRm Wf Af hWf hAf, fun F' hF' => ?_⟩
    have g0 := hG D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n1, hn1, hw1⟩ := hW _ g0
    have g1 := good_move D (Tn u') F0 Λ Z g0 hn1
    obtain ⟨n2, hn2, hw2, ha2⟩ := hAx _ g1 hw1
    have g2 := good_move D (Tn u') F0 Λ Z g1 hn2
    refine ⟨n1.trans n2, (hN D F0 Λ).2.2 n1 hn1 n2 hn2, ?_⟩
    have hact : act D (n1.trans n2) (F'.fl.e, F'.fl.z) = act D n2 (act D n1 (F'.fl.e, F'.fl.z)) := rfl
    show act D (n1.trans n2) (F'.fl.e, F'.fl.z) ∈ _
    rw [hact]
    exact ⟨g2, hw2 ▸ hw1, ha2⟩
  · refine ⟨∅, Set.finite_empty, fun F' hF' => absurd ⟨F', hF'⟩ hne⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_gram : RankG := by
  intro D T T' Z hG
  classical
  by_cases hdet : Z.det = 0
  · have hm : leadMinorE Z D.R.rS ≠ 0 := by
      intro hm
      apply hG
      have h1 : leadMinorE Z (D.R.rS + 1) = 0 := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos le_rfl, Fin.castLE_rfl, Matrix.submatrix_id_id]
        exact hdet
      simp [Formalism.L2.SG.CntLocal.GZ, h1, hm]
    have h : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
    set B := Z.submatrix (Fin.castLE h) (Fin.castLE h) with hB
    have hBdet : B.det ≠ 0 := by
      have e : leadMinorE Z D.R.rS = B.det := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos h]
      rwa [← e]
    refine ⟨Matrix.of fun j i => if hj : (j : ℕ) < D.R.rS then B⁻¹ ⟨j, hj⟩ i else 0, ?_⟩
    have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hBdet)
    ext a i
    rw [← hBB]
    simp only [Matrix.mul_apply, betaZ, Matrix.submatrix_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, not_false_eq_true, dif_neg, mul_zero,
      add_zero, id]
    rfl
  · refine ⟨(Z⁻¹).submatrix id Fin.castSucc, ?_⟩
    have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.2 hdet)
    unfold betaZ
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hZ]
    exact Matrix.submatrix_one_embedding Fin.castSuccEmb

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_int (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {x v : (VS D).V} (hx : x ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT x v := by
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' x hx)
  exact ⟨o, ho⟩

theorem smul_int_mem (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : D.host.E}
    (hk : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = k) {v : (VS D).V} (hv : v ∈ Λ) : k • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  rw [algebraMap_smul]
  exact Λ.smul_mem o hv

theorem eich_conds (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (D.sp.hypE a) = 0 ∧ (VS D).hT (D.sp.hypE a) ((2 : D.host.E) • y0) = 0 ∧
    (VS D).hT ((2 : D.host.E) • y0) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) + (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 ∧
    (-2 * (VS D).hT y0 y0) + star (-2 * (VS D).hT y0 y0) +
      (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 := by
  have hh : star ((VS D).hT y0 y0) = (VS D).hT y0 y0 := (VS D).herm.eq y0 y0
  have h22 : (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 4 * (VS D).hT y0 y0 := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, map_ofNat, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨D.sp.hyp_ee a a, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, hy.1 a, smul_zero]
  · rw [LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a, map_zero, smul_zero]
  · rw [h22]
    ring
  · have hs2 : star (-2 : D.host.E) = -2 := by simp
    rw [h22, star_mul', hs2, hh]
    ring

theorem eich_conds_neg (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (-((2 : D.host.E) • y0)) = 0 ∧
    (VS D).hT (-((2 : D.host.E) • y0)) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) +
      (VS D).hT (-((2 : D.host.E) • y0)) (-((2 : D.host.E) • y0)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_smul, hy.1 a, smul_zero, neg_zero]
  · rw [map_neg, LinearMap.neg_apply, LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a,
      map_zero, smul_zero, neg_zero]
  · rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, LinearMap.map_smulₛₗ₂, map_smul, map_ofNat,
      smul_eq_mul, smul_eq_mul]
    ring

def eichE (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0))
    (eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0))
    (LinearMap.ext fun v => by
      obtain ⟨he, -, -, -, -⟩ := eich_conds D a hy
      obtain ⟨n2, n3, n4⟩ := eich_conds_neg D a hy
      have := eich_inv D he n2 n3 n4 v
      rw [neg_neg] at this
      exact this)
    (LinearMap.ext fun v => by
      obtain ⟨he, h2, h3, h4, -⟩ := eich_conds D a hy
      exact eich_inv D he h2 h3 h4 v)

theorem eichE_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    eichE D a y0 hy v = eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichE_symm_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    (eichE D a y0 hy).symm v = eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichL_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {e y : (VS D).V} {c : D.host.E} (he : e ∈ Λ) (hy : y ∈ Λ)
    (hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c) {v : (VS D).V} (hv : v ∈ Λ) :
    eichL D e y c v ∈ Λ := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  exact Λ.add_mem (Λ.sub_mem (Λ.add_mem hv (smul_int_mem D (unimod_int D hU he hv) hy))
    (smul_int_mem D (unimod_int D hU hy hv) he)) (smul_int_mem D hc (smul_int_mem D (unimod_int D hU he hv) he))

theorem eichE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {y0 : (VS D).V}
    (hy : InW D y0) (hyΛ : y0 ∈ Λ) : eichE D a y0 hy ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hF.2.1
  have hea : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hFe] at h1
  obtain ⟨he, h2, h3, -, h5⟩ := eich_conds D a hy
  have hy2 : (2 : D.host.E) • y0 ∈ Λ := smul_int_mem D (k := (2 : D.host.E)) ⟨2, map_ofNat _ 2⟩ hyΛ
  have hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = -2 * (VS D).hT y0 y0 := by
    obtain ⟨o, ho⟩ := unimod_int D hU hyΛ hyΛ
    exact ⟨-2 * o, by rw [map_mul, ho, map_neg, map_ofNat]⟩
  have hP : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE),
      (∀ b, (VS D).hT (D.sp.hypE b) x = 0) ∧ (VS D).hT y0 x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨fun b => D.sp.hyp_ee b c, by rw [← (VS D).herm.eq (D.sp.hypE c) y0, hy.1 c, map_zero]⟩
    | zero => simp
    | add x z _ _ hx hz => exact ⟨fun b => by rw [map_add, hx.1 b, hz.1 b, add_zero], by
        rw [map_add, hx.2, hz.2, add_zero]⟩
    | smul c x _ hx => exact ⟨fun b => by rw [map_smul, hx.1 b, smul_zero], by
        rw [map_smul, hx.2, smul_zero]⟩
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE), eichE D a y0 hy x = x := by
    intro x hx
    obtain ⟨h1, h2'⟩ := hP x hx
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, h1 a, h2', smul_zero, zero_smul, add_zero, sub_zero]
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  have hy0z : (VS D).hT y0 D.sp.zm = 0 := by
    rw [← (VS D).herm.eq D.sp.zm y0, hy.2.2, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    exact eich_isom D he h2 h3 h5 u v
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => eichL_lat D hU hea hy2 hc hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨(eichE D a y0 hy).symm v, ?_, (eichE D a y0 hy).apply_symm_apply v⟩
      rw [eichE_symm_apply]
      exact eichL_lat D hU hea (Λ.neg_mem hy2) hc hv
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
      rw [← hFe]
      exact Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have hex : (VS D).hT (D.sp.hypE a) x = 0 := by
      have h1 : x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range F0.e)) := hx
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker] at h1
      exact h1 _ (by rw [hFe]; exact Submodule.subset_span ⟨a, rfl⟩)
    show (eichE D a y0 hy) x - x ∈ Submodule.span D.host.E (Set.range F0.e)
    rw [eichE_apply, hFe]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, hex, zero_smul, add_zero, smul_zero, add_sub_cancel_left, zero_sub]
    rw [sub_sub_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [hFe]
    exact hspan _ (Submodule.subset_span ⟨b, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, hzm a, hy0z, smul_zero, zero_smul, add_zero, sub_zero]

theorem eichE_pW (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    pW D (eichE D a y0 hy v) = pW D v + (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0) := by
  rw [eichE_apply]
  have hf : ∀ b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hy2 : ∀ b, (VS D).hT (D.sp.hypF b) y0 = 0 := hy.2.1
  simp only [pW, eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_sub, map_smul, hf, hy.1, hy2, hy.2.2,
    D.sp.hyp_ee, (D.sp.hyp_orthz a).1, smul_eq_mul, mul_zero, add_zero, sub_zero, zero_add, mul_ite,
    mul_one, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, add_smul, sub_smul, zero_div]
  module

theorem eichE_hTe (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (a' : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE a') (eichE D a y0 hy v) = (VS D).hT (D.sp.hypE a') v := by
  rw [eichE_apply]
  simp [eichL, D.sp.hyp_ee, hy.1 a']

theorem eich_all (hN : UnipotentIntegralIsGroup) (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (y0 : Fin D.R.rS → (VS D).V)
    (hy : ∀ a, InW D (y0 a)) (hyΛ : ∀ a, y0 a ∈ Λ) :
    ∃ n ∈ N0 F0 Λ, ∀ v, pW D (n v) = pW D v + ∑ a, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) := by
  have key : ∀ s : Finset (Fin D.R.rS), ∃ n ∈ N0 F0 Λ, ∀ v,
      pW D (n v) = pW D v + ∑ a ∈ s, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) ∧
      ∀ a', (VS D).hT (D.sp.hypE a') (n v) = (VS D).hT (D.sp.hypE a') v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl _ _, (hN D F0 Λ).1, fun v => ⟨by simp, fun a' => rfl⟩⟩
    | @insert a s ha ih =>
      obtain ⟨n, hn, hv⟩ := ih
      refine ⟨n.trans (eichE D a (y0 a) (hy a)),
        (hN D F0 Λ).2.2 n hn _ (eichE_mem D F0 Λ hF a (hy a) (hyΛ a)), fun v => ⟨?_, fun a' => ?_⟩⟩
      · rw [LinearEquiv.trans_apply, eichE_pW, (hv v).1, (hv v).2 a, Finset.sum_insert ha]
        abel
      · rw [LinearEquiv.trans_apply, eichE_hTe, (hv v).2 a']
  obtain ⟨n, hn, hv⟩ := key Finset.univ
  exact ⟨n, hn, fun v => (hv v).1⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gen_red {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (hP : P.FG) (N : ℤ) (hN : N ≠ 0) :
    ∃ Rs : Set M, Rs.Finite ∧ ∀ x ∈ P, ∃ q ∈ P, ∃ ρ ∈ Rs, x = N • q + ρ := by
  obtain ⟨s, hs⟩ := hP
  refine ⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩
  intro x hx
  rw [← hs] at hx
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  refine ⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩
  · rw [← hs]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)
  · refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (f g) hN
      have h2 := Int.emod_lt (f g) hN
      omega
    · rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]
  · rw [← hf, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem int_mult (D : Formalism.BasicNotions.D7) (s : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k ∈ s, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨n, hn, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  exact ⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩

theorem lat_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (v : (VS D).V) : ∃ n : ℤ, n ≠ 0 ∧ (n : D.host.E) • v ∈ Λ := by
  first | exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult .. | (apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ hΛ v | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ hΛ | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D

theorem common_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (vs : Finset (VS D).V) (ks : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ (∀ v ∈ vs, (n : D.host.E) • v ∈ Λ) ∧
      ∀ k ∈ ks, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ := by
    induction vs using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert v vs hv ih =>
      obtain ⟨n, hn, h⟩ := ih
      obtain ⟨m, hm, hmv⟩ := lat_mult D hΛ v
      refine ⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · have : ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul, mul_comm]
        rw [this]; exact smul_int_mem D ⟨n, by simp⟩ hmv
      · have : ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul]
        rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)
  obtain ⟨n, hn, h1⟩ := hv
  obtain ⟨m, hm, h2⟩ := int_mult D ks
  refine ⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩
  · have : ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v) := by
      rw [smul_smul, Int.cast_mul, mul_comm]
    rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)
  · obtain ⟨o, ho⟩ := h2 k hk
    refine ⟨(n : 𝓞 D.host.E) * o, ?_⟩
    rw [map_mul, ho, map_intCast]; push_cast; ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inW_add (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (hx : InW D x) (hy : InW D y) : InW D (x + y) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  exact ⟨fun a => by rw [map_add, h1 a, k1 a, add_zero], fun a => by rw [map_add, h2 a, k2 a, add_zero],
    by rw [map_add, h3, k3, add_zero]⟩

theorem inW_smul (D : Formalism.BasicNotions.D7) (k : D.host.E) {x : (VS D).V} (hx : InW D x) : InW D (k • x) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  exact ⟨fun a => by rw [map_smul, h1 a, smul_zero], fun a => by rw [map_smul, h2 a, smul_zero],
    by rw [map_smul, h3, smul_zero]⟩

theorem inW_zero (D : Formalism.BasicNotions.D7) : InW D 0 := by
  unfold InW
  exact ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩

theorem inW_sum (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (x : ι → (VS D).V) (hx : ∀ i, InW D (x i)) :
    InW D (∑ i ∈ s, x i) := by
  exact Finset.sum_induction x (InW D) (fun a b ha hb => inW_add D ha hb) (inW_zero D) (fun i _ => hx i)

def LamW (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | y ∈ Λ ∧ InW D y}
  add_mem' hx hy := ⟨Λ.add_mem hx.1 hy.1, inW_add D hx.2 hy.2⟩
  zero_mem' := ⟨Λ.zero_mem, inW_zero D⟩
  smul_mem' o _ hx := ⟨Λ.smul_mem o hx.1, by
    rw [← algebraMap_smul D.host.E o]; exact inW_smul D _ hx.2⟩

theorem hT_int_left (D : Formalism.BasicNotions.D7) (n : ℤ) (x y : (VS D).V) :
    (VS D).hT ((n : D.host.E) • x) y = (n : D.host.E) * (VS D).hT x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply, star_intCast]

private theorem hT_isIntegral_of_mem_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {y v : (VS D).V} (hy : y ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT y v := by
  have h : Formalism.E.hdual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.E.hdual (VS D).hT Λ := by rw [h]; exact hv
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hv'
  exact Submodule.mem_one.mp (hv' y hy)

theorem pW_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (heΛ : ∀ a, D.sp.hypE a ∈ Λ) (d : ℤ)
    (hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ)
    (hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ) {v : (VS D).V} (hv : v ∈ Λ) :
    (d : D.host.E) ^ 2 • pW D v ∈ Λ := by
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hsm : ∀ (o : 𝓞 D.host.E) {y : (VS D).V}, y ∈ Λ → algebraMap (𝓞 D.host.E) D.host.E o • y ∈ Λ :=
    fun o y hy => by rw [algebraMap_smul]; exact Λ.smul_mem o hy
  have hint : ∀ (n : ℤ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_intCast] at this
  have hnat : ∀ (n : ℕ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_natCast] at this
  unfold pW
  simp only [smul_add, smul_sub, Finset.smul_sum]
  refine Λ.add_mem (Λ.sub_mem (Λ.sub_mem ?_ ?_) ?_) ?_
  · rw [pow_two, mul_smul]; exact hint d (hint d hv)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (hdF a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypF a) v • D.sp.hypE a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • D.sp.hypE a := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho, hT_int_left]
      congr 1
      ring
    rw [heq]; exact hsm _ (heΛ a)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (heΛ a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypE a) v • D.sp.hypF a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • ((d : D.host.E) • D.sp.hypF a) := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho]
      congr 1
      ring
    rw [heq]; exact hsm _ (hdF a)
  · obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU hdz hv
    have hc : (VS D).hT (((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm) v =
        (d : D.host.E) * (D.sp.T : D.host.E)⁻¹ * (VS D).hT D.sp.zm v := by
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      congr 1
      simp
    have hdzm : (d : D.host.E) • D.sp.zm ∈ Λ := by
      have := hnat D.sp.T hdz
      rwa [smul_smul, ← mul_assoc, mul_comm (D.sp.T : D.host.E) (d : D.host.E), mul_assoc,
        mul_inv_cancel₀ hT0, mul_one] at this
    have heq : (d : D.host.E) ^ 2 • (((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm) =
        algebraMap (𝓞 D.host.E) D.host.E o • ((d : D.host.E) • D.sp.zm) := by
      simp only [smul_smul]
      rw [ho, hc]
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [heq]; exact hsm _ hdzm

def Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  1 - R * betaZ D Z

theorem beta_Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) : betaZ D Z * Pm D Z R = 0 := by
  unfold Pm
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]

def Gfl (D : Formalism.BasicNotions.D7) (T' : D.host.E) (b1 b2 : Fin (D.R.rS + 1)) : D.host.E :=
  if b1 = Fin.last D.R.rS ∧ b2 = Fin.last D.R.rS then -T' else 0

def gam (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) (c0 : D.host.E)
    (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0)) / (D.sp.T : D.host.E)

def kap (D : Formalism.BasicNotions.D7) (T' : D.host.E) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (c0 : D.host.E) (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2) +
    (D.sp.T : D.host.E) * star (gam D Z R c0 b) * gam D Z R c0 b

def tv (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) (b : Fin (D.R.rS + 1)) : (VS D).V :=
  ∑ b', Pm D Z R b' b • pWf D x b'

private theorem hT_swap_eq_star' (D : Formalism.BasicNotions.D7) (p q : (VS D).V) :
    (VS D).hT q p = star ((VS D).hT p q) := by
  first
  | exact ((VS D).herm p q).symm
  | exact ((VS D).herm.eq p q).symm
  | simpa using ((VS D).herm p q).symm
  | simpa using ((VS D).herm.eq p q).symm

private theorem pW_add' (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u + v) = pW D u + pW D v := by
  unfold pW
  simp only [map_add, add_smul, Finset.sum_add_distrib, add_div]
  abel

private theorem pW_smul' (D : Formalism.BasicNotions.D7) (c : D.host.E) (v : (VS D).V) :
    pW D (c • v) = c • pW D v := by
  unfold pW
  simp only [map_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub, smul_add, Finset.smul_sum]

private theorem pW_sum' (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    pW D (∑ i ∈ s, f i) = ∑ i ∈ s, pW D (f i) := by
  exact map_sum (AddMonoidHom.mk' (pW D) (pW_add' D)) f s

private theorem hT_pW_self_of_hT_hypE_eq_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V)
    (hw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0) :
    (VS D).hT (pW D w) (pW D w) = (VS D).hT w w +
      (D.sp.T : D.host.E) * star ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) *
        ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) := by
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = star ((VS D).hT p q) := fun p q => hT_swap_eq_star' D p q
  have hee : ∀ a a', (VS D).hT (D.sp.hypE a) (D.sp.hypE a') = 0 := D.sp.hyp_ee
  have hze : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  have hez : ∀ a, (VS D).hT (D.sp.hypE a) D.sp.zm = 0 := fun a => by rw [hs, hze, star_zero]
  have hwe : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => by rw [hs, hw a, star_zero]
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -(D.sp.T : D.host.E) := D.sp.zm_norm
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hwz : (VS D).hT w D.sp.zm = star ((VS D).hT D.sp.zm w) := hs _ _
  unfold pW
  simp only [hw, zero_smul, Finset.sum_const_zero, sub_zero]
  set g := (VS D).hT D.sp.zm w / (D.sp.T : D.host.E) with hg
  set s := ∑ a, (VS D).hT (D.sp.hypF a) w • D.sp.hypE a with hsdef
  have hsy : ∀ y, (VS D).hT s y = ∑ a, star ((VS D).hT (D.sp.hypF a) w) * (VS D).hT (D.sp.hypE a) y := by
    intro y
    simp only [hsdef, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂]
  have hys : ∀ y, (VS D).hT y s = ∑ a, (VS D).hT (D.sp.hypF a) w * (VS D).hT y (D.sp.hypE a) := by
    intro y
    simp only [hsdef, map_sum, map_smul, smul_eq_mul]
  have h1 : (VS D).hT s w = 0 := by rw [hsy]; simp [hw]
  have h2 : (VS D).hT s s = 0 := by rw [hsy]; simp [hys, hee]
  have h3 : (VS D).hT s D.sp.zm = 0 := by rw [hsy]; simp [hez]
  have h4 : (VS D).hT w s = 0 := by rw [hys]; simp [hwe]
  have h5 : (VS D).hT D.sp.zm s = 0 := by rw [hys]; simp [hze]
  have h6 : (VS D).hT D.sp.zm w = (D.sp.T : D.host.E) * g := by
    rw [hg, mul_div_assoc', mul_comm, mul_div_assoc, div_self hT0, mul_one]
  simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, h1, h2, h3, h4, h5, hzz, hwz, h6,
    starRingEnd_apply, star_mul', star_natCast]
  ring

theorem tv_norm (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) (he : F0.e = D.sp.hypE) {c0 : D.host.E} (hc0 : c0 ≠ 0) (hz : F0.z = c0 • D.sp.zm)
    {x : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (tv D Z R x b) (tv D Z R x b) = kap D T' Z R c0 b := by
  obtain ⟨-, hZ, hG⟩ := hx
  set w := ∑ b', Pm D Z R b' b • fr D x b' with hw
  have htv : tv D Z R x b = pW D w := by
    show ∑ b', Pm D Z R b' b • pW D (fr D x b') = pW D w
    rw [hw, pW_sum']
    simp only [pW_smul']
  have hEu : ∀ a b', (VS D).hT (D.sp.hypE a) (fr D x b') = Z (Fin.castSucc a) b' := by
    intro a b'
    have h := hZ (Fin.castSucc a) b'
    simpa [brS, FlagG.fvec, he] using h
  have hzu : ∀ b', (VS D).hT D.sp.zm (fr D x b') = Z (Fin.last D.R.rS) b' / star c0 := by
    intro b'
    have h := hZ (Fin.last D.R.rS) b'
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply] at h
    rw [eq_div_iff (star_ne_zero.mpr hc0), ← h, mul_comm]
  have hGu : ∀ b1 b2, (VS D).hT (fr D x b1) (fr D x b2) = Gfl D T' b1 b2 := by
    intro b1 b2
    rw [hG b1 b2]
    unfold Gfl
    split_ifs <;> first | rfl | (exfalso; tauto)
  have hEw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0 := by
    intro a
    have h0 : (betaZ D Z * Pm D Z R) a b = 0 := by rw [beta_Pm D Z R hR]; rfl
    rw [Matrix.mul_apply] at h0
    rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hEu]
    simpa [betaZ, Matrix.submatrix_apply, mul_comm] using h0
  have hww : (VS D).hT w w =
      ∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2 := by
    rw [hw]
    simp only [LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, map_sum, map_smul, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => ?_))
    rw [hGu b1 b2]
    ring
  have hzw : (VS D).hT D.sp.zm w = ∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0) := by
    rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hzu]
  rw [htv, hT_pW_self_of_hT_hypE_eq_zero D w hEw]
  unfold kap gam
  rw [hww, hzw]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inW_neg (D : Formalism.BasicNotions.D7) {x : (VS D).V} (hx : InW D x) : InW D (-x) := by
  simpa using inW_smul D (-1) hx

theorem stage1_of_unipotentIntegralIsGroup (hN : UnipotentIntegralIsGroup) : Stage1 := by
  intro D T T' F0 Λ hF Z R hR
  have hF' := hF
  obtain ⟨hlat, hU, he, heΛ0, c0, hc0, hz⟩ := hF
  have heΛ : ∀ a, D.sp.hypE a ∈ Λ := fun a => by rw [← he]; exact heΛ0 a
  obtain ⟨d, hd0, hdv, hdk⟩ := common_mult D hlat
    (Finset.univ.image D.sp.hypF ∪ {((D.sp.T : D.host.E)⁻¹) • D.sp.zm})
    (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) ∪
      Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2))
  have hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ := fun a =>
    hdv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ := by
    rw [← smul_smul]; exact hdv _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hdR : ∀ b a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * R b a := fun b a =>
    hdk _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2)
      (Finset.mem_univ (b, a))))
  have hdP : ∀ b' b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * Pm D Z R b' b :=
    fun b' b => hdk _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2) (Finset.mem_univ (b', b))))
  have hd2 : ∀ v ∈ Λ, (d : D.host.E) ^ 2 • pW D v ∈ Λ := fun v hv => pW_lat D hU heΛ d hdF hdz hv
  have hdE : (d : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hd0
  have hd3 : (d : D.host.E) ^ 3 ≠ 0 := pow_ne_zero 3 hdE
  have hΛfg : (Λ.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hlat.fg

  let Sb : Fin (D.R.rS + 1) → Set (VS D).V := fun b =>
    {w | w ∈ Λ.restrictScalars ℤ ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = (d : D.host.E) ^ 6 * kap D T' Z R c0 b}
  have hSb : ∀ b, (Sb b).Finite := fun b => definite_finite D _ hΛfg _
  let Tset : Fin (D.R.rS + 1) → Set (VS D).V := fun b => (fun w => (((d : D.host.E) ^ 3)⁻¹) • w) '' Sb b

  have hLWfg : ((LamW D Λ).restrictScalars ℤ).FG := Submodule.FG.of_le hΛfg (fun y hy => hy.1)
  obtain ⟨Rs, hRs, hred⟩ := gen_red _ hLWfg (2 * d ^ 3) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hd0))
  refine ⟨(fun p : (Fin (D.R.rS + 1) → (VS D).V) × (Fin D.R.rS → (VS D).V) =>
      fun b => p.1 b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • p.2 a) ''
      (Set.pi Set.univ Tset ×ˢ Set.pi Set.univ (fun _ => Rs)), ?_, ?_⟩
  · exact ((Set.Finite.pi (fun b => (hSb b).image _)).prod (Set.Finite.pi (fun _ => hRs))).image _
  intro x hx
  have hbeta : ∀ (a : Fin D.R.rS) b, (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro a b
    have := hx.2.1 (Fin.castSucc a) b
    simpa [brS, FlagG.fvec, he, betaZ] using this

  have hw2 : ∀ b, (d : D.host.E) ^ 2 • pWf D x b ∈ LamW D Λ := fun b =>
    ⟨hd2 _ (hx.1 b), inW_smul D _ (inW_pW D _)⟩
  have hu : ∀ a, (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) ∈ (LamW D Λ).restrictScalars ℤ := by
    intro a
    have : (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) =
        ∑ b, ((d : D.host.E) * R b a) • ((d : D.host.E) ^ 2 • pWf D x b) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_smul, smul_smul]; ring_nf
    rw [Submodule.restrictScalars_mem, this]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ := hdR b a
    rw [← ho, algebraMap_smul]
    exact (LamW D Λ).smul_mem o (hw2 b)
  choose q hq ρ hρ hqρ using fun a => hred _ (hu a)
  obtain ⟨n, hn, hpW⟩ := eich_all hN D F0 Λ hF' (fun a => -q a) (fun a => inW_neg D (hq a).2)
    (fun a => Λ.neg_mem (hq a).1)
  refine ⟨n, hn, ⟨(tv D Z R x, ρ), ⟨fun b _ => ?_, fun a _ => hρ a⟩, ?_⟩⟩
  ·
    refine ⟨(d : D.host.E) ^ 3 • tv D Z R x b, ⟨?_, ?_, ?_, ?_, ?_⟩, inv_smul_smul₀ hd3 _⟩
    · rw [Submodule.restrictScalars_mem]
      have : (d : D.host.E) ^ 3 • tv D Z R x b =
          ∑ b', ((d : D.host.E) * Pm D Z R b' b) • ((d : D.host.E) ^ 2 • pWf D x b') := by
        rw [tv, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ => by rw [smul_smul, smul_smul]; ring_nf
      rw [this]
      refine Submodule.sum_mem _ fun b' _ => smul_int_mem D (hdP b' b) (hw2 b').1
    all_goals have hW : InW D ((d : D.host.E) ^ 3 • tv D Z R x b) :=
      inW_smul D _ (inW_sum D _ _ fun b' => inW_smul D _ (inW_pW D _))
    · exact hW.1
    · exact hW.2.1
    · exact hW.2.2
    · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
        star_pow, star_intCast]
      rw [tv_norm D T' F0 Λ Z R hR he hc0 hz hx b]
      ring
  ·
    funext b
    have h2q : ∀ a, (2 : D.host.E) • q a = (∑ b', R b' a • pWf D x b') - (((d : D.host.E) ^ 3)⁻¹) • ρ a := by
      intro a
      have e1 := hqρ a
      rw [← Int.cast_smul_eq_zsmul D.host.E] at e1
      have e2 : ((2 * d ^ 3 : ℤ) : D.host.E) • q a = (d : D.host.E) ^ 3 • (∑ b', R b' a • pWf D x b') - ρ a := by
        rw [e1]; abel
      have e3 : (2 : D.host.E) • q a = (((d : D.host.E) ^ 3)⁻¹) • (((2 * d ^ 3 : ℤ) : D.host.E) • q a) := by
        rw [smul_smul]; congr 1; push_cast; field_simp
      rw [e3, e2, smul_sub, inv_smul_smul₀ hd3]
    symm
    show pW D (fr D (act D n x) b) = tv D Z R x b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • ρ a
    rw [fr_act, hpW]
    have e4 : ∀ a, (VS D).hT (D.sp.hypE a) (fr D x b) • ((2 : D.host.E) • -q a) =
        -(betaZ D Z a b • (∑ b', R b' a • pWf D x b')) + (((d : D.host.E) ^ 3)⁻¹) • (betaZ D Z a b • ρ a) := by
      intro a
      rw [hbeta, smul_neg, h2q, smul_neg, smul_sub, smul_comm (betaZ D Z a b) (((d : D.host.E) ^ 3)⁻¹) (ρ a)]
      abel
    rw [Finset.sum_congr rfl fun a _ => e4 a, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [tv, Pm, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_smul,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a b' => (betaZ D Z a b * R b' a) • pWf D x b')]
    have e5 : ∀ b' a, (betaZ D Z a b * R b' a) • pWf D x b' = (R b' a * betaZ D Z a b) • pWf D x b' :=
      fun b' a => by rw [mul_comm]
    simp only [e5]
    show pW D (fr D x b) + _ = _
    have e6 : pWf D x b = pW D (fr D x b) := rfl
    rw [← e6]
    abel

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_count_first_stage : Stage1 := stage1_of_unipotentIntegralIsGroup unipotent_integral_isGroup

theorem orbitReps_of_stage2 (h2 : Stage2) : OrbitReps :=
  orbitReps_of unipotent_integral_isGroup rank_gram good_places_integral orbit_count_first_stage h2 finite_level_index

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ∑ a, ∑ a', S a a' • ((VS D).hT (D.sp.hypE a')).smulRight (D.sp.hypE a)

theorem skL_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D S v = v + ∑ a, (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) • D.sp.hypE a := by
  simp only [skL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, Finset.sum_smul]

theorem hE_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE b) (skL D S v) = (VS D).hT (D.sp.hypE b) v := by
  rw [skL_apply, map_add, map_sum]
  simp [D.sp.hyp_ee]

theorem skL_inv (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D (-S) (skL D S v) = v := by
  rw [skL_apply D (-S) (skL D S v)]
  simp only [hE_skL]
  rw [skL_apply]
  have e : ∀ a, (∑ a', (-S) a a' * (VS D).hT (D.sp.hypE a') v) =
      -(∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) := fun a => by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.neg_apply, neg_mul]
  simp_rw [e, neg_smul, Finset.sum_neg_distrib]
  exact add_neg_cancel_right _ _

def skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (skL D S) (skL D (-S))
    (LinearMap.ext fun v => by
      have h := skL_inv D (-S) v
      rw [neg_neg] at h
      exact h)
    (LinearMap.ext fun v => skL_inv D S v)

theorem skE_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skE D S v = skL D S v := rfl

theorem dsum_cancel {K : Type} [CommRing K] {r : ℕ} (S : Matrix (Fin r) (Fin r) K) (X Y : Fin r → K) :
    ∑ a, (∑ a', S a a' * X a') * Y a + ∑ a, (∑ a', -S a' a * Y a') * X a = 0 := by
  have e : ∑ a, (∑ a', -S a' a * Y a') * X a = -∑ a, (∑ a', S a a' * X a') * Y a := by
    simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  rw [e, add_neg_cancel]

theorem skL_isom (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j) (u v : (VS D).V) :
    (VS D).hT (skL D S u) (skL D S v) = (VS D).hT u v := by
  have hue : ∀ b, (VS D).hT u (D.sp.hypE b) = star ((VS D).hT (D.sp.hypE b) u) := fun b =>
    ((VS D).herm.eq (D.sp.hypE b) u).symm
  have key := dsum_cancel S (fun b => (VS D).hT (D.sp.hypE b) v) (fun b => star ((VS D).hT (D.sp.hypE b) u))
  beta_reduce at key
  rw [skL_apply, skL_apply]
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
    D.sp.hyp_ee, hue, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero, starRingEnd_apply, star_sum,
    star_mul', hS]
  linear_combination key

theorem hE_int (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {v : (VS D).V}
    (hv : v ∈ Λ) : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT (D.sp.hypE a) v := by
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hF.2.1
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' _ he)
  exact ⟨o, ho⟩

theorem skL_lat (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) {v : (VS D).V} (hv : v ∈ Λ) :
    skL D S v ∈ Λ := by
  rw [skL_apply]
  refine Λ.add_mem hv (Λ.sum_mem fun a _ => ?_)
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hc : (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    sum_mem fun a' _ => mul_mem (hO a a') (hE_int D hF a' hv)
  obtain ⟨o, ho⟩ := hc
  rw [← ho, algebraMap_smul]
  exact Λ.smul_mem o he

theorem skL_X (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) : skL D S x = x := by
  have h0 : ∀ a', (VS D).hT (D.sp.hypE a') x = 0 := by
    intro a'
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact D.sp.hyp_ee a' b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  rw [skL_apply]
  simp [h0]

theorem skL_sub_mem (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (x : (VS D).V) :
    skL D S x - x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
  rw [skL_apply, add_sub_cancel_left]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem skE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) :
    skE D S ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e), skE D S x = x := by
    intro x hx
    rw [hFe] at hx
    exact skL_X D S hx
  have hO' : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (-S) i j := fun i j => by
    obtain ⟨o, ho⟩ := hO i j
    exact ⟨-o, by rw [map_neg, ho, Matrix.neg_apply]⟩
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact skL_isom D S hS x y
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => skL_lat D hF S hO hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨skL D (-S) v, skL_lat D hF (-S) hO' hv, ?_⟩
      have h1 := skL_inv D (-S) v
      rw [neg_neg] at h1
      exact h1
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x _
    have h1 := skL_sub_mem D S x
    rw [← hFe] at h1
    exact h1
  · intro a
    exact hspan _ (Submodule.subset_span ⟨a, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [skE_apply, skL_apply]
    simp [hzm]

private theorem pW_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (w : (VS D).V) : pW D (skL D S w) = pW D w := by
  have hf : ∀ a b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun a b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hz : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  rw [skL_apply]
  simp only [pW, map_add, map_sum, map_smul, hf, hz, D.sp.hyp_ee, smul_eq_mul, mul_zero, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, add_smul,
    Finset.sum_add_distrib, Finset.sum_const_zero, zero_smul]
  module

theorem pWf_skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : pWf D (act D (skE D S) x) = pWf D x := by
  funext b
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [pWf]
  rw [hfr, pW_skL]

theorem alM_skE (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) : alM D (act D (skE D S) x) = alM D x + S * betaZ D Z := by
  ext a b
  have hf : ∀ c, (VS D).hT (D.sp.hypF a) (D.sp.hypE c) = if c = a then 1 else 0 := fun c => by
    rw [← (VS D).herm.eq (D.sp.hypE c) (D.sp.hypF a), D.sp.hyp_ef]
    split_ifs <;> simp
  have hZ : ∀ c', (VS D).hT (D.sp.hypE c') (fr D x b) = Z (Fin.castSucc c') b := fun c' => by
    have h1 := hx.2.1 (Fin.castSucc c') b
    simp only [Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1
    exact h1
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [alM, Matrix.add_apply, Matrix.mul_apply, betaZ, Matrix.submatrix_apply, id]
  rw [hfr, skL_apply, map_add, map_sum]
  simp only [map_smul, smul_eq_mul, hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hZ]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem isInt_O (o : 𝓞 K) : IsIntegral ℤ (algebraMap (𝓞 K) K o) := o.2

theorem O_of_isInt {x : K} (h : IsIntegral ℤ x) : ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x := ⟨⟨x, h⟩, rfl⟩

theorem isInt_intCast (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))

theorem isInt_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  h.map (starRingEnd K).toIntAlgHom

theorem commonDen (s : Finset K) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ s, IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩
  have e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
  have e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2 := by rw [← Int.cast_natCast, e0, Int.cast_pow]
  rw [e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]
  exact (isInt_intCast y).mul (h x hx)

theorem reduceRep (N : ℕ) (hN : 0 < N) : ∃ Rep : Set K, Rep.Finite ∧ (∀ ρ ∈ Rep, IsIntegral ℤ ρ) ∧
    ∀ o : K, IsIntegral ℤ o → ∃ t ρ : K, IsIntegral ℤ t ∧ ρ ∈ Rep ∧ o = (N : K) * t + ρ := by
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI
  have hIne : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have := I.finiteQuotientOfFreeOfNeBot hIne
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ
  refine ⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact isInt_O _
  · intro o ho
    obtain ⟨oo, rfl⟩ := O_of_isInt ho
    set q := Ideal.Quotient.mk I oo
    have hq : Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq _ q
    have hmem : oo - σ q ∈ I := Ideal.Quotient.eq.1 hq.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩
    have e : oo = t * N + σ q := by rw [ht]; ring
    rw [e, map_add, map_mul, map_natCast]
    ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hermP (D : Formalism.BasicNotions.D7) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  (alM D x).conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * alM D x

private theorem fr_sub_eq_sum_hypE_of_good_of_pWf_eq (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) (b : Fin (D.R.rS + 1)) :
    fr D x b - fr D y b = ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) • D.sp.hypE c := by
  have hE : ∀ c, (VS D).hT (D.sp.hypE c) (fr D x b - fr D y b) = 0 := by
    intro c
    have h1 := hx.2.1 (Fin.castSucc c) b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZ : (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
    obtain ⟨c0, hc0, hz⟩ := hF.2.2.2.2
    have h1 := hx.2.1 (Fin.last _) b
    have h2 := hy.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    have h3 : (starRingEnd D.host.E) c0 * (VS D).hT D.sp.zm (fr D x b - fr D y b) = 0 := by
      rw [map_sub, mul_sub, h1, h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd ((map_eq_zero _).1 h) hc0
    · exact h
  have hP : pW D (fr D x b - fr D y b) = 0 := by
    have h := congrFun hw b
    simp only [pWf] at h
    rw [pW_eq, map_sub, ← pW_eq, ← pW_eq, h, sub_self]
  have h := hP
  simp only [pW, hE, hZ, zero_smul, Finset.sum_const_zero, sub_zero, zero_div, add_zero] at h
  exact sub_eq_zero.1 h

theorem hermitianDivisible_eq_smul (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    {x y : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (hy : Good D T' F0 Λ Z y)
    (hw : pWf D x = pWf D y) : hermP D Z x = hermP D Z y := by
  have hd := fun b => fr_sub_eq_sum_hypE_of_good_of_pWf_eq D T' F0 Λ hF Z hx hy hw b
  have hβ : ∀ c b, (VS D).hT (D.sp.hypE c) (fr D y b) = betaZ D Z c b := by
    intro c b
    have h2 := hy.2.1 (Fin.castSucc c) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h2
    simp only [betaZ, Matrix.submatrix_apply, id, h2]
  have hβ' : ∀ c a, (VS D).hT (fr D y a) (D.sp.hypE c) = star (betaZ D Z c a) := by
    intro c a
    rw [← hβ, hT_star]
  have hα : ∀ c b, alM D x c b = alM D y c b + (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) := by
    intro c b
    simp only [alM, map_sub]
    ring
  have hee : ∀ i j, (VS D).hT (D.sp.hypE i) (D.sp.hypE j) = 0 := fun i j => D.sp.hyp_ee i j
  have key : ∀ a b, ∑ c, star ((VS D).hT (D.sp.hypF c) (fr D x a - fr D y a)) * betaZ D Z c b +
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) = 0 := by
    intro a b
    have hxx := hx.2.2 a b
    rw [← hy.2.2 a b] at hxx
    have ex : ∀ a, fr D x a = fr D y a + ∑ c, (VS D).hT (D.sp.hypF c) (fr D x a - fr D y a) • D.sp.hypE c := by
      intro a
      rw [← hd a]
      abel
    rw [ex a, ex b] at hxx
    simp only [map_add, map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, hee, mul_zero,
      Finset.sum_const_zero, add_zero, hβ, hβ', starRingEnd_apply] at hxx
    linear_combination hxx
  ext a b
  simp only [hermP, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hα, star_add,
    add_mul, mul_add, Finset.sum_add_distrib]
  have k2 : ∑ c, star (betaZ D Z c a) * (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) =
      ∑ c, (VS D).hT (D.sp.hypF c) (fr D x b - fr D y b) * star (betaZ D Z c a) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linear_combination key a b + k2

private theorem exists_nat_mul_alM_mul_isIntegral_of_fr_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : (Fin D.R.rS → (VS D).V) × (VS D).V, (∀ b, fr D x b ∈ Λ) →
      ∀ i j, IsIntegral ℤ ((N : D.host.E) * (alM D x * R) i j) := by
  obtain ⟨g, hg⟩ := hF.1.fg
  obtain ⟨N1, hN1, h1⟩ := commonDen (K := D.host.E)
    (Finset.image (fun p : Fin D.R.rS × (VS D).V => (VS D).hT (D.sp.hypF p.1) p.2)
      (Finset.univ ×ˢ g) ∪
     Finset.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) Finset.univ)
  have hv : ∀ v ∈ Λ, ∀ c, IsIntegral ℤ ((N1 : D.host.E) * (VS D).hT (D.sp.hypF c) v) := by
    intro v hv c
    rw [← hg] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      exact h1 _ (Finset.mem_union_left _ (Finset.mem_image.2
        ⟨(c, y), Finset.mem_product.2 ⟨Finset.mem_univ _, by exact_mod_cast hy⟩, rfl⟩))
    | zero =>
      rw [map_zero, mul_zero]
      exact isIntegral_zero
    | add y z _ _ hy hz =>
      rw [map_add, mul_add]
      exact hy.add hz
    | smul o y _ hy =>
      rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, mul_left_comm]
      exact (isInt_O o).mul hy
  refine ⟨N1 * N1, Nat.mul_pos hN1 hN1, fun x hx i j => ?_⟩
  rw [Matrix.mul_apply, Nat.cast_mul, Finset.mul_sum]
  refine IsIntegral.sum _ (fun b _ => ?_)
  have e : (N1 : D.host.E) * N1 * (alM D x i b * R b j) =
      ((N1 : D.host.E) * alM D x i b) * ((N1 : D.host.E) * R b j) := by ring
  rw [e]
  exact (hv _ (hx b) i).mul (h1 _ (Finset.mem_union_right _ (Finset.mem_image.2
    ⟨(b, j), Finset.mem_univ _, rfl⟩)))

theorem orbit_count_second_stage : Stage2 := by
  intro D T T' F0 Λ hF Z R hR Wf hWf
  obtain ⟨N, hN, hden⟩ := exists_nat_mul_alM_mul_isIntegral_of_fr_mem D F0 Λ hF R
  obtain ⟨Rep, hRepF, hRepI, hrep⟩ := reduceRep (K := D.host.E) (4 * N) (by omega)
  let hfun : (Fin (D.R.rS + 1) → (VS D).V) → Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun w =>
    if h : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = w then R.conjTranspose * hermP D Z h.choose * R else 0
  refine ⟨(fun q : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E × (Fin D.R.rS → Fin D.R.rS → D.host.E) =>
      Matrix.of fun i j => q.1 i j / 2 + (q.2 i j - star (q.2 j i)) / 4) ''
      ((hfun '' Wf) ×ˢ Set.pi Set.univ
        (fun _ => Set.pi Set.univ (fun _ => (fun ρ => ρ / (N : D.host.E)) '' Rep))), ?_, ?_⟩
  · exact ((hWf.image _).prod (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hRepF.image _)).image _
  intro x hx hxw
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ i j, IsIntegral ℤ ((N : D.host.E) *
      ((alM D x * R) i j - star ((alM D x * R) j i))) := by
    intro i j
    rw [mul_sub]
    refine (hden x hx.1 i j).sub ?_
    have h := isInt_star (hden x hx.1 j i)
    rw [star_mul', star_natCast] at h
    exact h
  choose t ρ ht hρ heq using fun i j => hrep _ (hint i j)
  have hrel : ∀ i j, (alM D x * R) i j - star ((alM D x * R) j i) = 4 * t i j + ρ i j / N := by
    intro i j
    have h := heq i j
    push_cast at h
    have h' : (alM D x * R) i j - star ((alM D x * R) j i) - 4 * t i j = ρ i j / N := by
      rw [eq_div_iff hN0]
      linear_combination h
    linear_combination h'
  let S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := Matrix.of fun i j => star (t j i) - t i j
  have hSskew : ∀ i j, star (S j i) = -S i j := by
    intro i j
    simp only [S, Matrix.of_apply, star_sub, star_star, neg_sub]
  have hSint : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j :=
    fun i j => O_of_isInt ((isInt_star (ht j i)).sub (ht i j))
  refine ⟨skE D S, skE_mem D F0 Λ hF S hSskew hSint, pWf_skE D S x, ?_⟩
  rw [alM_skE D T' F0 Λ hF Z S hx, Matrix.add_mul, Matrix.mul_assoc, hR, Matrix.mul_one]
  have e1 : R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = (alM D x * R).conjTranspose := by
    calc R.conjTranspose * ((alM D x).conjTranspose * betaZ D Z) * R = R.conjTranspose * (alM D x).conjTranspose * (betaZ D Z * R) := by
          simp only [Matrix.mul_assoc]
      _ = (alM D x * R).conjTranspose := by rw [hR, Matrix.mul_one, Matrix.conjTranspose_mul]
  have e2 : R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = alM D x * R := by
    calc R.conjTranspose * ((betaZ D Z).conjTranspose * alM D x) * R = (R.conjTranspose * (betaZ D Z).conjTranspose) * (alM D x * R) := by
          simp only [Matrix.mul_assoc]
      _ = alM D x * R := by
          rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one, Matrix.one_mul]
  have hH : R.conjTranspose * hermP D Z x * R = alM D x * R + (alM D x * R).conjTranspose := by
    rw [hermP, Matrix.mul_add, Matrix.add_mul, e1, e2, add_comm]
  have hfx : hfun (pWf D x) = alM D x * R + (alM D x * R).conjTranspose := by
    have hex : ∃ y, Good D T' F0 Λ Z y ∧ pWf D y = pWf D x := ⟨x, hx, rfl⟩
    simp only [hfun, dif_pos hex]
    rw [hermitianDivisible_eq_smul D T' F0 Λ hF Z hex.choose_spec.1 hx hex.choose_spec.2, hH]
  refine ⟨(alM D x * R + (alM D x * R).conjTranspose, fun i j => ρ i j / N),
    ⟨⟨pWf D x, hxw, hfx⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    exact ⟨ρ i j, hρ i j, rfl⟩
  · ext i j
    have h1 := hrel i j
    have h2 := congrArg star (hrel j i)
    simp only [star_sub, star_add, star_mul', star_star, star_div₀, star_natCast, star_ofNat] at h2
    simp only [S, Matrix.of_apply, Matrix.add_apply, Matrix.conjTranspose_apply, star_div₀,
      star_natCast]
    linear_combination (-1 / 4 : D.host.E) * h1 + (1 / 4 : D.host.E) * h2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_representatives : OrbitReps := orbitReps_of_stage2 orbit_count_second_stage

end PI.UnitaryGroupMassFormula.CntFormula
end
end
