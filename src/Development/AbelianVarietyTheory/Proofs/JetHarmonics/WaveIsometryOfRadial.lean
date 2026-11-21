import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialModuleFormOfXiExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableWeightNormSq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PosAtOfCptCoefOfThmPActualCpt

section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.WaveIsometry

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBFV

theorem isometry_of_bounded (hRad : JC.RadialModuleForm) (hP : P5.ThmPActualCpt) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (s : ℂ)
    (x x' : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ) (hε : 0 < ε)
    (hx : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) (hx' : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e))
    (hb : ∀ e, ∃ R, PBF.BSR R (x e)) (hb' : ∀ e, ∃ R, PBF.BSR R (x' e))
    (hbw : ∀ e, ∃ R, PBF.BSR R (KB.waveG (p.T.bs j) s w x' e)) :
    p.form j hj w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') = p.form j hj w x x' := by
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hJ := fun (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JC.NiceCoef (p.T.bs j) ε F)
    (hR : ∃ R, PBF.BSR R F) => PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR.choose_spec
  obtain ⟨Cst, hC, hform⟩ := hRad Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) (hx a) (hb a)
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) (hx' a) (hb' a)
  have hnx := waveG_nice (p.T.bs j) ε s w x hx
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) (hnx' e) (hbw e)
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end GlobalTheory.WaveIsometry
end
end

section
namespace GlobalTheory.ListDuality

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Tower

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

theorem entry_picture_bounded {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
    {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
    {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
    {l0 : ℕ} (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef (T.bs j) ε F)
    {R : ℝ} (hR : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) (Y : ℝ) (a b : Fin 2) :
    ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j ((QQi L st 0 (Y : ℂ) a b).1 Φ) F' := by
  let w : List C.Letter := [(true, Y)]
  let Fv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := Pi.single (eS 0 b) F
  have hFv : ∀ e, JC.NiceCoef (T.bs j) ε (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  have hRv : ∀ e, BSR R (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hR
    · simp only [Fv, Pi.single_eq_of_ne h]; exact fun g _ h0 => absurd rfl h0
  let xv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun e => B.JF (T.bs j) (Fv e)
  let Φv : Ix (Fin w.length) →
      RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' :=
    Pi.single (eS 0 b) Φ
  have hx : ∀ e, xv e ∈ FFl (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
      (OmPlus (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z') := fun e =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (Fv e) ε hε (hFv e)
  have hΦv : ∀ e, ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φv e : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (xv e) y.1 y.2 := by
    intro e y hy
    by_cases h : e = eS 0 b
    · subst h
      have := hΦ y hy
      simp only [Φv, xv, Fv, Pi.single_eq_same]
      exact this
    · simp only [Φv, xv, Fv, Pi.single_eq_of_ne h]
      have h0 := congrFun (congrFun (resG_JF_zero (T.bs j) (Fin.last (JC.parLev P0 j).r)) y.1) y.2
      exact h0.symm
  refine ⟨D.actOp (D.RRlev T (M.sgn P0 l0) j w) Fv (eS 0 a),
    (actOp_nice_bsr P0 T (M.sgn P0 l0) j w Fv hFv hRv (eS 0 a)).1,
    (actOp_nice_bsr P0 T (M.sgn P0 l0) j w Fv hFv hRv (eS 0 a)).2, fun y hy => ?_⟩
  have hact := Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w xv Φv hx hΦv (eS 0 a) y hy
  have hbes := Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a) y hy
  have e : P5.act (RRi L st 0 (D.positionted w)) Φv (eS 0 a) = (QQi L st 0 (Y : ℂ) a b).1 Φ := by
    show actP (RRw (QQi L st 0) [(⟨true, 0, (Y : ℂ)⟩ : Letter ℂ (Fin 1))]) (Pi.single (eS 0 b) Φ) (eS 0 a) = _
    exact blockMulVec_one_letter _ _ _ _ _ _
  have e' := congrArg (fun Ψ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
    (T.bs j).π' => (Ψ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2) e
  exact e'.symm.trans (hact.trans hbes.symm)

end Tower

section Cls

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

theorem picture_mem_stable_bounded (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    (hJ : ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε R : ℝ), 0 < ε → JC.NiceCoef (T.bs j) ε F → BSR R F →
      ∃ Φ ∈ K 0, IsPic T j Φ F)
    (Pts : Set ℝ) {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) {R : ℝ} (hR : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ Ucls (K 0) (Gen L st Pts) := by
  intro m hm
  have key : ∀ m ∈ Submonoid.closure (Gen L st Pts), ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      JC.NiceCoef (T.bs j) ε F → BSR R F → IsPic T j Φ F →
      ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j (m.1 Φ) F' := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem a ha =>
      intro F Φ hF hR hΦ
      obtain ⟨Y, _, i, i', rfl⟩ := ha
      exact entry_picture_bounded hD hε hF hR Φ hΦ Y i i'
    | one => intro F Φ hF hR hΦ; exact ⟨F, hF, hR, hΦ⟩
    | mul a b _ _ iha ihb =>
      intro F Φ hF hR hΦ
      obtain ⟨F1, h1, h1r, h1'⟩ := ihb F Φ hF hR hΦ
      obtain ⟨F2, h2, h2r, h2'⟩ := iha F1 _ h1 h1r h1'
      exact ⟨F2, h2, h2r, h2'⟩
  obtain ⟨F', hF', hR', hΦ'⟩ := key m hm F Φ hF hR hΦ
  obtain ⟨Ψ, hK, hΨ⟩ := hJ F' ε R hε hF' hR'
  have e : m.1 Φ = Ψ := radSp_ext _ Ψ (fun y hy => (hΦ' y hy).trans (hΨ y hy).symm)
  rw [e]; exact hK

end Cls

theorem listDuality_cpt (hRMF : Formalism.FourierDecayAlt.JC.RadialModuleForm) : Formalism.FourierDecayAlt.KB.SizeStdCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w ys hc1 hc2 hys
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  have hqpos := qw_pos P hOK p.l0 hl1 hlk w ys hc1 hc2
  refine ⟨fun y hy => (hqpos y hy).1, ?_⟩
  intro x x' hcx hcx'
  obtain ⟨ε₁, hε₁, hx₁⟩ := Formalism.FourierDecayAlt.P.PBL.nv_of_cv (Bs := p.T.bs j) (x := x) hcx
  obtain ⟨ε₂, hε₂, hx₂⟩ := Formalism.FourierDecayAlt.P.PBL.nv_of_cv (Bs := p.T.bs j) (x := x') hcx'
  obtain ⟨ε, hε, hx, hx'⟩ : ∃ ε : ℝ, 0 < ε ∧ (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) ∧
      (∀ e, JC.NiceCoef (p.T.bs j) ε (x' e)) :=
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, Formalism.FourierDecayAlt.P.PBL.nv_mono hx₁ (min_le_left _ _),
      Formalism.FourierDecayAlt.P.PBL.nv_mono hx₂ (min_le_right _ _)⟩
  choose Rx hRx using fun e => (cpt_nice_bsr (hcx e)).2
  choose Rx' hRx' using fun e => (cpt_nice_bsr (hcx' e)).2
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin (KB.plusW ys w).length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := hRMF Wp Wq P p.T jF X μ L st p.l0 hD
  have hJ' : ∀ (F : B.Mat P.k (P.r - jF) → (Wq →L[ℂ] Wp)) (ε R : ℝ), 0 < ε → JC.NiceCoef (p.T.bs jF) ε F →
      BSR R F → ∃ Φ ∈ K 0, IsPic p.T jF Φ F := fun F ε R hε hF hR =>
    pic_of_cptClause (p.T.bs jF) (K 0) hJ hε hF hR

  choose Φ hΦK hΦ using fun a => hJ' (x a) ε (Rx a) hε (hx a) (hRx a)
  choose Φ' hΦ'K hΦ' using fun a => hJ' (x' a) ε (Rx' a) hε (hx' a) (hRx' a)

  let Pts : Set ℝ := {Y | (∃ l ∈ KB.plusW ys w, l.2 = Y) ∨ (∃ l ∈ KB.minusW ys w, l.2 = Y)}
  have hW1 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.plusW ys w)
    hc1.1 hc1.2
  have hW2 := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 (KB.minusW ys w)
    hc2.1 hc2.2
  have hPts : ∀ Y ∈ Pts, ∃ s0 : Fin (KB.plusW ys w).length,
      WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
        [(⟨true, s0, (Y : ℂ)⟩ : Letter ℂ (Fin (KB.plusW ys w).length))] := by
    intro Y hY
    have hn : 0 < (KB.plusW ys w).length ∧ I.OnCut P.u P.u' p.l0 Y := by
      rcases hY with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · exact ⟨List.length_pos_of_mem hl, cutWord_mem P hc1 hl⟩
      · exact ⟨by rw [← len_pm]; exact List.length_pos_of_mem hl, cutWord_mem P hc2 hl⟩
    refine ⟨⟨0, hn.1⟩, wordOK_gen (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 _ (by simp)
      (fun l hl => ⟨Y, by simp at hl; rw [hl], hn.2⟩) (by simp)⟩
  have hΦU : ∀ e, Φ e ∈ Ucls (K 0) (Gen L st Pts) := fun e =>
    picture_mem_stable_bounded hD hJ' Pts hε (hx e) (hRx e) (Φ e) (hΦ e)
  have hΦ'U : ∀ e, Φ' e ∈ Ucls (K 0) (Gen L st Pts) := fun e =>
    picture_mem_stable_bounded hD hJ' Pts hε (hx' e) (hRx' e) (Φ' e) (hΦ' e)

  have hS := isStart_QQi _ _ _ _ _ X μ L st p.l0 hD 0
  have hle := Ucls_le (K 0) (Gen L st Pts)
  have hU := (sesquilinear_level_zero_pairing hThm).mono hle

  have hP1 : ∀ l ∈ Lw ys w ++ Ww ys w, ∃ Y ∈ Pts, l.pt = (Y : ℂ) := by
    intro l hl
    rw [Lw_append_Ww] at hl
    unfold D.positionted at hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨((KB.plusW ys w).get a).2, Or.inl ⟨_, List.get_mem _ _, rfl⟩, rfl⟩
  have hLmem : ∀ l ∈ Lw ys w, ∃ y ∈ ys, l.pt = (y : ℂ) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    rw [Lw_getElem]
    exact ⟨_, List.getElem_mem _, rfl⟩
  have hP2 : ∀ l ∈ Lw ys w, ∃ Y ∈ Pts, l.pt + 1 = (Y : ℂ) := by
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    refine ⟨y + 1, Or.inr ⟨(false, y + 1), ?_, rfl⟩, by rw [e]; push_cast; ring⟩
    rw [minusW_eq]
    exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)
  have hOK1 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      (Lw ys w ++ Ww ys w) := by rw [Lw_append_Ww]; exact hW1
  have hOK2 : WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' st p.l0
      ((Lw ys w).map dl ++ Ww ys w) := by
    rw [Lw_dual]
    exact cast_map_pred (len_pm ys w) (fun k u => WordOK (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π' st p.l0 u) _ hW2
  have hDK : FormPairingAction.DKHyp (M.qC (JC.parLev P jF)) (Ww ys w) (Lw ys w) := by
    refine ⟨Lw_plus ys w, good_of_adm st _ hOK1.1, good_of_adm st _ hOK2.1, Lw_pairwise w ys hys, ?_⟩
    intro l hl
    obtain ⟨y, hy, e⟩ := hLmem l hl
    rw [e, qw_Ww]
    intro h0
    have := (hqpos y hy).1
    rw [show qw (M.qC P) (D.positionted w) (y : ℂ) = qw (M.qC (JC.parLev P jF)) (D.positionted w) (y : ℂ) from rfl, h0] at this
    simp at this
  have dk := dk_radial hD hThm Pts hPts (Ww ys w) (Lw ys w) hDK hOK1 hOK2 hP1 hP2 Φ
    (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) hΦU (fun e => hΦ'U _)

  have hRRw : RRw (QQi L st 0) (D.positionted w) ∈ entSub (adjB (Ucls (K 0) (Gen L st Pts)) (bet μ) hU) := by
    refine rrw_mem_at _ _ fun l hl a b => ?_
    unfold D.positionted at hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    refine gen_mem_adjB hThm hS Pts hPts ⟨(w.get i).2, Or.inl ⟨w.get i, ?_, rfl⟩, a, b, rfl⟩
    rw [plusW_eq]; exact List.mem_append_right _ (List.get_mem _ _)
  have hodd := bet_neg (k := (JC.parLev P jF).k) (r := (JC.parLev P jF).r) (z := (p.T.bs jF).z)
    (z' := (p.T.bs jF).z') (π := (p.T.bs jF).π) (π' := (p.T.bs jF).π') μ
  have hmn : w.length ≤ (KB.plusW ys w).length := by rw [len_plusW]; omega
  have ePlus := hform (KB.plusW ys w) x x Φ Φ ε hε hx hx hΦ hΦ
  have eMinus := hform (KB.minusW ys w) x' x' Φ' Φ' ε hε hx' hx' hΦ' hΦ'
  have ePJ := pairJ_rel (w := w) (fun F Ψ => JC.NiceCoef (p.T.bs jF) ε F ∧ IsPic p.T jF Ψ F) (Cst : ℂ)
    (p.form j hj w) (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun u u' v v' hu hu' => hform w u u' v v' ε hε (fun e => (hu e).1) (fun e => (hu' e).1) (fun e => (hu e).2)
      (fun e => (hu' e).2)) ys x x' Φ Φ' (fun e => ⟨hx e, hΦ e⟩) (fun e => ⟨hx' e, hΦ' e⟩)
  have eXi := pairJ_rel (w := w) (fun a b => a = b ∧ a ∈ Ucls (K 0) (Gen L st Pts)) (1 : ℂ)
    (fun u u' => form μ 0 (P5.act (RRi L st 0 (D.positionted w)) u) u' 0)
    (fun x x' => ∑ e, bet μ (actP (RRw (QQi L st 0) (D.positionted w)) x e) (x' e))
    (fun u u' v v' hu hu' => by
      have e1 : u = v := funext fun e => (hu e).1
      have e2 : u' = v' := funext fun e => (hu' e).1
      subst e1 e2
      rw [one_mul]
      have hin : InU (Ucls (K 0) (Gen L st Pts)) (actP (RRw (QQi L st 0) (D.positionted w)) u) :=
        blockMulVec_apply_mem (fun a b x hx => (hRRw a b).1 x hx) (fun e => (hu e).2)
      exact form_zero_eq_position_pairing_of_le hThm hmn _ _ (fun a => hle (hin a)) (fun a => hle (hu' a).2))
    ys Φ Φ' Φ Φ' (fun e => ⟨rfl, hΦU e⟩) (fun e => ⟨rfl, hΦ'U e⟩)
  have ePosition := position_pair (V := RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
    (p.T.bs jF).π (p.T.bs jF).π') (bet μ) hodd (QQi L st 0) w ys Φ Φ'
  have eA : form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.plusW ys w))) Φ) Φ 0 := by rw [Lw_append_Ww]
  have eB : form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 =
      form μ 0 (P5.act (RRi L st 0 (D.positionted (KB.minusW ys w))) Φ') Φ' 0 := by
    rw [Lw_dual]
    show form μ 0 (actP (RRw (QQi L st 0) ((D.positionted (KB.minusW ys w)).map (castL (len_pm ys w))))
      (fun z => Φ' (z ∘ Fin.cast (len_pm ys w)))) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 = _
    have hc := blockMulVec_cast (QQi L st 0) (len_pm ys w) (D.positionted (KB.minusW ys w)) Φ'
    exact (congrArg (fun V => form μ 0 V (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0) hc).trans
      (form_castIx μ (len_pm ys w) _ _ 0)

  obtain ⟨hAi, -, hBi, -, hdk⟩ := dk
  have ePlus' : p.form j hj (KB.plusW ys w) x x =
      (Cst : ℂ) * form μ 0 (P5.act (RRi L st 0 (Lw ys w ++ Ww ys w)) Φ) Φ 0 := ePlus.trans (congrArg _ eA.symm)
  have eMinus' : p.form j hj (KB.minusW ys w) x' x' = (Cst : ℂ) *
      form μ 0 (P5.act (RRi L st 0 ((Lw ys w).map dl ++ Ww ys w)) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))))
        (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) 0 := eMinus.trans (congrArg _ eB.symm)
  have hPJ : KB.pairJ (p.form j hj w) ys x x' = (Cst : ℂ) *
      pairS (bet μ) (actP (JL (Lw ys w) * RRw (QQi L st 0) (Ww ys w)) Φ) (fun z => Φ' (z ∘ Fin.cast (len_pm ys w))) :=
    ePJ.trans (congrArg (fun t => (Cst : ℂ) * t) (eXi.trans ((one_mul _).trans ePosition.symm)))
  have hQ : ((Lw ys w).map fun l => qw (M.qC (JC.parLev P jF)) (Ww ys w) l.pt).prod =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).prod := congrArg List.prod (Lw_qw _ ys w)
  have hre : (ys.map fun y : ℝ => (qw (M.qC P) (D.positionted w) (y : ℂ)).re) =
      (ys.map fun y : ℝ => qw (M.qC P) (D.positionted w) (y : ℂ)).map Complex.re := by
    rw [List.map_map]; rfl
  rw [hPJ, ePlus', eMinus', hre]
  refine final_ineq Cst _ _ _ _ _ hQ (fun z hz => ?_) hAi hBi hdk
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  exact hqpos y hy


end

end GlobalTheory.ListDuality
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder
open Formalism.FourierDecayAlt.P.TBBx5 Filter Topology
open scoped ComplexConjugate ENNReal

namespace GlobalTheory

noncomputable section

open Classical

namespace PlaneWaveCompact

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end PlaneWaveCompact

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma integral_planeWave_eq_lemma_3 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Cb : ℝ)
    (hI : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (j : ℕ) (hj : j ≤ P.r)
    (h : _root_.Formalism.FourierDecayAlt.C.LPt) (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) (s : ℂ) :
    ∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) =
      ((_root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w : ℝ) : ℂ) *
        p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
          (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)) := by
  obtain ⟨φ, -, -, hφ, hint⟩ := _root_.Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hQ _root_.Formalism.FourierDecayAlt.P.radial_head _root_.Formalism.FourierDecayAlt.P.head_top Wp Wq P p F j hj w h h hh hh Cb hI hF hw
  rw [← hint s, ← integral_const_mul]
  apply integral_congr_ae
  have h0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (μ := (volume : Measure ℂ)) (0 : ℂ))
  filter_upwards [h0] with c hc
  rw [hφ c hc, ← _root_.Formalism.FourierDecayAlt.P.TBBx5.wv_np p nn F j hj h hh w c]
  ring

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma shiftedPairing_bound_lemma_4 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hV : _root_.Formalism.FourierDecayAlt.KB.VIsoCpt) (hS : _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt)
    (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y)
    (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt) (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (s : ℂ)
    (ys : List ℝ) (h₁ : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.plusW ys w)) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.minusW ys w))
    (hys : List.Pairwise (fun y y' => 2 < |y - y'|) ys) :
    _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
        ‖_root_.Formalism.FourierDecayAlt.KB.pairJ (p.form j hj w) ys
          (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s (_root_.Formalism.FourierDecayAlt.KB.plusW ys w)
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h (And.right hh)))
          (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h (And.right hh))‖ ≤
      √((ys.map nn).prod * (ys.map fun y : ℝ => nn (y + 1)).prod /
          (ys.map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod) *
        max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h) (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h) := by
  have hx : ∀ e, _root_.Formalism.FourierDecayAlt.KB.CptCoef (p.T.bs j) (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h (And.right hh) e) :=
    fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj _ h hh hF e
  have hx' : ∀ e, _root_.Formalism.FourierDecayAlt.KB.CptCoef (p.T.bs j) (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj (_root_.Formalism.FourierDecayAlt.KB.minusW ys w) h (And.right hh) e) :=
    fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj _ h hh hF e
  obtain ⟨hθ, hbd⟩ := hS hQ Wp Wq P p j hj w ys h₁ h₂ hys
  have hU := hV hQ Wp Wq P p j hj (_root_.Formalism.FourierDecayAlt.KB.plusW ys w) h₁ s _ _ hx hx
  have key := hbd _ _ hU.1 hx'
  rw [hU.2] at key
  have f₁ := (Complex.nonneg_iff.mp (hPos hQ Wp Wq P p j hj _ h₁ _ hx)).1
  have f₂ := (Complex.nonneg_iff.mp (hPos hQ Wp Wq P p j hj _ h₂ _ hx')).1
  have hJL := _root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh
  have hN := _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w
  have hQ₁ := _root_.Formalism.FourierDecayAlt.P.TBBx5.prod_map_pos nn hnn ys
  have hQ₂ := _root_.Formalism.FourierDecayAlt.P.TBBx5.prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
  have hq : 0 < (ys.map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact hθ y hy
  have hα : 0 ≤ _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w := div_nonneg hJL hN.le
  have hcs := _root_.Formalism.FourierDecayAlt.P.TBBx5.scal_cs _ _ _ _ _ _ _ _ _ hα (by ring) hα hα hq hQ₁ hQ₂ (norm_nonneg _) f₁ f₂ key
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [_root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj _ h hh, _root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj _ h hh, _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_plusW, _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_minusW]
  refine le_trans (le_of_eq ?_) (_root_.Formalism.FourierDecayAlt.P.TBBx5.sqrt_mul_le_max _ _ ?_ ?_)
  · congr 1 <;> field_simp
  · exact mul_nonneg (div_nonneg hJL (mul_pos hQ₁ hN).le) f₁
  · exact mul_nonneg (div_nonneg hJL (mul_pos hQ₂ hN).le) f₂

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma planeWave_grid_bound_lemma (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hV : _root_.Formalism.FourierDecayAlt.KB.VIsoCpt) (hS : _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt)
    (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Cb : ℝ) (hI : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt)
    (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) (s : ℂ) (K : ℕ)
    (grid : Fin K → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hcut : ∀ n : Fin K → Fin (2 * j + 1),
      _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) ∧ _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) ∧
        List.Pairwise (fun y y' => 2 < |y - y'|) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)) :
    ‖s‖ ^ K *
        ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      ∑ n, |∏ a, _root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) (n a)| *
        (√(((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map nn).prod * ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => nn (y + 1)).prod /
            ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod) *
          max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)
            (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)) := by
  have hα : 0 ≤ _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w :=
    div_nonneg (_root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh) (_root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w).le
  have hdeg := _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave Wp Wq P p F j hj w h h hh hh K grid s LinearMap.id
    (fun _ _ hx e => hx e) hF hinj
  simp only [LinearMap.id_apply, _root_.Formalism.FourierDecayAlt.P.PBL.onOld_id] at hdeg
  rw [integral_planeWave_eq_lemma_3 hQ P p nn F Cb hI hF j hj h hh w hw s, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hα]
  calc ‖s‖ ^ K * (_root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
          ‖p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh))‖)
      = _root_.Formalism.FourierDecayAlt.C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / _root_.Formalism.FourierDecayAlt.TBB.normC nn w *
          ‖s ^ K * p.form j hj w (_root_.Formalism.FourierDecayAlt.KB.waveG (p.T.bs j) s w (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh)))
            (_root_.Formalism.FourierDecayAlt.KB.slv p.T F j hj w h (And.right hh))‖ := by
        rw [norm_mul, norm_pow]; ring
    _ ≤ _ := by
        rw [hdeg]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hα).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (shiftedPairing_bound_lemma_4 hQ hV hS hPos P p nn F hF hnn j hj h hh w s _
            (hcut n).1 (hcut n).2.1 (hcut n).2.2) (abs_nonneg _)

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in
private lemma normalizedWeight_nonneg_lemma_2 (hQ : _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt) (hPos : _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par)
    (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (j : ℕ) (hj : j ≤ P.r) (h : _root_.Formalism.FourierDecayAlt.C.LPt)
    (hh : _root_.Formalism.FourierDecayAlt.D.IsLocPt h j) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w) :
    0 ≤ _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j w h := by
  rw [_root_.Formalism.FourierDecayAlt.P.TBBx5.wv_ew p nn F j hj w h hh]
  have h1 := _root_.Formalism.FourierDecayAlt.P.TBBx5.weighted_auxiliary_norm_nonneg P j hj h hh
  have h2 := _root_.Formalism.FourierDecayAlt.P.TBBx5.normC_pos nn hnn w
  have h3 := hPos hQ Wp Wq P p j hj w hw _ (fun e => _root_.Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e)
  exact mul_nonneg (div_nonneg h1 h2.le) (Complex.nonneg_iff.mp h3).1

open NumberField MeasureTheory in
open scoped ComplexOrder in
open Filter Topology in
open scoped ComplexConjugate ENNReal in
open Classical in

theorem _root_.GlobalTheory.planeWave_bound_of_xiExists (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) :
    _root_.Formalism.FourierDecayAlt.P5.ThmPActualCpt → _root_.Formalism.FourierDecayAlt.KB.VIsoCpt → _root_.Formalism.FourierDecayAlt.KB.SizeStdCpt → _root_.Formalism.FourierDecayAlt.P.PBL.FormPosCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb : ℝ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid p nn Y Λ K N → _root_.Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound p nn F Y Λ K N := by
  intro hQ hV hS hPos Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N Cb hI hF hnn hgrid
  unfold _root_.Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound
  intro j hj h hh w hw hlen s
  have hw0 : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w := by
    unfold _root_.Formalism.FourierDecayAlt.TBB.AdmW at hw
    exact hw.1
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid at hgrid
  obtain ⟨grid, hg⟩ := hgrid j hj w hw hlen
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK at hg
  obtain ⟨hinj, hmem, hcut, hsum⟩ := hg

  have hE₁ : ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j w h := by
    have hnil : ∀ n : Fin 0 → Fin (2 * j + 1),
        _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf (fun a => Fin.elim0 a : Fin 0 → Fin (2 * j + 1) → ℝ) n = [] :=
      fun n => List.ofFn_zero
    have hb := planeWave_grid_bound_lemma hQ hV hS hPos P p nn F Cb hI hF hnn j hj h hh w hw0 s 0
      (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
      (fun n => by simp only [hnil, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq, List.map_nil, List.nil_append]; exact ⟨hw0, hw0, List.Pairwise.nil⟩)
    simpa [hnil, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq] using hb

  obtain ⟨n₀, hn₀⟩ := _root_.Formalism.FourierDecayAlt.P.TBBx5.sum_le_max
    (fun n => |∏ a, _root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) (n a)| *
      √(((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map nn).prod * ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => nn (y + 1)).prod /
          ((_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n).map fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re).prod))
    (fun n => max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h)
      (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) w) h))
    (Λ ^ K) (fun n => by positivity)
    (fun n => le_max_of_le_left
      (normalizedWeight_nonneg_lemma_2 hQ hPos P p nn F hF hnn j hj h hh _ (hcut n).1)) hsum
  have hE₂ : 0 < ‖s‖ → ‖s‖ ^ K *
      ‖∫ c : ℂ, _root_.Formalism.FourierDecayAlt.P5.fsv s c * _root_.Formalism.FourierDecayAlt.TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      Λ ^ K * max (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h)
        (_root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h) := fun _ =>
    (planeWave_grid_bound_lemma hQ hV hS hPos P p nn F Cb hI hF hnn j hj h hh w hw0 s K grid hinj
      hcut).trans (by simpa only [mul_assoc] using hn₀)
  have hlenK : (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀).length = K := List.length_ofFn
  rcases _root_.Formalism.FourierDecayAlt.P.TBBx5.mn_pick Λ ‖s‖ _ _ _ K (norm_nonneg s) hE₁ hE₂ with H | H
  · exact ⟨w, _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_self P p.l0 Y N K w hw (by omega), H⟩
  · by_cases hm : _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h ≤
        _root_.Formalism.FourierDecayAlt.TBB.Ew p nn F j (_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w) h
    · refine ⟨_root_.Formalism.FourierDecayAlt.KB.plusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w,
        _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_plusW P p.l0 Y N K w _ hlen hlenK (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf_mem grid hmem n₀) (hcut n₀).1, ?_⟩
      rwa [max_eq_left hm] at H
    · refine ⟨_root_.Formalism.FourierDecayAlt.KB.minusW (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n₀) w,
        _root_.Formalism.FourierDecayAlt.P.TBBx5.isExt_minusW P p.l0 Y N K w _ hlen hlenK (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf_mem grid hmem n₀) (hcut n₀).2.1, ?_⟩
      rwa [max_eq_right (le_of_not_ge hm)] at H

end

end GlobalTheory
end

section
namespace GlobalTheory.LiftBoundCpt

noncomputable section

open Matrix Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

section step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (τ τ' : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j)
  (ha' : D.ptSize (h' ++ [(s, τ')]) = j)

theorem lift_pairing_poly (hXi : B.XiExists) (hs : 1 ≤ s) (hsj : s ≤ j)
    (hSP : SlicePoly p.T F j hj (h ++ [(s, τ)]) ha) (hSP' : SlicePoly p.T F j hj (h' ++ [(s, τ')]) ha')
    (hLD : LiftDeg p.T F j s hj h τ ha) (hLD' : LiftDeg p.T F j s hj h' τ' ha')
    (hN : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h ++ [(s, τ)]) ha a''))
    (hN' : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h' ++ [(s, τ')]) ha' a''))
    (ys : List ℝ) :
    ∃ c : Fin (2 * (j - s) + s + 1) → ℂ,
      c (Fin.last (2 * (j - s) + s)) = ((-1 : ℂ) ^ (s - 1) * (τ⁻¹ - τ'⁻¹)) * Wl p F j s hj w h h' τ τ' ha ha' ys ∧
      ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) = ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * c q := by
  classical
  set Ξ := p.form j hj w with hΞ
  have hΞ' : Ξ = D.formLev p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w := rfl
  obtain ⟨C0, hC0l, hC0n, hC0⟩ := hSP (KB.plusW ys w) true 0 0
  obtain ⟨D0, hD0l, hD0n, hD0⟩ := hSP' (KB.minusW ys w) false 1 0
  obtain ⟨E, hEn, hE0, hEt, hEJ⟩ := reduceJ p.T F j s hj h τ ha hsj hSP hLD (KB.plusW ys w) (hN _) true 0
  obtain ⟨E', hE'n, hE'0, hE't, hE'J⟩ := reduceJ p.T F j s hj h' τ' ha' hsj hSP' hLD' (KB.minusW ys w) (hN' _) false 1
  have dC0 : ∀ l, DecV (C0 l) := fun l => by obtain ⟨ε, hε⟩ := hC0n l; exact decV_of_nice hε
  have dD0 : ∀ l, DecV (D0 l) := fun l => by obtain ⟨ε, hε⟩ := hD0n l; exact decV_of_nice hε
  have dE : ∀ l, DecV (E l) := fun l => by obtain ⟨ε, hε⟩ := hEn l; exact decV_of_nice hε
  have dE' : ∀ l, DecV (E' l) := fun l => by obtain ⟨ε, hε⟩ := hE'n l; exact decV_of_nice hε
  have zL : ∀ (y' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV y' →
      KB.pairJ Ξ ys 0 y' = 0 := by
    intro y' hy
    have := FormsFromXi.pairing_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y' 1 decV_zero decV_zero hy
    rw [one_smul, add_zero, one_mul, ← hΞ'] at this
    linear_combination -this
  have zR : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
      KB.pairJ Ξ ys x 0 = 0 := by
    intro x hx
    have := FormsFromXi.pairing_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
    rw [one_smul, add_zero, map_one, one_mul, ← hΞ'] at this
    linear_combination -this

  have hX : ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) =
      ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) := by
    intro y
    show KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) -
      KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) = _
    have hy0 : ((true, y) : C.Letter) = (true, y + 0) := by rw [add_zero]

    obtain ⟨εa, hεa⟩ := hN ((true, y) :: KB.plusW ys w)
    obtain ⟨εb, hεb⟩ := nice_lincomb (Bs := p.T.bs j) E hEn (fun l : Fin (j + 1) => (y : ℂ) ^ (l : ℕ))
    have t1 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • D0 m) := by
      rw [hΞ', pairJ_congrJ_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w (min εa εb) ys _
        (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) _
        (fun a => nice_mono (hεa _) (min_le_left _ _)) (fun a => nice_mono (hεb a) (min_le_right _ _))
        (fun a g hg => by have := hEJ y a g hg; rwa [add_zero] at this)]
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ (eqGV_refl _) (hD0 y)
    have t2 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • C0 l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) := by
      rw [hΞ', pairJ_congrJ_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _
        (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) (fun a g hg => hE'J y a g hg)]
      have h0 := hC0 y
      rw [add_zero] at h0
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ h0 (eqGV_refl _)
    rw [t1, t2, hΞ', FormsFromXi.pairing_sum_sum hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ E D0 dE dD0,
      FormsFromXi.pairing_sum_sum hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ C0 E' dC0 dE', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [conj_tpow]
    ring
  set N := 2 * (j - s) + s with hNdef
  have hNj : N = 2 * j - s := by omega
  set P1 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (E l) (D0 m) with hP1
  set P2 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (C0 l) (E' m) with hP2
  have P1z : ∀ l m : Fin (j + 1), j - s < (l : ℕ) → P1 l m = 0 := by
    intro l m hl; simp only [hP1]; rw [hE0 l hl]; exact zL _ (dD0 m)
  have P2z : ∀ l m : Fin (j + 1), j - s < (m : ℕ) → P2 l m = 0 := by
    intro l m hm; simp only [hP2]; rw [hE'0 m hm]; exact zR _ (dC0 l)
  have Xz : ∀ l m : Fin (j + 1), N < (l : ℕ) + m → P1 l m - P2 l m = 0 := by
    intro l m hlm
    have := l.isLt; have := m.isLt
    rw [P1z l m (by omega), P2z l m (by omega), sub_zero]
  refine ⟨fun q => ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = q then P1 l m - P2 l m else 0, ?_,
    fun y => ?_⟩
  · dsimp only
    simp only [Fin.val_last]
    have hsplit : ∀ l m : Fin (j + 1), (if (l : ℕ) + m = N then P1 l m - P2 l m else 0) =
        (if (l : ℕ) + m = N then P1 l m else 0) - (if (l : ℕ) + m = N then P2 l m else 0) := by
      intro l m; split_ifs <;> simp
    simp only [hsplit, Finset.sum_sub_distrib]
    have hA : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P1 l m else 0) =
        P1 ⟨j - s, by omega⟩ (Fin.last j) := by
      rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
      · rw [Finset.sum_eq_single (Fin.last j)]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j - s := fun e => hl (Fin.ext (by simp [e]))
          exact P1z l m (by omega)
        · rfl
      · simp
    have hB : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P2 l m else 0) =
        P2 (Fin.last j) ⟨j - s, by omega⟩ := by
      rw [Finset.sum_eq_single (Fin.last j)]
      · rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j - s := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j := fun e => hl (Fin.ext (by simp [e]))
          exact P2z l m (by omega)
        · rfl
      · simp
    rw [hA, hB]
    have dXP : DecV (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) := by
      obtain ⟨ε, hε⟩ := hN (KB.plusW ys w); exact decV_of_nice hε
    have dXM : DecV (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') := by
      obtain ⟨ε, hε⟩ := hN' (KB.minusW ys w); exact decV_of_nice hε
    have e1 : P1 ⟨j - s, by omega⟩ (Fin.last j) = cLift s τ true * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP1]
      rw [hEt, hD0l, if_pos rfl]
      have := FormsFromXi.pairing_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ true) decV_zero dXP dXM
      rw [zero_add, ← hΞ', zL _ dXM, zero_add] at this
      rw [this]; rfl
    have e2 : P2 (Fin.last j) ⟨j - s, by omega⟩ = conj (cLift s τ' false) * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP2]
      rw [hE't, hC0l, if_pos rfl]
      have := FormsFromXi.pairing_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) 0
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ' false) dXP decV_zero dXM
      rw [zero_add, ← hΞ', zR _ dXP, zero_add] at this
      rw [this]; rfl
    rw [e1, e2]
    simp only [cLift, if_true, Bool.false_eq_true, if_false, map_mul, map_pow, map_neg, map_one, map_inv₀,
      Complex.conj_conj]
    ring
  · rw [hX y]
    have key : ∀ l m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) =
        ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * (if (l : ℕ) + m = q then P1 l m - P2 l m else 0) := by
      intro l m
      by_cases hlm : (l : ℕ) + m ≤ N
      · rw [Finset.sum_eq_single ⟨(l : ℕ) + m, by omega⟩]
        · rw [if_pos rfl, pow_add]
        · intro q _ hq
          rw [if_neg, mul_zero]
          intro e
          exact hq (Fin.ext e.symm)
        · simp
      · have hz := Xz l m (by omega)
        simp only [hP1, hP2] at hz
        rw [hz, mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg, mul_zero]
        have := q.isLt
        omega
    simp only [key]
    refine (Finset.sum_congr rfl (fun l _ => Finset.sum_comm)).trans ?_
    refine Finset.sum_comm.trans ?_
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]

end step

theorem degLift_of_liftDeg (hXi : B.XiExists) (hL : LiftDegAll) : KB.DegLift := by
  intro Wp Wq _ _ _ _ _ _ P p F j s hj w h h' t t' ha ha' K grid hF hgrid
  have hsz : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s t
  have hs1 : 1 ≤ s := (ha.1 (s, t) (by simp)).1
  have hsj : s ≤ j := by rw [← ha.2, hsz]; omega
  have hN : ∀ (q : C.LPt) (hq : D.IsLocPt q j) (w' : List C.Letter), ∃ ε, ∀ a'',
      JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' q hq.2 a'') := fun q hq w' =>
    nice_vec_of_cpt (p.T.bs j) (fun a'' => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w' q hq hF a'')
  set W : ℕ → (Fin K → ℝ) → ℂ := fun m y => Wl p F j s hj w h h' t t' ha.2 ha'.2 (Lst K m y) with hW
  have hPS : F7.PolyStep K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W := by
    intro a y
    obtain ⟨c, hc, hcs⟩ := lift_pairing_poly p F j s hj w h h' t t' ha.2 ha'.2 hXi hs1 hsj
      (slicePolyAll Wp Wq P p F hF j hj _ ha) (slicePolyAll Wp Wq P p F hF j hj _ ha')
      (hL Wp Wq P p F hF j s hj h t ha) (hL Wp Wq P p F hF j s hj h' t' ha') (hN _ ha) (hN _ ha') (Lst K a y)
    refine ⟨c, ?_, fun u => ?_⟩
    · rw [hc, smul_eq_mul]
    · simp only [hW]
      rw [lst_succ, hcs u]
      simp only [smul_eq_mul]
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound ℂ K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hE
  have hW0 : W 0 (fun _ => 0) = p.RR F j w (h ++ [(s, t)]) (h' ++ [(s, t')]) := by
    simp only [hW, KB.Pl.RR, D.RRplace, dif_pos (And.intro ha ha'), dif_pos hj]
    rfl
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW, smul_eq_mul]
  rw [lst_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2]
  rfl

theorem degLift_of_xiExists (hXi : B.XiExists) : KB.DegLift :=
  degLift_of_liftDeg hXi (liftDegAll_of left_fubini_normalized_tower LeftFubiniLemmas.normal_form_left_hypothesis right_average_smooth_comm)

end

end GlobalTheory.LiftBoundCpt

namespace GlobalTheory.LiftBoundCpt

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx5 Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem form_cauchySchwarz (hXi : B.XiExists) (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) :
    ‖p.form j hj w x y‖ ^ 2 ≤ (p.form j hj w x x).re * (p.form j hj w y y).re := by
  let VT := Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)
  have hadd : ∀ x y : VT, PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) y → PBL.CV (p.T.bs j) (x + y) :=
    fun _ _ => PBL.cv_add
  have hsmul : ∀ (c : ℂ) (x : VT), PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) (c • x) := fun c _ => PBL.cv_smul c
  have hl : ∀ (x₁ x₂ y : VT) (c : ℂ), PBL.CV (p.T.bs j) x₁ → PBL.CV (p.T.bs j) x₂ → PBL.CV (p.T.bs j) y →
      p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
    fun x₁ x₂ y c h₁ h₂ h₃ => by
      obtain ⟨ε, -, a, b, d⟩ := PBL.exists_norm_bound_three_families h₁ h₂ h₃
      exact FormsFromXi.formLev_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c
        (PBG.decV_of_nice a) (PBG.decV_of_nice b) (PBG.decV_of_nice d)
  have hr : ∀ (x y₁ y₂ : VT) (c : ℂ), PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) y₁ → PBL.CV (p.T.bs j) y₂ →
      p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
    fun x y₁ y₂ c h₁ h₂ h₃ => by
      obtain ⟨ε, -, a, b, d⟩ := PBL.exists_norm_bound_three_families h₁ h₂ h₃
      exact FormsFromXi.formLev_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c
        (PBG.decV_of_nice a) (PBG.decV_of_nice b) (PBG.decV_of_nice d)
  have hp : ∀ x : VT, PBL.CV (p.T.bs j) x → 0 ≤ p.form j hj w x x :=
    fun x hx => hFP hA Wp Wq P p j hj w hw x hx
  refine cs_abs (PBL.CV (p.T.bs j)) (p.form j hj w) hadd hsmul hl hr hp x y hx hy ?_
  exact PBL.herm_of_nonneg (PBL.CV (p.T.bs j)) (p.form j hj w) PBL.cv_zero hadd hsmul hl hr hp x y hx hy

theorem form_re_nonneg_cpt (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : PBL.CV (p.T.bs j) x) :
    0 ≤ (p.form j hj w x x).re :=
  (Complex.nonneg_iff.1 (hFP hA Wp Wq P p j hj w hw x hx)).1

theorem slice_cv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    PBL.CV (p.T.bs j) (KB.slv p.T F j hj w a ha.2) :=
  fun e => slice_compact_support_coefficient _ _ P p F j hj w a ha hF e

theorem liftBound_at (hXi : B.XiExists) (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : LiftGrid p nn Y Λ K N) :
    TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := by
  intro b s hb hs hbs h hh w hw hN t t' ht ht'
  set j := b + s - 1 with hjdef
  have hj : j ≤ P.r := hbs
  obtain ⟨grid, hinj, hY, hcut, hsum⟩ := hgrid b s hb hs hbs w hw hN
  simp only [ysOf] at hsum hcut
  have ha := li_locPt h b s t hb hs hh ht
  have ha' := li_locPt h b s t' hb hs hh ht'
  set u := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) with hudef
  set u' := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) with hu'def
  set n := TBB.normC nn w with hndef
  have hn : 0 < n := normC_pos nn hnn w
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu' : 0 ≤ u' := Real.sqrt_nonneg _
  have hα : 0 ≤ u * u' / n := by positivity
  set x := KB.slv p.T F j hj w _ ha.2 with hxdef
  set x' := KB.slv p.T F j hj w _ ha'.2 with hx'def
  have hNP : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ = (u * u' / n) * ‖p.form j hj w x x'‖ := by
    rw [li_np p nn F j hj w _ _ ha ha', norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]

  have c1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2 := by
    have hx : PBL.CV (p.T.bs j) x := slice_cv p hF j hj w _ ha
    have hx' : PBL.CV (p.T.bs j) x' := slice_cv p hF j hj w _ ha'
    have hcs := form_cauchySchwarz hXi hA hFP p j hj w hw.1 x x' hx hx'
    have hf := form_re_nonneg_cpt hA hFP p j hj w hw.1 x hx
    have hf' := form_re_nonneg_cpt hA hFP p j hj w hw.1 x' hx'
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) ‖p.form j hj w x x'‖ 1 1 1
      (p.form j hj w x x).re (p.form j hj w x' x').re hα (by field_simp) (by positivity) (by positivity)
      one_pos one_pos one_pos (norm_nonneg _) hf hf' (by rw [mul_one]; exact hcs)
    rw [hNP, li_ew p nn F j hj w _ ha, li_ew p nn F j hj w _ ha']
    refine key.trans ?_
    simp only [mul_one, div_one, Real.sqrt_one, one_mul]
    exact sqrt_mul_le_avg _ _ (mul_nonneg (by positivity) hf) (mul_nonneg (by positivity) hf')

  have hEnn : ∀ (w' : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j), KB.CutWord P p.l0 w' →
      0 ≤ TBB.Ew p nn F j w' a := by
    intro w' a ha hw'
    rw [li_ew p nn F j hj w' a ha]
    have hxa := slice_cv p hF j hj w' a ha
    exact mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le)
      (form_re_nonneg_cpt hA hFP p j hj w' hw' _ hxa)

  have hdeg := degLift_of_xiExists hXi Wp Wq P p F j s hj w h h t t' ha ha' K grid hF hinj
  rw [PBL.rr_eq_form p F j hj w _ _ ha ha'] at hdeg
  have hper : ∀ m : Fin K → Fin (2 * (j - s) + s + 1),
      (u * u' / n) * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
          (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ ≤
        Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
          ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
          ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
        ((TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
          TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2) := by
    intro m
    set ys := List.ofFn fun a => grid a (m a) with hys
    obtain ⟨hqpos, hSSm⟩ := hSS hA Wp Wq P p j hj w ys (hcut m).1 (hcut m).2.1 (hcut m).2.2
    have hx := slice_cv p hF j hj (KB.plusW ys w) _ ha
    have hx' := slice_cv p hF j hj (KB.minusW ys w) _ ha'
    have hcs := hSSm _ _ hx hx'
    set fp := (p.form j hj (KB.plusW ys w) (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)
      (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)).re with hfp
    set fm := (p.form j hj (KB.minusW ys w) (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)
      (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)).re with hfm
    have hf : 0 ≤ fp := form_re_nonneg_cpt hA hFP p j hj _ (hcut m).1 _ hx
    have hf' : 0 ≤ fm := form_re_nonneg_cpt hA hFP p j hj _ (hcut m).2.1 _ hx'
    have hq : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      refine List.prod_pos fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hqpos y hy
    have hQ₁ := prod_map_pos nn hnn ys
    have hQ₂ := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) _ _ _ _ fp fm hα (by field_simp) (by positivity)
      (by positivity) hq hQ₁ hQ₂ (norm_nonneg _) hf hf' hcs
    refine key.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [li_ew p nn F j hj _ _ ha, li_ew p nn F j hj _ _ ha', normC_plusW, normC_minusW, ← hfp, ← hfm]
    have e₁ : u * u / n * fp / (ys.map nn).prod = u * u / ((ys.map nn).prod * n) * fp := by
      field_simp
    have e₂ : u' * u' / n * fm / (ys.map fun y => nn (y + 1)).prod =
        u' * u' / ((ys.map fun y => nn (y + 1)).prod * n) * fm := by
      field_simp
    rw [e₁, e₂]
    exact sqrt_mul_le_avg _ _ (by positivity) (by positivity)
  set g : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun m =>
    (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
      TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2 with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m =>
    div_nonneg (add_nonneg (hEnn _ _ ha (hcut m).1) (hEnn _ _ ha' (hcut m).2.1)) zero_le_two
  obtain ⟨m₀, hm₀⟩ := sum_le_max (fun m => |∏ a, F7.lagCo (grid a) (m a)| *
      Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
        ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    g (Λ ^ K) (fun m => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hg0 hsum
  have c2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤ Λ ^ K * g m₀ := by
    have hn1 : ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ =
        ‖t⁻¹ - t'⁻¹‖ ^ K * ‖p.form j hj w x x'‖ := by
      rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hNP]
    calc ‖t⁻¹ - t'⁻¹‖ ^ K * (u * u' / n * ‖p.form j hj w x x'‖)
        = u * u' / n * ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ := by rw [hn1]; ring
      _ ≤ u * u' / n * ∑ m : Fin K → Fin (2 * (j - s) + s + 1), ‖((∏ a, F7.lagCo (grid a) (m a) : ℝ) : ℂ)‖ *
          ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hα
          rw [hdeg]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => norm_mul _ _
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (u * u' / n * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hper m) (abs_nonneg _)
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m := Finset.sum_congr rfl fun m _ => by ring
      _ ≤ Λ ^ K * g m₀ := hm₀
  rcases mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ (g m₀) K (norm_nonneg _) c1 (fun _ => c2) with hc | hc
  · exact ⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), hc⟩
  · refine ⟨KB.plusW (List.ofFn fun a => grid a (m₀ a)) w, KB.minusW (List.ofFn fun a => grid a (m₀ a)) w,
      isExt_plusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).1,
      isExt_minusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).2.1, hc⟩

end

theorem liftBound_of_xiExists (hXi : B.XiExists) : P5.ThmPActualCpt → KB.SizeStdCpt → PBL.FormPosCpt →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
      KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → TBBx5.LiftGrid p nn Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N :=
  fun hA hSS hFP _ _ _ _ _ _ _ _ _ p nn F Y Λ K N hF hnn hgrid =>
    liftBound_at hXi hA hSS hFP p nn F Y Λ K N hF hnn hgrid

end GlobalTheory.LiftBoundCpt
end

section
namespace GlobalTheory.PointwiseBound

noncomputable section

section Wave

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants

theorem uInv_eq_zero {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (s : ℂ) (g : Y) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Y → Z) (e : Wd.Ix (Fin w.length)),
      (∀ a, x a g = 0) → KB.uInv s w x e g = 0
  | [], _, e, h => h e
  | l :: w, x, e, h => by
    have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _)
    have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _)
    simp only [KB.uInv]
    by_cases h : e 0 = 0
    · simp only [if_pos h]
      exact h0
    · simp only [if_neg h, Pi.add_apply, Pi.smul_apply]
      rw [h0, h1, smul_zero, add_zero]

theorem waveG_cptCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef Bs (x e))
    (e : Wd.Ix (Fin w.length)) : KB.CptCoef Bs (KB.waveG Bs s w x e) := by
  obtain ⟨ε, hε, hn⟩ := PBL.nv_of_cv (Bs := Bs) (x := x) hx
  have hw := PBFV.waveG_nice Bs ε s w x hn e
  refine ⟨hw.1, ?_, ε, hε, hw.2.2⟩
  choose R hR using fun a => (hx a).2.1
  refine ⟨∑ a, |R a|, fun g hg hne => ?_⟩
  by_cases h0 : ∀ a, x a g = 0
  · exact absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne
  · push Not at h0
    obtain ⟨a, ha⟩ := h0
    exact ((hR a g hg ha).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))

theorem waveIsometry_of_radial (hRad : JC.RadialModuleForm) : KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'
  refine ⟨waveG_cptCoef _ s w x hx, ?_⟩
  obtain ⟨ε, hε, a, b, -⟩ := PBL.exists_norm_bound_three_families (Bs := p.T.bs j) (x := x) (y := x') (z := x) hx hx' hx
  exact GlobalTheory.WaveIsometry.isometry_of_bounded hRad hP Wp Wq P p j hj w hw s x x' ε hε a b
    (fun e => (hx e).2.1) (fun e => (hx' e).2.1) (fun e => (waveG_cptCoef _ s w x' hx' e).2.1)

end Wave

section Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem extension_at_zero (hXi : B.XiExists) (hP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := PBO.pStd_cpt_of_parts hP (FormsFromXi.radHead hXi) head_top
    (FormsFromXi.form_const_one hXi) exists_zeta_normalized_haar Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

end

end GlobalTheory.PointwiseBound
end
