import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaIntegrandIntegrableOfXiExists

section
open MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.WeightedFormPos

open Formalism.FourierDecayAlt.P.JCx2 in

theorem radialBetaPos_of_xiExists (hXi : B.XiExists) : JC.RadialBetaPos := by
  intro Wp Wq _ _ _ _ _ _ P0 T j μ hμ
  obtain ⟨C1, hC1, hpair⟩ := rb_pairAt (T.bs j) μ hμ
  refine ⟨C1⁻¹, inv_pos.2 hC1, fun n x x' Φ Φ' ε _ hx hx' hΦ hΦ' => ?_⟩
  have h : P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta (T.bs j) (x a) (x' a) := by
    refine (rb_form_eq (k := P0.k) (r := P0.r - j) μ Φ Φ').trans ?_
    let f : Wd.Ix (Fin n) → (Fin (P0.r - j) → ℂ) × ℂ → ℂ := fun a q =>
      (bcWeight P0.k (P0.r - j) (Tz P0.k (P0.r - j) (T.bs j).z) (Tz P0.k (P0.r - j) (T.bs j).z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF (T.bs j) (x' a) (B.gq (T.bs j) q))) (B.hsVec (B.JF (T.bs j) (x a) (B.gq (T.bs j) q)))
    have hint : ∀ a, Integrable (f a) := fun a =>
      betaIntegrand_integrable_of_xiExists hXi P0.k (P0.r - j) Wp Wq (T.bs j) _ (x a) (x' a) le_rfl
        ((hx a).2.1 _ 5) ((hx' a).2.1 _ 5)
    have hae : (fun c : Fin (P0.r - j) → ℂ => ((∏ a : Fin (P0.r - j), ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ b, P5.pairAt (k := P0.k) (r := P0.r - j) μ (Φ b) (Φ' b) c)
        =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
      filter_upwards [rb_ae_OmX] with c hc
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [rb_weight hc]
      rfl
    refine (integral_congr_ae hae).trans ?_
    rw [integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, ← integral_prod _ (hint b)]
    rfl
  rw [h]
  have hC : (C1 : ℂ) ≠ 0 := by exact_mod_cast hC1.ne'
  push_cast
  field_simp

theorem radialModuleForm_of_xiExists (hXi : B.XiExists) : JC.RadialModuleForm :=
  radial_module_form_of_parts (radialBetaPos_of_xiExists hXi) radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end GlobalTheory.WeightedFormPos
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory.WeightedFormPos

open Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q in

theorem form_nonneg_of_cptCoef (hXi : B.XiExists) (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hc : KB.CutWord P p.l0 w) (x : Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hxc : ∀ e, KB.CptCoef (p.T.bs j) (x e)) : 0 ≤ p.form j hj w x x := by
  obtain ⟨ε, hε, hx⟩ := PBL.nv_of_cv (Bs := p.T.bs j) (x := x) hxc
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := radialModuleForm_of_xiExists hXi Wp Wq P p.T jF X μ L st p.l0 hD
  have hpic := fun a => (hxc a).2.1.elim fun R hR =>
    PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJ hε (hx a) (R := R) hR
  choose Φ hΦK hΦ using hpic
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hx hx hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

theorem posAt_of_cptCoef_of_xiExists (hXi : B.XiExists) : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), (∀ y, 0 ≤ nn y) → KB.CptCoef p.T.base F → TBB.PosAt p nn F Y N := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N hnn hF
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p F j hj w h h hh hh]
    have h0 := form_nonneg_of_cptCoef hXi hA P p j hj w hw.1 _
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e)
    exact (Complex.nonneg_iff.1 h0).1
  · unfold KB.Pl.RR D.RRplace
    rw [dif_neg (fun h1 => hh h1.1)]
    simp

theorem formPosCpt_of_xiExists (hXi : B.XiExists) : PBL.FormPosCpt :=
  fun hP _ _ _ _ _ _ _ _ P p j hj w hc x hx => form_nonneg_of_cptCoef hXi hP P p j hj w hc x hx

end GlobalTheory.WeightedFormPos
end
