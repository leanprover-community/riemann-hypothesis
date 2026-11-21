import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem fockVarEquiv_lt {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : k < m) (hk : k < Dw.p) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨k, h⟩, c) = (tauPsi hΨ ρ, Sum.inl ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

theorem fockVarEquiv_ge {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : Dw.p + k < m) (hk : k < Dw.q) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨Dw.p + k, h⟩, c) = (tauPsi hΨ ρ, Sum.inr ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_minorPlus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.p) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) := by
  rw [minorPlus, GlobalTheory.Harm.xMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.Harm.baseCovec, GlobalTheory.Harm.xForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_lt Dw hΨ hm ρ _ _ (by omega)]
  rfl

theorem rename_minorMinus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.q) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : GlobalTheory.Harm.Poly ℂ _ Dw.p Dw.q (Fin n)) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) := by
  rw [minorMinus, GlobalTheory.Harm.yMinor, AlgHom.map_det, ← Matrix.det_permute']
  conv_lhs => rw [← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id, GlobalTheory.Harm.baseVec, GlobalTheory.Harm.yForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_ge Dw hΨ hm ρ _ _ (by omega)]
  refine congrArg MvPolynomial.X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  simp only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_delta_eq_smul_basePoly : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  intro D H Dw m n hΨ hm w a hw hn
  have hp : ∀ ρ, w.p ρ = Dw.p := fun ρ => (hw ρ).1
  have hq : ∀ ρ, w.q ρ = Dw.q := fun ρ => (hw ρ).2.1
  refine ⟨∏ ρ : D.what₂.Tau, ∏ i : Fin Dw.q,
    (((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i, ?_⟩
  rw [GlobalTheory.ExportSeries.Weight.delta, Datum.delta, map_prod, GlobalTheory.Harm.basePoly, GlobalTheory.Harm.minorProd, map_prod,
    ← (tauPsi hΨ).prod_comp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [deltaAt, hp ρ, hq ρ, map_mul, map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  have hx : ∀ i : Fin Dw.p, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.ap ρ i - if i.val + 1 < Dw.p then w.ap ρ (i.val + 1) else 0)) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) ^ stepsX Dw a (tauPsi hΨ ρ) i := by
    intro i
    rw [map_pow, rename_minorPlus Dw hΨ hm hn ρ i]
    congr 1
    simp only [stepsX, GlobalTheory.Harm.diffOf, tauPsi_apply]
    rw [(hw ρ).2.2.1 i i.isLt]
    split_ifs with h1
    · rw [(hw ρ).2.2.1 _ h1]
    · rfl
  have hy : ∀ i : Fin Dw.q, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0)) =
      MvPolynomial.C ((((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) ^ stepsY Dw a (tauPsi hΨ ρ) i := by
    intro i
    have he : (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0) = stepsY Dw a (tauPsi hΨ ρ) i := by
      simp only [stepsY, GlobalTheory.Harm.diffOf, tauPsi_apply]
      have e0 : ∀ j < Dw.q, a (ComplexEmbedding.conjugate (tauE D ρ), j) = w.am ρ j := (hw ρ).2.2.2
      rw [e0 i i.isLt]
      split_ifs with h1
      · rw [e0 _ h1]
      · rfl
    rw [map_pow, rename_minorMinus Dw hΨ hm hn ρ i, he, mul_pow, map_pow, map_intCast]
  simp only [hx, hy, Finset.prod_mul_distrib, map_prod]
  ring

end GlobalTheory.FockLetters
end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_delta_base_polynomial : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  atlas_forward_decl GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem rename_fockGL_eq_C_mul_colAct : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (u : GLR D n) (P : PolF D m n), ∃ (s : ℂ) (g : {τ : D.host.E →+* ℂ // InPsi H τ} → GL (Fin n) ℂ), MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (fockGL m w 1 u P) = MvPolynomial.C s * GlobalTheory.Harm.colAct ℂ _ Dw.p Dw.q (Fin n) g (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) P) := by
  intro D H Dw m n hΨ hm w a hw u P
  subst hm
  refine ⟨(((detFam w.c u)⁻¹ : ℂˣ) : ℂ), fun t => u ((tauPsi hΨ).symm t), ?_⟩
  have key : (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)).comp (GlobalTheory.ExportSeries.fockSubst (m := Dw.p + Dw.q) w.p u) =
      (GlobalTheory.Harm.colSubst (p := Dw.p) (q := Dw.q) (fun t => (((u ((tauPsi hΨ).symm t))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (fun t => ((u ((tauPsi hΨ).symm t) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).comp
        (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨ρ, i, b⟩ := v
    have hp := (hw ρ).1
    induction i using Fin.addCases with
    | left i =>
      have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_pos hi, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_castAdd]
      erw [GlobalTheory.Harm.colSubst_X_xVar]
      simp [GlobalTheory.Harm.xForm_apply]
    | right j =>
      have hj : ¬ ((Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_neg hj, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_natAdd]
      erw [GlobalTheory.Harm.colSubst_X_yVar]
      simp [GlobalTheory.Harm.yForm_apply]
  have hB : GlobalTheory.ExportSeries.inBasis (1 : GLR D n) u = u := by simp [GlobalTheory.ExportSeries.inBasis]
  rw [GlobalTheory.ExportSeries.fockGL_apply, hB, map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  exact DFunLike.congr_fun key P

end GlobalTheory.FockLetters
end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_base_polynomial : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (u : GLR D n) (P : PolF D m n), ∃ (s : ℂ) (g : {τ : D.host.E →+* ℂ // InPsi H τ} → GL (Fin n) ℂ), MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (fockGL m w 1 u P) = MvPolynomial.C s * GlobalTheory.Harm.colAct ℂ _ Dw.p Dw.q (Fin n) g (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) P) := by
  atlas_forward_decl GlobalTheory.FockLetters.rename_fockGL_eq_C_mul_colAct
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

include hΨ in
theorem exists_tau : Nonempty D.what₂.Tau := by
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  by_cases h : InPsi H τ₀
  · obtain ⟨ρ, -⟩ := (hΨ τ₀).1 h
    exact ⟨ρ⟩
  · obtain ⟨ρ, -⟩ := (hΨ (conjEmb τ₀)).1 ((GlobalTheory.Harm.not_mem_hostType_iff H τ₀).1 h)
    exact ⟨ρ⟩

include hΨ in
theorem le_of_good {w : Weight D n} {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hw : w.Good) (hwt : WtIs Dw w a) :
    Dw.p + Dw.q ≤ n := by
  obtain ⟨ρ⟩ := exists_tau hΨ
  have := hw.le ρ
  rw [(hwt ρ).1, (hwt ρ).2.1] at this
  exact this

include hΨ in
theorem antitone_of_good {w : Weight D n} {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hw : w.Good) (hwt : WtIs Dw w a) :
    (∀ t : {τ : D.host.E →+* ℂ // InPsi H τ}, Antitone fun i : Fin Dw.p => a (t.1, i)) ∧
      ∀ t : {τ : D.host.E →+* ℂ // InPsi H τ}, Antitone fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) := by
  have hn := le_of_good Dw hΨ hw hwt
  constructor
  · rintro ⟨τ, hτ⟩ i j hij
    obtain ⟨ρ, rfl⟩ := (hΨ τ).1 hτ
    obtain ⟨hp, hq, hap, -⟩ := hwt ρ
    dsimp only
    rw [hap i i.2, hap j j.2]
    have h1 := (w.lam ρ).anti (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, by omega⟩ from hij)
    rw [hw.lam_eq, hw.lam_eq, if_pos (by rw [hp]; exact j.2), if_pos (by rw [hp]; exact i.2)] at h1
    exact_mod_cast (add_le_add_iff_right _).1 h1
  · rintro ⟨τ, hτ⟩ i j hij
    obtain ⟨ρ, rfl⟩ := (hΨ τ).1 hτ
    obtain ⟨hp, hq, -, ham⟩ := hwt ρ
    dsimp only
    rw [show ComplexEmbedding.conjugate (tauE D ρ) = conjEmb (tauE D ρ) from rfl, ham i i.2, ham j j.2]
    have hij' : (j : ℕ) ≥ i := hij
    have h1 := (w.lam ρ).anti (show (⟨n - 1 - j, by omega⟩ : Fin n) ≤ ⟨n - 1 - i, by omega⟩ from
      show n - 1 - (j : ℕ) ≤ n - 1 - i by omega)
    rw [hw.lam_eq, hw.lam_eq] at h1
    simp only [hp, hq] at h1
    have e1 : n - 1 - (n - 1 - (i : ℕ)) = i := by omega
    have e2 : n - 1 - (n - 1 - (j : ℕ)) = j := by omega
    have c1 : ¬ (n - 1 - (i : ℕ) < Dw.p) := by omega
    have c2 : ¬ (n - 1 - (j : ℕ) < Dw.p) := by omega
    have c3 : n - Dw.q ≤ n - 1 - (i : ℕ) := by omega
    have c4 : n - Dw.q ≤ n - 1 - (j : ℕ) := by omega
    simp only [c1, c2, c3, c4, e1, e2, if_true, if_false] at h1
    have : (w.am ρ j : ℤ) ≤ w.am ρ i := by linarith
    exact_mod_cast this

end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

theorem isLetters_letterEquiv : IsLetters Dw (letterEquiv (n := n) Dw hΨ hm) := by
  rintro ⟨τ, i, b⟩
  rcases GlobalTheory.Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate _)
    (GlobalTheory.Harm.not_mem_hostType_iff H) τ with h | ⟨τ', h, rfl⟩
  · have e : letterEquiv Dw hΨ hm ⟨τ, i, b⟩ = ((tauPsi hΨ).symm ⟨τ, h⟩,
        Fin.cast hm.symm (Fin.castAdd Dw.q (i.cast (GlobalTheory.Harm.mult_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_of_mem Dw h]
      rfl
    rw [e]
    exact ⟨rfl, Or.inl ⟨(congrArg Subtype.val ((tauPsi hΨ).apply_symm_apply ⟨τ, h⟩)).symm, rfl⟩⟩
  · have e : letterEquiv Dw hΨ hm ⟨ComplexEmbedding.conjugate τ', i, b⟩ = ((tauPsi hΨ).symm ⟨τ', h⟩,
        Fin.cast hm.symm (Fin.natAdd Dw.p (i.cast (GlobalTheory.Harm.mult_conjEmb_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_conjugate Dw h]
      rfl
    rw [e]
    refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
    change conjEmb τ' = conjEmb (tauE D ((tauPsi hΨ).symm ⟨τ', h⟩))
    rw [← tauPsi_apply hΨ, Equiv.apply_symm_apply]


end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters


end GlobalTheory.FockLetters
end
end
end
end
