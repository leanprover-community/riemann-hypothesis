import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PolyComp

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose MvPolynomial

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ}

def scalTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

end

end GlobalTheory.HatNF.PolyComp

namespace GlobalTheory.HatNF

open GlobalTheory.HatNF.PolyComp

end GlobalTheory.HatNF
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_mono' {n n' κ κ' : ℕ} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ)
    (hn : n ≤ n') (hκ : κ ≤ κ') : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n' κ' Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  intro T hT
  obtain ⟨hlen, Q, ⟨q, hq, hQ⟩, hc, hca⟩ := h T hT
  exact ⟨hlen.trans hn, Q, ⟨q, hq.trans hκ, hQ⟩, hc, hca⟩

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_nil (n κ : ℕ) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp
  simp

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_nil (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) F g = 0 := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_of_polyOp_cons {n κ : ℕ} {T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq}
    (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ (T :: Θ)) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  exact fun T' hT' => h T' (by simp [hT'])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_lin_le_one {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : _root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) :
    (_root_.PI.UnitaryGroupMassFormula.UsCompose.lin X i).totalDegree ≤ 1 := by
  rcases i with x | x <;>
  · simp only [_root_.PI.UnitaryGroupMassFormula.UsCompose.lin]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => ?_)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_pderiv_add_one_le_of_ne_zero {σ : Type*} (q : MvPolynomial σ ℂ) (i : σ)
    (h : pderiv i q ≠ 0) : (pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  have hne : (pderiv i q).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by simpa [MvPolynomial.support_eq_empty] using h)
  obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  rw [totalDegree, hdeg]
  have hm' := (mem_support_iff.mp hm)
  rw [coeff_pderiv] at hm'
  have hs : m + Finsupp.single i 1 ∈ q.support := by
    rw [mem_support_iff]
    intro h0
    exact hm' (by simp [h0])
  have := le_totalDegree hs
  rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_dP_le {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (q : MvPolynomial (_root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) ℂ) : (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q).totalDegree ≤ q.totalDegree := by
  unfold _root_.PI.UnitaryGroupMassFormula.UsCompose.dP
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  by_cases h : pderiv i q = 0
  · simp [h]
  · exact (totalDegree_mul _ _).trans
      ((Nat.add_le_add_left (totalDegree_lin_le_one X i) _).trans (totalDegree_pderiv_add_one_le_of_ne_zero q i h))

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_isPolyDeg_hasDerivAt_comp_crv {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} {κ : ℕ} {Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ}
    (hQ : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q) : ∃ Q' : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q' ∧
      ∀ g, HasDerivAt (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (Q' g) 0 := by
  obtain ⟨q, hq, hQq⟩ := hQ
  refine ⟨fun g => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars g) (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q),
    ⟨_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q, (totalDegree_dP_le X q).trans hq, fun g => rfl⟩, fun g => ?_⟩
  have e : (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) =
      fun t => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) q := by
    funext t
    rw [hQq]
    rfl
  rw [e]
  exact _root_.PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly X g q

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma ckOn_rightWordDeriv_of_forall_inLie {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.B.Rw w F)
  | [], _ => by simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hF
  | X :: w, hw => by
    have h := ckOn_rightWordDeriv_of_forall_inLie hF w (fun Y hY => hw Y (by simp [hY]))
    have := _root_.Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by simpa using h)
    simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_cons' (T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word F g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_deriv_lemma_10 {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} (hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X) {κ : ℕ} :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + 1) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
        ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ' F g) 0
  | [], n, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by
      simpa [opApply_nil] using hasDerivAt_const (0 : ℝ) (0 : Wq →L[ℂ] Wp)⟩
  | T :: Θ, n, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hDr⟩ := polyOp_deriv_lemma_10 hX Θ n (polyOp_of_polyOp_cons h)
    obtain ⟨Q', hQ', hdQ⟩ := exists_isPolyDeg_hasDerivAt_comp_crv (X := X) hQ
    have hw : ∀ Y ∈ X :: T.word, _root_.Formalism.FourierDecayAlt.B.inLie k r Y := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      exacts [hX, T.word_lie Y hY]
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm Q' T.word T.word_lie ::
      _root_.GlobalTheory.HatNF.PolyComp.scalTerm Q (X :: T.word) hw :: Θr, ?_, ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨hlen.trans (Nat.le_succ n), Q', hQ', fun _ => rfl, fun _ => rfl⟩
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, hlen], Q, hQ, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · intro F hF g hg
      have hG := ckOn_rightWordDeriv_of_forall_inLie hF T.word T.word_lie
      have hD : HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t))
          (_root_.Formalism.FourierDecayAlt.B.Rw (X :: T.word) F g) 0 := by
        have := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_diff (x := (false, X)) hX (_root_.Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top hG) hg hg
        rw [← _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx] at this
        exact this
      have hfun : (fun t => _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) = fun t =>
          Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) • _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) +
            _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) := by
        funext t
        rw [opApply_cons', hc]
        simp
      rw [hfun]
      have := ((hdQ g).smul hD).add (hDr F hF g hg)
      refine this.congr_deriv ?_
      rw [opApply_cons', opApply_cons']
      simp only [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_zero]
      abel

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_word_lemma_6 {κ : ℕ} : ∀ (u : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)), (∀ X ∈ u, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + u.length) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g = _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g
  | [], _, Θ, n, h => ⟨Θ, h, fun F _ g _ => rfl⟩
  | X :: u, hu, Θ, n, h => by
    have hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X := hu X (by simp)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 u (fun Y hY => hu Y (by simp [hY])) Θ n h
    obtain ⟨Θ2, hJ2, hD2⟩ := polyOp_deriv_lemma_10 hX Θ1 (n + u.length) hJ1
    refine ⟨Θ2, ?_, fun F hF g hg => ?_⟩
    · have e : n + (X :: u).length = n + u.length + 1 := by simp [add_assoc]
      rw [e]
      exact hJ2
    · have step : _root_.Formalism.FourierDecayAlt.B.Rw (X :: u) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g =
          _root_.Formalism.REAL.RdV X (_root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F)) g := rfl
      rw [step, _root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local isOpen_univ (fun x _ hx => hE1 F hF x hx) hX g (Set.mem_univ g) hg,
        _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_eq]
      exact (hD2 F hF g hg).deriv

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_polyOp_opApply_eq_smul {κa : ℕ} {Pf : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hP : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κa Pf) :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n κ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n (κa + κ) Θ' ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) g,
        _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g = Pf g • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g
  | [], n, κ, _ => ⟨[], polyOp_nil _ _, fun F g => by simp [opApply_nil]⟩
  | T :: Θ, n, κ, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := exists_polyOp_opApply_eq_smul hP Θ n κ (polyOp_of_polyOp_cons h)
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun g => Pf g * Q g) T.word T.word_lie :: Θr, ?_,
      fun F g => ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · obtain ⟨p, hp, hPp⟩ := hP
        obtain ⟨q, hq, hQq⟩ := hQ
        exact ⟨hlen, _, ⟨p * q, (totalDegree_mul p q).trans (add_le_add hp hq),
          fun g => by simp [hPp, hQq]⟩, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · rw [opApply_cons', opApply_cons', hEr F g, hc]
      simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, smul_add, mul_smul]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_append' (Θ₁ Θ₂ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (Θ₁ ++ Θ₂) F g = _root_.Formalism.FourierDecayAlt.B.opApply Θ₁ F g + _root_.Formalism.FourierDecayAlt.B.opApply Θ₂ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_comp_lemma_2 {o₂ κ₁ κ₂ : ℕ} {Θb : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (hb : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₂ κ₂ Θb) :
    ∀ (Θa : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (o₁ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₁ κ₁ Θa → ∃ Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.opApply Θ F g = _root_.Formalism.FourierDecayAlt.B.opApply Θa (_root_.Formalism.FourierDecayAlt.B.opApply Θb F) g
  | [], o₁, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by simp [opApply_nil]⟩
  | T :: Θa, o₁, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Pf, hP, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := polyOp_comp_lemma_2 hb Θa o₁ (polyOp_of_polyOp_cons h)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 T.word T.word_lie Θb o₂ hb
    obtain ⟨Θ2, hJ2, hE2⟩ := exists_polyOp_opApply_eq_smul hP Θ1 (o₂ + T.word.length) κ₂ hJ1
    refine ⟨Θ2 ++ Θr, ?_, fun F hF g hg => ?_⟩
    · have hJ2' := polyOp_mono' hJ2 (show o₂ + T.word.length ≤ o₁ + o₂ by omega) le_rfl
      unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJ2' hJr ⊢
      intro T' hT'
      rcases List.mem_append.mp hT' with hT' | hT'
      exacts [hJ2' T' hT', hJr T' hT']
    · rw [opApply_append', opApply_cons', hE2 F g, ← hE1 F hF g hg, hEr F hF g hg, hc]
      simp

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.polyLift_closed : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par)
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), _root_.GlobalTheory.HatNF.PolyLift P Bs 0 0 1 ∧
      (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → _root_.GlobalTheory.HatNF.PolyLift P Bs o κ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o' κ' a) ∧
      ∀ o₁ κ₁ o₂ κ₂ a b, _root_.GlobalTheory.HatNF.PolyLift P Bs o₁ κ₁ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o₂ κ₂ b →
        _root_.GlobalTheory.HatNF.PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  intro Wp Wq _ _ _ _ _ _ P Bs
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨[_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun _ => 1) [] (by simp)], ?_, ?_⟩
    · intro Tm hTm
      simp only [List.mem_singleton] at hTm
      subst hTm
      refine ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm], fun _ => 1, ?_, fun _ => rfl, fun _ => rfl⟩
      exact ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
    · intro F _ Φ hΦ
      have hF : _root_.Formalism.FourierDecayAlt.B.opApply [_root_.GlobalTheory.HatNF.PolyComp.scalTerm (Wp := Wp) (Wq := Wq) (fun _ => 1) []
          (by simp)] F = F := by
        funext g
        simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.B.Rw, _root_.GlobalTheory.HatNF.PolyComp.scalTerm]
      rw [hF]
      exact hΦ
  · rintro o o' κ κ' a ho hκ ⟨Θ, hΘ, hR⟩
    exact ⟨Θ, polyOp_mono' hΘ ho hκ, hR⟩
  · rintro o₁ κ₁ o₂ κ₂ a b ⟨Θa, hJa, hRa⟩ ⟨Θb, hJb, hRb⟩
    obtain ⟨Θ, hJ, hE⟩ := polyOp_comp_lemma_2 hJb Θa o₁ hJa
    refine ⟨Θ, hJ, ?_⟩
    unfold _root_.Formalism.FourierDecayAlt.TL.RadIs at hRa hRb ⊢
    intro F hF Φ hΦ
    have hsmooth : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F := by
      unfold _root_.Formalism.FourierDecayAlt.KB.CptCoef at hF
      exact hF.1
    have hsm : _root_.Formalism.FourierDecayAlt.B.SmoothCoef (_root_.Formalism.FourierDecayAlt.C6.domL Bs ∅) Θb :=
      (_root_.GlobalTheory.HatNF.polyOp_ok P.k P.r Wp Wq o₂ κ₂ Θb hJb).1 _
    have h2 := hRa _ (_root_.Formalism.FourierDecayAlt.P.TLB.cpt_op hF hsm) _ (hRb F hF Φ hΦ)
    unfold _root_.Formalism.FourierDecayAlt.Top.IsRadOf at h2 ⊢
    intro x hx
    rw [show (a * b).1 Φ = a.1 (b.1 Φ) from rfl, h2 x hx]
    unfold _root_.Formalism.FourierDecayAlt.Q.resG
    rw [_root_.Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs (fun g hg => (hE F hsmooth g hg).symm) (_root_.Formalism.FourierDecayAlt.P.TLB.wCell_gv Bs hx)]

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  atlas_forward_decl GlobalTheory.HatNF.polyLift_closed
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mulG_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im := by
    funext w; exact Complex.normSq_apply w
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem mulG_ld_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiffOn ℝ ∞ (LE.ld q φ) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv q hφ
  exact h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mulG_gR_contDiff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    ContDiff ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => gR P Bs x.1 x.2) := by
  unfold gR Q.GGl
  refine ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)
  · exact contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a
  · exact (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd

theorem mulG_gR_pos (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Formalism.FourierDecayAlt.P.Qx5.OpR P.k P.r Bs.z Bs.z') : 0 < gR P Bs x.1 x.2 :=
  mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2

theorem mulG_mem (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ)
    {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ) • Φ c g) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
  refine Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ
  · refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx
  · intro x _ h hh h' hh'
    simp only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']

theorem exists_isMulG_of_smoothLog (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W := by
  refine ⟨fun q =>
    { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩
      map_add' := fun Φ Ψ => ?_
      map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem mulG_exists : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W :=
  fun _ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ => exists_isMulG_of_smoothLog P Bs hφ

end GlobalTheory.HatNF
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  atlas_forward_decl GlobalTheory.HatNF.radial_mulG
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem vec_bigPt_eq_radial : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ P p c hc hG
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  have hc' : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc _
  have hz := Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ p.T.base.z_mem p.T.base.z'_mem p.T.base.sec hζ
  have hx : ((fun a : Fin P.r => c a.castSucc), NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r))) ∈
      Q.DomR P.k P.r p.T.base.z p.T.base.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR p.T.base.z_mem p.T.base.z'_mem p.T.base.sec
      (q := ((fun a : Fin P.r => c a.castSucc), c (Fin.last P.r))) ⟨hc', hζ⟩
  refine ⟨_, hx, ?_, ?_, ?_⟩
  · show Complex.normSq (∏ a : Fin P.r, c a.castSucc) *
        (Complex.normSq (Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))) - Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') =
        D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [hz, Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc c, Complex.normSq_mul]
    ring
  · show ‖(∏ a : Fin P.r, c a.castSucc) * Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))‖ = _
    rw [hz, Fin.prod_univ_castSucc c]
  · have hpos : 0 < ∏ a : Fin P.r,
        (if a.val < (Fin.last P.r).val then ‖c a.castSucc‖ ^ (Mdim P.k P.r a - 1) else 1 : ℝ) := by
      refine Finset.prod_pos fun a _ => ?_
      split_ifs
      · exact pow_pos (norm_pos_iff.2 (hc' a)) _
      · exact one_pos
    refine ⟨_, inv_pos.2 hpos, fun H Φ hΦ => ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p H c hc hG]
    unfold nv
    rw [hΦ _ hx]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_cancel_left₀ hpos.ne']
    have e : Q.wCell P.k P.r (Fin.last P.r) (fun a : Fin P.r => c a.castSucc) *
        NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)) =
        bigCell P.k P.r (fun a : Fin P.r => c a.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
      unfold NF.muZ
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization _ _ _ _).1]
    rw [e]

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  atlas_forward_decl GlobalTheory.HatNF.vec_bigPt_eq_radial
end

section
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_listProd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (H : List (RA P Bs)) (hH : ∀ h ∈ H, PolyLift P Bs o κ h) :
    PolyLift P Bs (H.length * o) (H.length * κ) H.prod := by
  obtain ⟨h1, -, hmul⟩ := GlobalTheory.T.polyLift_one_mono_mul Wp Wq P Bs
  induction H with
  | nil => simpa using h1
  | cons a H ih =>
    have := hmul _ _ _ _ _ _ (hH a (by simp)) (ih fun h hh => hH h (by simp [hh]))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, add_comm _ o, add_comm _ κ]
    exact this

theorem wordBound_cptCoef : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  intro a ha Wp Wq _ _ _ _ _ _ P p w hw
  obtain ⟨X, μ, L, st, hD, hL⟩ := p.hΘ
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P _ _ _ _ p.hP X
  have hNF : IsNF (Bs := p.T.base) X d := hd
  have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 p.hl.1 p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w
    hw.1 hw.2
  have hl : (D.positionted w).length = w.length := by simp [D.positionted]
  obtain ⟨C, J, Ts, hC, hTs, hB⟩ := GlobalTheory.T.wordOperator_radial_pointwise_bound Wp Wq P p.T.base X μ L st p.l0 d hD hNF (Fin w.length) _ (a P.r)
    (ha Wp Wq P p.T.base X μ L st p.l0 d hD hNF) (D.positionted w) hok.1
  rw [hl] at hTs hB
  have hlift : ∀ H : List (RA P p.T.base), ∃ Θ : B.DiffOp P.k P.r Wp Wq, H ∈ Ts →
      Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
        (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ ∧ TL.RadIs P p.T.base Θ H.prod.1 := by
    intro H
    by_cases hH : H ∈ Ts
    · obtain ⟨Θ, hΘ⟩ := polyLift_listProd P p.T.base _ _ H (hTs H hH).2
      rw [(hTs H hH).1] at hΘ
      exact ⟨Θ, fun _ => hΘ⟩
    · obtain ⟨Θ, -⟩ := (GlobalTheory.T.polyLift_one_mono_mul Wp Wq P p.T.base).1
      exact ⟨Θ, fun h => absurd h hH⟩
  choose lf hlf using hlift
  refine ⟨C, J, Ts.map lf, hC, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hΘ
    exact (hlf H hH).1
  · rintro φ f ⟨hφ, hf⟩ e c hc hG
    obtain ⟨hm1, hm2⟩ := GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier Wp Wq P p.T.base φ f
    obtain ⟨hsl, hcpt⟩ := hm1 hφ
    obtain ⟨W, hW⟩ := mulG_exists Wp Wq P p.T.base X μ L st p.l0 d hD hNF φ hsl
    obtain ⟨⟨ε, hε, hN⟩, -⟩ := Formalism.FourierDecayAlt.P.compact_support_facts P.k P.r Wp Wq p.T.base f hf
    obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P _ _ _ _ p.T.base f p.hP rfl rfl rfl rfl
      ⟨hN.2.1, ε, hε, hN.2.2⟩
    have hΦ' : Top.IsRadOf P p.T.base Φ f := hΦ
    have hrad := hL w hw _ (hcpt hf) _ (hm2 W Φ hW hΦ') e
    rw [TL.act_e1Vec] at hrad
    obtain ⟨x, hx, hg, hdd, lam, hlam, hV⟩ := GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm Wp Wq P p c hc hG
    have hb := hB φ W hsl hW Φ e x hx
    rw [hg, hdd] at hb
    have hs : ((Ts.map lf).map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum =
        lam * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun H hH => ?_
      exact hV _ _ ((hlf H hH).2 f hf Φ hΦ')
    rw [hV _ _ hrad, hs]
    have := mul_le_mul_of_nonneg_left hb hlam.le
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    ring

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  atlas_forward_decl GlobalTheory.HatNF.wordBound_cptCoef
end

section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem vec_opApply_cutF_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Θ : B.DiffOp P.k P.r Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (δ : ℝ) (γ : C.LPt), C6.IsCut0 χ → 0 < δ → δ < TBB.Gp p γ → p.V (B.opApply Θ (D.cutF p.T.base χ f δ)) γ = p.V (B.opApply Θ f) γ := by
  intro Wp Wq _ _ _ _ _ _ P p Θ f χ δ γ hχ hδ hlt
  have hlt0 : δ < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hlt
  have hopen : IsOpen {x : B.Mat P.k P.r | δ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hloc : ∀ g, δ < Gf P.k P.r p.T.base.z p.T.base.z' g →
      B.opApply Θ (D.cutF p.T.base χ f δ) g = B.opApply Θ f g := by
    intro g hg
    refine Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hopen (fun x hx => ?_) g hg
    have hx' : δ < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    simp only [D.cutF]
    rw [hχ.2.2 _ ((one_le_div hδ).mpr hx'.le), Complex.ofReal_one, one_smul]
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose h.1 h'.choose_spec.2.1
    have hlt' : δ < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hlt0
    have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h'.choose
      (D.muR p.T.base h'.choose (h.1.2 ▸ D.ptPerm γ)) (B.opApply Θ (D.cutF p.T.base χ f δ)) (B.opApply Θ f) 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [hloc _ (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hlt')])
    rw [e, one_smul]
  · rfl
  · rfl

end GlobalTheory.HatNF
end

section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow {e : ℕ} {φ : ℝ → ℝ} (hφ : _root_.GlobalTheory.HatNF.CutPow e φ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) ∧
      ∀ x, φ x = x ^ e * h x := by
  unfold _root_.GlobalTheory.HatNF.CutPow at hφ
  obtain ⟨hφs, ⟨δ, hδ, hφ0⟩, a, R, hφR⟩ := hφ
  have hzero : ∀ x < δ, (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => (0 : ℝ) := fun x hx =>
    (eventually_lt_nhds hx).mono fun y hy => by
      show φ y / y ^ e = 0
      rw [hφ0 y hy, zero_div]
  have hconst : ∀ x, max R δ < x → (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => a := fun x hx =>
    (eventually_gt_nhds hx).mono fun y hy => by
      have hy0 : 0 < y := hδ.trans (lt_of_le_of_lt (_root_.le_max_right _ _) hy)
      have hy1 : φ y = a * y ^ e := hφR y ((_root_.le_max_left _ _).trans hy.le)
      simp only
      rw [hy1, mul_div_assoc, div_self (pow_ne_zero _ hy0.ne'), mul_one]
  have hsmooth : ContDiff ℝ ∞ (fun y => φ y / y ^ e) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x δ with hx | hx
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
    · exact hφs.contDiffAt.div (contDiffAt_id.pow e) (pow_ne_zero _ (hδ.trans_le hx).ne')
  refine ⟨fun y => φ y / y ^ e, hsmooth, fun q => ?_, fun x => ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ (max R δ))).exists_bound_of_continuousOn
      (hsmooth.continuous_iteratedDeriv q (WithTop.coe_le_coe.mpr le_top)).continuousOn
    refine ⟨max C (max |a| 0), fun x => ?_⟩
    rcases lt_or_ge x δ with hx | hx
    · rw [(hzero x hx).iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs <;> rw [norm_zero] <;> exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
    rcases le_or_gt x (max R δ) with hx' | hx'
    · exact (hC x ⟨hx, hx'⟩).trans (_root_.le_max_left _ _)
    · rw [(hconst x hx').iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs
      · rw [Real.norm_eq_abs]; exact (_root_.le_max_left _ _).trans (_root_.le_max_right _ _)
      · rw [norm_zero]; exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
  · rcases lt_or_ge x δ with hx | hx
    · show φ x = x ^ e * (φ x / x ^ e)
      rw [hφ0 x hx, zero_div, mul_zero]
    · have hx0 : x ^ e ≠ 0 := pow_ne_zero _ (hδ.trans_le hx).ne'
      show φ x = x ^ e * (φ x / x ^ e)
      rw [mul_comm, div_mul_cancel₀ (φ x) hx0]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem ckOn_smul_of_ckOn_infinite {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hc : ContDiff ℝ ∞ c) {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (n : ℕ∞)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : _root_.Formalism.FourierDecayAlt.B.CkOn n (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => c g • F g) := by
  unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF ⊢
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hF', hEq⟩ := hF g₀ hg₀
  refine ⟨U, fun g => c g • F' g, hU, hgU, ?_, fun g hgU hg => by simp only [hEq g hgU hg]⟩
  exact (hc.contDiffOn.smul hF').of_le (WithTop.coe_le_coe.mpr le_top)

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem inCC_real_smul_comp_Gf_of_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} {A : ℝ} {m : ℕ} (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f)
    (hA : _root_.Formalism.FourierDecayAlt.B.InCC A m f) :
    _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (r : ℝ) + 2) * m) m (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k r z z' g) : ℝ) : ℂ) • f g) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
  have hcd : ContDiff ℝ ∞ (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hh.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z'))
  obtain ⟨M, hM⟩ := _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.poly_H (_root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k (0 + ρ) z z') m
  obtain ⟨K, hK0, hK⟩ := _root_.PI.UnitaryCorollaryDerivatives.CRH.main (fun g => _root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) h
    (fun _ => 2 * (0 + ρ) + 2) m M (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z') hh hb (fun w hw hne g hg => by
      have hp : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) w = (2 * (0 + ρ) + 2) * w.length := by
        simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, List.map_const', List.sum_replicate, smul_eq_mul]
        ring
      rw [hp]
      exact hM w hw hne g hg) m 0
  have hWB : _root_.PI.UnitaryCorollaryDerivatives.WB (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2))
      (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) (m + 0) K 0 := by
    unfold _root_.PI.UnitaryCorollaryDerivatives.WB
    intro u v hu hv huv g hg
    rw [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
    have hadm : _root_.PI.UnitaryCorollaryDerivatives.CRH.admitted m (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := ⟨u, v, hu, hv, huv, rfl⟩
    have hlen : (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ m := by
      simp only [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.length_append, List.length_map]; omega
    have hK1 := hK _ hadm hlen g hg
    simp only [iteratedDeriv_zero] at hK1
    have hn : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) ≤
        (List.map (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2)) (u ++ v)).sum := by
      simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.map_append, List.map_map, List.sum_append,
        List.sum_map_add, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul,
        List.length_map]
      omega
    calc _ ≤ K * _root_.Formalism.FourierDecayAlt.B.gN g ^ _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := hK1
      _ = K * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((_root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
          (by linarith [(Nat.cast_le (α := ℝ)).mpr hn])) hK0
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := _root_.PI.UnitaryCorollaryDerivatives.cC_bound (j := 0) (ρ := ρ) (E := Wq →L[ℂ] Wp) (Q := m) (o := 0)
    (mm₀ := m) (A₀ := A) hcd hWB (w := []) (fun X hX => nomatch hX) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨c, hc⟩ := id hA
  have hc' := hc
  unfold _root_.Formalism.FourierDecayAlt.B.InCC
  refine ⟨CΨ * c, ?_⟩
  unfold _root_.Formalism.FourierDecayAlt.B.CCle at hc ⊢
  refine ⟨ckOn_smul_of_ckOn_infinite hcd _ hf, fun u v hu hv huv g hg => ?_⟩
  have hIW : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k (0 + ρ)), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.unitLie k (0 + ρ) X) → _root_.Formalism.FourierDecayAlt.U.unitP k 0 ρ w :=
    fun w hw X hX => ⟨⟨(hw X hX).1, fun i b hb' _ => absurd hb' (Nat.not_lt_zero _)⟩, (hw X hX).2⟩
  have hB : ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖ ≤
      CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) :=
    hCΨ f c hc' u v (hIW u hu) (hIW v hv) huv g hg
  have hpos := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
  calc _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖
      ≤ _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        (CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A)) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hpos.le _)
    _ = CΨ * c := by
        rw [mul_comm, mul_assoc, ← Real.rpow_add hpos]
        have h0 : ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) +
            (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) = 0 := by
          simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [h0, Real.rpow_zero, mul_one]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.mulG_ckOn_inCC : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), ∀ (e m : ℕ) (φ : ℝ → ℝ)
    (f : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.GlobalTheory.HatNF.CutPow e φ →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) f → _root_.Formalism.FourierDecayAlt.B.InCC A m f →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (_root_.GlobalTheory.HatNF.mulG Bs φ f) ∧
      _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m (_root_.GlobalTheory.HatNF.mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e m φ f A hφ hf hA
  have hval : _root_.GlobalTheory.HatNF.mulG Bs φ f =
      fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g := rfl
  obtain ⟨h, hh, hb, hφh⟩ := exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow hφ
  have hφs : ContDiff ℝ ∞ φ := by
    unfold _root_.GlobalTheory.HatNF.CutPow at hφ
    exact hφ.1
  have hfun : _root_.GlobalTheory.HatNF.mulG Bs φ f = fun g =>
      ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) •
        (((h (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g) := by
    rw [hval]
    funext g
    rw [smul_smul, ← Complex.ofReal_mul, ← hφh]
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact ckOn_smul_of_ckOn_infinite (c := fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hφs.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))) ⊤ hf
  · rw [hfun]
    obtain ⟨c, hc⟩ := inCC_real_smul_comp_Gf_of_inCC Bs.z Bs.z' hh hb hf hA
    have hpd := (show (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F →
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r)
          (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g)) ∧
      ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (b : ℝ),
        _root_.Formalism.FourierDecayAlt.B.CCle (A' + (((2 * P.r + 2) * e : ℕ) : ℝ)) m' F b →
          _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g) (K * b) from
      _root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow (Wp := Wp) (Wq := Wq) Bs.z Bs.z' e).2
    obtain ⟨K, -, hK⟩ := hpd (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m
    refine ⟨K * c, hK _ c ?_⟩
    have hA' : A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m) + (((2 * P.r + 2) * e : ℕ) : ℝ) =
        A - (2 * (P.r : ℝ) + 2) * m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hA']
    exact hc

end

end GlobalTheory.HatNF
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma norm_opApply_le_of_polynomial_coeffs_lemma {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (A : ℝ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (B : ℝ), _root_.Formalism.FourierDecayAlt.B.CCle A o G B →
      ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ ≤ C * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
  induction Θ with
  | nil => exact ⟨0, le_rfl, fun G B hG g _ => by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.P.B4.gN_rpow_nonneg, mul_nonneg (mul_nonneg le_rfl (_root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG))]⟩
  | cons T Θ ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (fun S hS => hΘ S (List.mem_cons_of_mem _ hS))
    obtain ⟨hlen, Q, hQ, hcoef⟩ := hΘ T List.mem_cons_self
    obtain ⟨CQ, hCQ0, hCQ⟩ := _root_.PI.UnitaryCorollaryDerivatives.pb_nonneg (_root_.PI.UnitaryCorollaryDerivatives.pb_poly hQ) 0
    have hunit : ∀ X ∈ List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word, _root_.Formalism.FourierDecayAlt.B.unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
    set ν : ℝ := ‖((List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nz T.word).prod : ℂ)‖ with hν
    refine ⟨CQ * ν + C₁, by positivity, fun G B hG g hg => ?_⟩
    have hgpos : 0 < _root_.Formalism.FourierDecayAlt.B.gN g := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
    have hB : 0 ≤ B := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG
    have hRw : _root_.Formalism.FourierDecayAlt.B.CCle A 0 (_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G) B :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hunit (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by simpa using hlen) hG)
    have hRw' := hRw.2 [] [] (by simp) (by simp) (by simp) g hg
    simp only [_root_.Formalism.FourierDecayAlt.B.dLR, List.foldr_nil, _root_.Formalism.FourierDecayAlt.B.Rw] at hRw'
    have hword : ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖ ≤ B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A) := by
      rw [Real.rpow_neg hgpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgpos _),
        mul_comm]
      simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hRw'
    have hQg : ‖Q g‖ ≤ CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) := by
      have := hCQ [] (by simp) (by simp) g hg
      simpa [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw] using this
    have hterm : ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
      rw [hcoef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        congrFun (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale T.word G) g, norm_smul, ← hν, sub_eq_add_neg,
        Real.rpow_add hgpos]
      calc ‖Q g‖ * (ν * ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖)
          ≤ (CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ)) * (ν * (B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A))) := by
            gcongr
        _ = CQ * ν * B * (_root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A)) := by ring
    have hrest := hC₁ G B hG g hg
    have hsplit : _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) G g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g := by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]
    rw [hsplit]
    calc ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖
        ≤ ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ + ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ := norm_add_le _ _
      _ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) + C₁ * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) :=
          add_le_add hterm hrest
      _ = (CQ * ν + C₁) * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by ring

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma continuousOn_opApply_of_polynomial_coeffs_lemma_2 {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) G) :
    ContinuousOn (_root_.Formalism.FourierDecayAlt.B.opApply Θ G) (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  apply _root_.Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
  intro T hT
  obtain ⟨-, Q, hQ, hcoef⟩ := hΘ T hT
  have hQc : Continuous Q := (_root_.Formalism.FourierDecayAlt.P.poly_adm (n := 0) hQ).1.continuous
  have hRw : ContinuousOn (_root_.Formalism.FourierDecayAlt.B.Rw T.word G) (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
    _root_.Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' subset_rfl (_root_.Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hG T.word_lie)
  have hfun : (fun g => (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)) =
      fun g => Q g • _root_.Formalism.FourierDecayAlt.B.Rw T.word G g := by
    funext g
    rw [hcoef]
    simp
  rw [hfun]
  exact hQc.continuousOn.smul hRw

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.vecV_cut_polyOp : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (o κ : ℕ) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp P.k P.r Wp Wq) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ → _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F → _root_.Formalism.FourierDecayAlt.B.InCC A o F → c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - 1 - κ → ∀ cut : ℕ → _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, (∀ n g, cut n g = ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) → ∀ γ : _root_.Formalism.FourierDecayAlt.C.LPt, Filter.Tendsto (fun n => p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) γ) Filter.atTop (nhds (p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) γ)) := by
  obtain ⟨c₃, hc₃⟩ := _root_.Formalism.FourierDecayAlt.P.PBE.vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p o κ Θ F A hΘ hF hCC hA cut hcut γ
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hΘ
  have hΘ' : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by
    intro T hT
    obtain ⟨hl, Q, hQ, hc, -⟩ := hΘ T hT
    exact ⟨hl, Q, hQ, hc⟩
  have hcutφ : ∀ n : ℕ, cut n = fun g => _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := by
    intro n
    funext g
    rw [hcut]
    rfl
  have hψ : ∀ (n : ℕ) g, cut n g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    have h : _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := rfl
    rw [hcutφ, h]
    ring
  unfold _root_.Formalism.FourierDecayAlt.B.InCC at hCC
  obtain ⟨b, hb⟩ := hCC
  have hb0 : 0 ≤ b := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hb
  have hb1 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F b := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨K, hK0, hK⟩ := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) o
  have hGn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o (fun g => cut n g • F g) (b + K * b) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) (hK ((n : ℝ) + 1) hR A F b hb))
    refine _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (_root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr ?_ h3) ?_
    · intro g _
      rw [hψ n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    · rw [norm_neg, norm_one, one_mul]
      linarith [div_le_self (mul_nonneg hK0 hb0) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
  have hG0 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F (b + K * b) := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb1 (by nlinarith)
  obtain ⟨C, hC0, hC⟩ := norm_opApply_le_of_polynomial_coeffs_lemma o κ (A - 1) Θ hΘ'
  have hexp : (κ : ℝ) - (A - 1) = -(A - 1 - κ) := by ring
  have hckn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (fun g => cut n g • F g) := by
    intro n
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_nice (R := (n : ℝ) + 1) (by positivity) hF).1
    rw [hcutφ n]
    exact h
  unfold _root_.Formalism.FourierDecayAlt.KB.Pl.V
  refine hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ (A - 1 - κ) hA
    (fun n => _root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) (C * (b + K * b))
    (by positivity)
    (fun n => (continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' (hckn n)).mono
      (fun g hg => hg.1))
    ((continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' hF).mono (fun g hg => hg.1))
    (fun n g hg => by
      have := hC _ _ (hGn n) g hg.1
      rwa [hexp] at this)
    (fun g hg => by
      have := hC _ _ hG0 g hg.1
      rwa [hexp] at this) ?_
  intro g _
  set S : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℝ := fun h => ∑ i, ∑ j, Complex.normSq (h i j) with hS
  have hScont : Continuous S :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hO : IsOpen {h | S h < S g + 1} := isOpen_lt hScont continuous_const
  obtain ⟨N, hN⟩ := exists_nat_ge (S g + 1)
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hO _ g (by simp)
  intro h hh
  have hSh : S h < S g + 1 := hh
  have hS0 : 0 ≤ S h := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • h) i j) =
      ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h := by
    simp only [hS, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Finset.mul_sum]
  have hle : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h ≤ 1 := by
    rw [← mul_inv, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hone : cut n h = 1 := by
    rw [hcut, hscaled, Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  simp only [hone, one_smul]

end GlobalTheory.HatNF
end

section
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

theorem tendsto_list_map_sum_real {α : Type*} (l : List α) (u : α → ℕ → ℝ) (v : α → ℝ)
    (h : ∀ x ∈ l, Tendsto (u x) atTop (𝓝 (v x))) :
    Tendsto (fun n => (l.map fun x => u x n).sum) atTop (𝓝 (l.map v).sum) :=
  tendsto_list_sum l h

theorem wordBound_decay : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  intro a ha Cb
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.HatNF.vecV_cut_polyOp
  obtain ⟨c₂, hc₂⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_op
  refine ⟨5 * max Cb 8 + max Cb 8 ^ 2 + 1 + |max c₁ c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p N w hDD hw hwN
  obtain ⟨C, J, Θs, hC, hpoly, hB⟩ := GlobalTheory.T.wordBound_compactSupportCoefficients a ha Wp Wq P0 p w hw
  refine ⟨C, J, Θs, hC, hpoly, ?_⟩
  rintro φ f ⟨e₀, A, hφ, hf, hfA, hA⟩ e c hc hG
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb8 : (8 : ℝ) ≤ max Cb 8 := le_max_right _ _
  have hCb0 : (0 : ℝ) ≤ max Cb 8 := by linarith
  have hwN' : (w.length : ℝ) ≤ N := by exact_mod_cast hwN
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (2 * (P0.r : ℝ) + 2) * e₀ := by positivity
  have hcut' : ∀ n g, Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    simp [Formalism.FourierDecayAlt.P.CutBP.cutN, Formalism.FourierDecayAlt.P.JCx2.pdPsi, Formalism.FourierDecayAlt.P.JCx2.pdPhi, Formalism.FourierDecayAlt.P.JCx2.pdChi,
      Formalism.FourierDecayAlt.P.JCx2.pdSq]
  have hmono : ∀ c : ℝ, c ≤ max c₁ c₂ → ∀ B' : ℝ,
      max c₁ c₂ * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) + 1) ≤ B' →
      c * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) + 1) ≤ B' := by
    intro c hc B' hB
    rw [hXn]
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  obtain ⟨δ₀, hδ₀, hφ0⟩ := hφ.2.1
  set γ := TBB.bigPt P0.r c with hγ
  set δ : ℝ := min δ₀ (TBB.Gp p γ / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ < TBB.Gp p γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := ⟨_, Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation⟩
  have hmul : ∀ n, mulG p.T.base φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n) =
      fun g => Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r n g • mulG p.T.base φ f g := by
    intro n
    funext g
    simp only [mulG, Formalism.FourierDecayAlt.P.CutBP.apx, D.cutF]
    by_cases hg : Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀
    · simp [hφ0 _ hg]
    · rw [hχ.2.2 _ ((one_le_div hδ).2 (hδ1.trans (not_lt.1 hg)))]
      simp only [Complex.ofReal_one, one_smul]
      exact smul_comm _ _ _
  have hn := fun n => hB φ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)
    ⟨hφ.1, Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P0 p.T.base hχ hf hδ n⟩ e c hc hG
  simp only [hmul] at hn
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ hn
  · refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
    have hcongr : ∀ G, p.V (p.Θ.Θ w e G) γ = D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) γ :=
      fun G => Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ γ
        (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    rw [hcongr]
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
        _ ≤ max Cb 8 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
          rw [hXn]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
            (by linarith)
        _ ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwN' hCb0) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o :=
      hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Nat.cast_nonneg _))
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    obtain ⟨hck, bF, hbF⟩ := GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P0 p.T.base e₀ o φ f A hφ hf (hfA o)
    have hv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < δ₀ → mulG p.T.base φ f g = 0 := by
      intro g hg
      simp [mulG, hφ0 _ hg]
    have hth := hmono c₂ (le_max_right _ _)
      (A - (2 * (P0.r : ℝ) + 2) * ((e₀ : ℝ) + o) - 1 - ((κ : ℝ) + 3 * ((P0.r : ℝ) + 1) * o)) (by linarith [hthr])
    have key := hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ γ (mulG p.T.base φ f) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r)
      nf fib o κ Dop δ₀ _ bF hfib hIn hδ₀ hv hck hbF hcut' hth
    exact key.congr fun n => (hcongr _).symm
  · refine Tendsto.const_mul _ (tendsto_list_map_sum_real Θs
      (fun Θ n => ‖B.hsVec (p.V (B.opApply Θ (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f δ) n)) γ)‖)
      (fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) γ)‖) fun Θ hΘ => ?_)
    refine Tendsto.norm ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_)
    rw [← GlobalTheory.HatNF.vec_opApply_cutF_eq Wp Wq P0 p Θ f χ δ γ hχ hδ hδ2]
    set o : ℕ := w.length * (2 * P0.r + P0.k + 1) with ho
    set κ : ℕ := w.length * (8 * (P0.r + 1) * (2 * P0.r + P0.k + 1)) with hκ
    have hoR : (o : ℝ) = w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by rw [ho]; push_cast; ring
    have hκR : (κ : ℝ) = 8 * ((P0.r : ℝ) + 1) * o := by rw [hoR, hκ]; push_cast; ring
    have ho' : (o : ℝ) ≤ max Cb 8 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
      rw [hoR]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have hκ' : (κ : ℝ) ≤ max Cb 8 * ((P0.r : ℝ) + 1) * o := by
      rw [hκR]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb8 (by linarith)) (Nat.cast_nonneg _)
    have hthr := Formalism.FourierDecayAlt.P.PBE.thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 8) (max c₁ c₂) o κ _
      hr0 hrX hN0 hCb0 (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
    have h3 : (0 : ℝ) ≤ 3 * ((P0.r : ℝ) + 1) * o := by positivity
    exact hc₁ Wp Wq P0 p o κ Θ (D.cutF p.T.base χ f δ) (A - 2 * ((P0.r : ℝ) + 1) * o) (hpoly Θ hΘ)
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf δ)
      (Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hfA hδ _ o (by linarith))
      (hmono c₁ (le_max_left _ _) _ (by linarith [hthr])) (Formalism.FourierDecayAlt.P.CutBP.cutN P0.k P0.r) (fun _ _ => rfl) γ

end GlobalTheory.HatNF
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordBound_smooth_decaying_coefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  atlas_forward_decl GlobalTheory.HatNF.wordBound_decay
end
