import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.WeightBoundMultiplicative

section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma gf_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'

lemma dmin_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, hq, he⟩ := minor_polynomial_property k r z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), he⟩

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_monoM (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (a b : Fin (r + 2) → ℕ) (c : ℕ)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (C6.monoM D a b c) S n 0 (2 * r + 2) := by
  have hfac : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))),
      UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l)
        S n 0 (2 * r + 2) := by
    intro l _
    by_cases hl : l ∈ L ∨ l = Fin.last (r + 1)
    · have hl' : l.val ≤ 2 * r + 2 := by have := l.isLt; omega
      have h1 : UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (minor_polynomial_property k r D.z D.z' l) hSG hc₀
          (fun g hg => hSD g hg l hl) (a l) n) le_rfl hl'
      have h2 : UBL (fun g => (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (dmin_star_pd k r D.z D.z' l) hSG hc₀
          (fun g hg => by rw [Complex.star_def, Complex.normSq_conj]; exact hSD g hg l hl) (b l) n)
          le_rfl hl'
      exact ubl_mul hSG h1 h2
    · push_neg at hl
      obtain ⟨ha, hb⟩ := hab l hl.1 hl.2
      have e : (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) =
          fun _ => (1 : ℂ) := by
        funext g
        simp [ha, hb]
      rw [e]
      exact ubl_const 1 hSG n _
  have hP := ubl_prod hSG Finset.univ
    (fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) hfac
  have hG := ubl_invpow (gram_function_polynomial k r D.z D.z') hSG hc₀ hSGf c n
  exact ubl_mul hSG hP hG

private lemma rw_congr_on_open_of_eq_on_GV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set (Mat k r)}
    (hV : IsOpen V) {f f' : Mat k r → F} (he : ∀ g ∈ GV k r, g ∈ V → f g = f' g) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ V → Rw w f g = Rw w f' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgV; exact he g hg hgV
  | cons X w ih =>
    intro hw g hg hgV
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show Dx (false, X) (Rw w f) g = Dx (false, X) (Rw w f') g
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hV hgV] with t ht
    exact ih' _ (crv_mem (x := (false, X)) (hw X (by simp)) hg t) ht

private lemma dw_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ) (f : Mat k r → F) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext g
    show Dx x (Dw w (fun g => c • f g)) g = c • Dx x (Dw w f) g
    rw [ih, Dx_eq, Dx_eq]
    first
    | exact deriv_const_smul' c (f := fun t => Dw w f (crv x g t))
    | exact deriv_const_smul' (f := fun t => Dw w f (crv x g t)) c
    | simp [deriv_const_smul']

lemma ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hSsub : S ⊆ GPos D := fun g hg => ⟨(hS g hg).1, lt_of_lt_of_le hε (hS g hg).2⟩
  choose Cf hCf using fun i => hE2 ε hε i
  refine ⟨⟨|(v.map nz).prod| * ∑ j ∈ Finset.range (n + v.length + 1), |Cf j|, by positivity, ?_⟩, ?_⟩
  · intro w hw g hg
    obtain ⟨u, v', hu, hv', hlen, rfl⟩ := hw
    have hgGV := (hS g hg).1
    have hgε := (hS g hg).2
    have hX : 0 ≤ gN g := by
      first
      | positivity
      | (unfold gN; positivity)
      | (simp only [gN]; positivity)
    rw [Rw_scale v E, dw_const_smul, norm_smul]
    have hsplit : Dw (wL u ++ wR v') (Rw (v.map nrm) E) g = dLR u (v' ++ v.map nrm) E g := by
      rw [dLR_eq, Dw_append, Dw_append, Dw_wR, Dw_wR]
      rw [show Rw (v' ++ v.map nrm) E = Rw v' (Rw (v.map nrm) E) by simp only [Rw, List.foldr_append]]
    rw [hsplit]
    have hU : C6.UnitWords k r u (v' ++ v.map nrm) (u.length + (v' ++ v.map nrm).length) := by
      refine ⟨hu, fun X hX => ?_, rfl⟩
      rcases List.mem_append.1 hX with h | h
      · exact hv' X h
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 h
        exact nrm_unit (hv Y hY)
    have hb := hCf (u.length + (v' ++ v.map nrm).length) u (v' ++ v.map nrm) hU g hgGV hgε
    have hlenw : (wL u ++ wR v').length = u.length + v'.length := by simp [wL, wR]
    have hexp : 3 * (r + 1) * (u.length + (v' ++ v.map nrm).length) =
        3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length := by
      rw [hlenw, List.length_append, List.length_map]; ring
    rw [hexp] at hb
    have hX' : 0 ≤ gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length) :=
      pow_nonneg hX _
    have hi : u.length + (v' ++ v.map nrm).length < n + v.length + 1 := by
      rw [List.length_append, List.length_map]; omega
    have hCi : Cf (u.length + (v' ++ v.map nrm).length) ≤
        ∑ j ∈ Finset.range (n + v.length + 1), |Cf j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 hi))
    have hnorm : ‖(((v.map nz).prod : ℝ) : ℂ)‖ = |(v.map nz).prod| := by
      first
      | simp
      | rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |(v.map nz).prod| * ‖dLR u (v' ++ v.map nrm) E g‖
        ≤ |(v.map nz).prod| * (Cf (u.length + (v' ++ v.map nrm).length) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(v.map nz).prod| * ((∑ j ∈ Finset.range (n + v.length + 1), |Cf j|) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCi hX') (abs_nonneg _)
      _ = _ := by ring
  · intro g₀ hg₀
    obtain ⟨f', hf', V, hV, hgV, he⟩ := lss_of_ckOn hE1 hSsub g₀ hg₀
    refine ⟨Rw v f', ?_, V, hV, hgV, fun g' hg' hg'V => rw_congr_on_open_of_eq_on_GV hV he v hv g' hg' hg'V⟩
    rw [← Dw_wR]
    exact cdw _ hf'

end fac

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_of_lss {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfe⟩ := h g hg
  refine ⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩
  exact WithTop.coe_le_coe.mpr le_top

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

private lemma contDiff_of_isPolyDeg {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg κ P) :
    ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := hP
  rw [show P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2)
    (fun x => star (g x.1 x.2))) q from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with x | x
    · exact contDiff_apply_apply ℝ ℂ x.1 x.2
    · exact Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ x.1 x.2)

private lemma exists_bound_iteratedFDeriv_cutoff_normSq {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (j : ℕ) :
    ∃ B : ℝ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ j (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ)) y‖ ≤ B := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set Φ : ℂ → ℂ := fun y => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ) with hΦdef
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hΦ : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp (hs.comp (hns.div_const de))
  have hc : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top))
  have hconst : ∀ (c x y : ℂ), iteratedFDeriv ℝ j (fun _ : ℂ => c) x =
      iteratedFDeriv ℝ j (fun _ : ℂ => c) y := by
    intro c x y
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_const_of_ne hj.ne']
      rfl
  obtain ⟨c, R, hR0, hloc⟩ : ∃ c : ℂ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℂ, R < ‖y‖ → Φ =ᶠ[nhds y] fun _ => c := by
    rcases le_or_gt de 0 with hde | hde
    · refine ⟨0, 0, le_rfl, fun y _ => Filter.Eventually.of_forall fun z => ?_⟩
      have hz : Complex.normSq z / de ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg z) hde
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 0
      rw [h0 _ (by linarith)]
      simp
    · refine ⟨1, de + 1, by linarith, fun y hy => ?_⟩
      have hopen : IsOpen {z : ℂ | de + 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : de + 1 < ‖z‖ := hz
      have hn : de ≤ Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg z]
      have h1' : 1 ≤ Complex.normSq z / de := by
        rw [le_div_iff₀ hde]
        linarith
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 1
      rw [h1 _ h1']
      simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have y0n : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨B, fun y => ?_⟩
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · exact hB y (by rw [mem_closedBall_zero_iff]; exact hy)
  · have e1 := ((hloc y (by linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds
    have e2 := ((hloc ((R + 1 : ℝ) : ℂ) (by rw [y0n]; linarith)).iteratedFDeriv
      (𝕜 := ℝ) j).eq_of_nhds
    rw [e1, hconst c y ((R + 1 : ℝ) : ℂ), ← e2]
    exact hB _ (by rw [mem_closedBall_zero_iff, y0n])

lemma ubl_chi (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    (n : ℕ) : UBL (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) (GV k r) n 0 (2 * r + 2) := by
  have hSG : GV k r ⊆ GV k r := subset_rfl
  have e0 : (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) =
      fun g => ∏ l ∈ L, ((χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de) : ℝ) : ℂ) := by
    funext g
    simp [C6.chiAll]
  rw [e0]
  apply ubl_prod hSG L
  intro l _
  obtain ⟨C, hC0, hC⟩ := (ubl_poly (dmin_pd k r D.z D.z' l) (GV k r) hSG n 0).1
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  refine ubl_fdb (fun g => Dmin k r D.z D.z' g l) (contDiff_of_isPolyDeg (dmin_pd k r D.z D.z' l)) (GV k r) hSG
    Set.univ (fun _ _ => trivial) (2 * r + 2) n C ?_
    (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hχ.1.comp (hns.div_const de))) (fun j => ?_)
  · intro w hw hne g hg
    refine (hC w hw g hg).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    apply pow_le_pow_right₀ (gN_ge_one hg)
    have hl : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    simpa using Nat.le_mul_of_pos_right (2 * r + 2) hl
  · obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv_cutoff_normSq hχ de j
    exact ⟨B, fun y _ => hB y⟩

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma fc_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (N : ℕ) :
    CkOn N (GV k r) (C6.cutAll D χ₀ de L F) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted N W → ∀ g ∈ GV k r,
      ‖Dw W (C6.cutAll D χ₀ de L F) g‖ ≤ C * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) := by
  obtain ⟨⟨Cχ, hCχ0, hCχ⟩, hlχ⟩ := ubl_chi D hχ de L N
  set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ
  set a : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)
  have hGG : GV k r ⊆ GV k r := le_rfl
  have hua := ub_clm Lid hGG hlχ hCχ
  have hla := lss_clm Lid hlχ
  obtain ⟨c, hc⟩ := hF N
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hP : Pr (∅ : Set (Mat k r)) (GV k r) N a F :=
    ⟨sCkOn_mono le_top (ckOn_of_lss hla ⊤), hc.1, fun _ _ h => absurd h (notMem_empty _)⟩
  have eq : C6.cutAll D χ₀ de L F = ap a F := by
    funext g; simp [C6.cutAll, ap, a, Lid]
  rw [eq]
  refine ⟨hP.ck isOpen_empty hcov, 2 ^ N * (‖Lid‖ * Cχ * max c 0), by positivity, fun W hW g hg => ?_⟩
  have hgp := gN_pos hg
  have hg1 := gN_ge_one hg
  set M := ‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) with hM
  have hb := leib_bound isOpen_empty hcov g hg M W a F (admissible_word_mem_lie hW)
    (hP.mono (by exact_mod_cast admissible_word_length_le hW)) (by
      intro w₁ w₂ h₁ h₂ hl
      have b1 := hua w₁ (Adm_sub h₁ hW) g hg
      have b2 : ‖Dw w₂ F g‖ ≤ max c 0 * gN g ^ (-A₀) := by
        obtain ⟨u, v, hu, hv, hl', hw2⟩ := Adm_sub h₂ hW
        rw [hw2, ← dLR_eq]
        have := hc.2 u v hu hv hl' g hg
        rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgp _), mul_comm]
        exact this.trans (le_max_left _ _)
      have hex : (((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀) ≤ -A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ) := by
        have : (2 * r + 2) * w₁.length ≤ (2 * r + 2) * W.length :=
          Nat.mul_le_mul_left _ (by omega)
        have : (((2 * r + 2) * w₁.length : ℕ) : ℝ) ≤ (((2 * r + 2) * W.length : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      calc ‖Dw w₁ a g‖ * ‖Dw w₂ F g‖
          ≤ (‖Lid‖ * Cχ * gN g ^ (0 + (2 * r + 2) * w₁.length)) * (max c 0 * gN g ^ (-A₀)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
        _ = ‖Lid‖ * Cχ * max c 0 * gN g ^ ((((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀)) := by
            rw [Real.rpow_add hgp, Real.rpow_natCast, zero_add]; ring
        _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg1 hex) (by positivity))
  refine hb.trans ?_
  have h2 : (2 : ℝ) ^ W.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hW)
  rw [hM]
  calc 2 ^ W.length * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)))
      ≤ 2 ^ N * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

lemma phi_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (mm : ℕ) :
    CkOn mm (GV k r) (Rw w (C6.cutAll D χ₀ de L F)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted mm W → ∀ g ∈ GV k r,
      ‖Dw W (Rw w (C6.cutAll D χ₀ de L F)) g‖ ≤
        C * gN g ^ (-A₀ + (((2 * r + 2) * (W.length + w.length) : ℕ) : ℝ)) := by
  obtain ⟨hck, C, hC0, hC⟩ := fc_bound D hχ de L hF (mm + w.length)
  have hwR : ∀ x ∈ wR w, inLie k r x.2 := fun x hx => by
    simp only [wR, List.mem_map] at hx; obtain ⟨X, hX, rfl⟩ := hx; exact hw X hX
  constructor
  · rw [← Dw_wR]
    apply CkOn_Dw hwR
    have : ((mm : ℕ∞) + ((wR w).length : ℕ∞)) = ((mm + w.length : ℕ) : ℕ∞) := by simp [wR]
    rw [this]; exact hck
  · set cw : ℝ := (w.map nz).prod with hcw
    have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (nz_pos X).le
    refine ⟨cw * C, mul_nonneg hcw0 hC0, fun W hW g hg => ?_⟩
    obtain ⟨u, v, hu, hv, hl, rfl⟩ := hW
    have hvn : ∀ X ∈ w.map nrm, unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact nrm_unit (hw Y hY)
    have e1 : Dw (wL u ++ wR v) (Rw w (C6.cutAll D χ₀ de L F)) g =
        ((cw : ℝ) : ℂ) • Dw (wL u ++ wR (v ++ w.map nrm)) (C6.cutAll D χ₀ de L F) g := by
      rw [Rw_scale, Dw_smul]
      simp only [hcw]
      congr 1
      rw [← Dw_wR, ← Dw_append]
      simp [wR, List.append_assoc]
    have hA : admitted (mm + w.length) (wL u ++ wR (v ++ w.map nrm)) :=
      ⟨u, v ++ w.map nrm, hu, fun X hX => (List.mem_append.1 hX).elim (hv X) (hvn X), by simp; omega, rfl⟩
    rw [e1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hlen' : (wL u ++ wR (v ++ w.map nrm)).length = (wL u ++ wR v).length + w.length := by
      simp [wL, wR]; ring
    rw [← hlen']
    exact hC _ hA g hg

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end Formalism.FourierDecayAlt.P
end
end
