import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HderEntry
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LgCpt

section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.rdcalc :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V],
      (∀ f f' : Mat n → V, Set.EqOn f f' (GLs n) → ∀ X, Set.EqOn (Rd X f) (Rd X f') (GLs n)) ∧
      ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
        (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
        ∀ h ∈ GLs n, ∀ X, ∀ g ∈ GLs n, Rd X (fun y => f (h * y)) g = Rd X f (h * g) ∧
          Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  intro n V _ _
  refine ⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf =>
    ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg,
      fun h hh X g hg => ?_⟩⟩
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hhg : h * g ∈ GLs n := by
    show (h * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hh hg
  have hgh : g * h ∈ GLs n := by
    show (g * h).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  constructor
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg
    have hc : HasFDerivAt (fun y : Mat n => f (h * y))
        ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh
    have hc : HasFDerivAt (fun y : Mat n => f (y * h))
        ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt
    have e : g * h * (h⁻¹ * X * h) = g * X * h := by
      rw [Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet,
        Matrix.one_mul, Matrix.mul_assoc]
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]
end
end

section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem eu_loc (s : Bool) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro x hx
  have h1 := (UpperTheory.RealTr.rdcalc n V).1 f f' h
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1 _ hx]

private theorem eu_smo (s : Bool) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h1 := ((UpperTheory.RealTr.rdcalc n V).2 f h).1
  exact ((h1 _).add ((h1 _).const_smul _)).const_smul _

private theorem rd_smul (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Set.EqOn (Rd X (fun y => c • f y)) (fun y => c • Rd X f y) (GLs n) := by
  intro g hg
  have hd : DifferentiableAt ℝ f g :=
    (h.differentiableOn (by simp)).differentiableAt (((UpperTheory.RealTr.basic n).1).mem_nhds hg)
  have e : fderiv ℝ (fun y => c • f y) g = c • fderiv ℝ f g := (hd.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, e]
  rfl

private theorem eu_smul (s : Bool) (a b : Fin n) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Eu s a b (fun y => c • f y)) (fun y => c • Eu s a b f y) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_smul c h _ hx]
  rw [smul_comm _ c, ← smul_add, smul_comm]

private theorem epow_loc (s : Bool) (m : ℕ) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d _ => eu_loc s a d (ih d b) hx

private theorem epow_smo (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    simp only [Epow.eq_1]
    split_ifs
    · exact h
    · exact contDiffOn_const
  | succ m ih =>
    simp only [Epow.eq_2]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun d _ => eu_smo s a d (ih d b)

private theorem epow_smul (s : Bool) (m : ℕ) (a b : Fin n) (c : ℂ) {f : Mat n → V}
    (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Epow s m a b (fun y => c • f y)) (fun y => c • Epow s m a b f y) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs <;> simp
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eu_loc s a d (ih d b) hx]
    exact eu_smul s a d c (epow_smo s m d b h) hx

private theorem gel_loc (s : Bool) (m : ℕ) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_loc s m a a h hg

private theorem gel_smul (s : Bool) (m : ℕ) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (gel s m (fun y => c • f y)) (fun y => c • gel s m f y) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => epow_smul s m a a c h hg

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.zEig :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (χ : Inf n) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → IsEig χ f →
      ∀ c : ℂ, (∀ x ∈ GLs n, Om (fun y => c • f y) x = cas χ • c • f x) ∧
        ∀ (w : List (Bool × ℕ)), ∀ x ∈ GLs n, zOp w (fun y => c • f y) x = (c * zVal w χ) • f x := by
  intro n V _ _ χ f hf hE c
  refine ⟨fun x hx => ?_, fun w => ?_⟩
  · simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul _ _ c hf hx, hE _ _ x hx, cas]
    module
  · induction w with
    | nil =>
      intro x hx
      simp [zOp.eq_1, zVal]
    | cons p w ih =>
      intro x hx
      simp only [zOp.eq_2]
      rw [gel_loc p.1 p.2 ih hx, gel_smul p.1 p.2 _ hf hx]
      beta_reduce
      rw [hE _ _ x hx]
      simp only [zVal, List.map_cons, List.prod_cons, smul_smul]
      ring_nf
end
end

section
noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem hasDerivAt_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) ((a * Complex.sinh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_cosh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

private theorem hasDerivAt_sinh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.sinh ((s : ℂ) * a) • v) ((a * Complex.cosh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_sinh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

private theorem iteratedDeriv_two_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) t
      = (a * a * Complex.cosh ((t : ℂ) * a)) • v := by
  have hd : deriv (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v)
      = fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v) := by
    funext s
    rw [(hasDerivAt_cosh_smul' a v s).deriv, mul_smul]
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h : HasDerivAt (fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v))
      (a • ((a * Complex.cosh ((t : ℂ) * a)) • v)) t := (hasDerivAt_sinh_smul' a v t).const_smul a
  rw [h.deriv, smul_smul, mul_assoc]

private theorem half_mul_half' (c : ℂ) : c ^ (1 / 2 : ℂ) * c ^ (1 / 2 : ℂ) = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Complex.zero_cpow (by norm_num)]
    ring
  · rw [← Complex.cpow_add _ _ hc]
    norm_num

private theorem contDiff_cosh_fst {n : ℕ} (a : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh ((p.1 : ℂ) * a)) := by
  have h0 : ContDiff ℝ ∞ Complex.cosh := Complex.contDiff_cosh.restrict_scalars ℝ
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact h0.comp (h1.mul contDiff_const)

private theorem eigWave {n : ℕ} (E : KMod n) (χ : Inf n) (f : Mat n → E.V) (hf : f ∈ CE E) (he : IsEig χ f) :
    IsWave E (fun (t : ℝ) y => Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) := by
  have ha2 := half_mul_half' (cas χ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact (contDiff_cosh_fst _).contDiffOn.smul h2
  · intro t
    refine ⟨contDiffOn_const.smul hf.1, ?_⟩
    intro g hg k
    simp only [hf.2 g hg k, map_smul]
  · intro t g hg
    have h := ((UpperTheory.RealTr.zEig n E.V χ f hf.1 he (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)))).1 g hg)
    beta_reduce
    rw [iteratedDeriv_two_cosh_smul', h, ha2, smul_smul]
  · intro g hg
    beta_reduce
    rw [(hasDerivAt_cosh_smul' _ (f g) 0).deriv]
    simp

private theorem val_mem_GLs' {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  exact ((UpperTheory.RealTr.basic n).2.1 _).2 y.isUnit

private theorem integrable_ker {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (hc : ContinuousOn κ (GLs n))
    (hs : ∃ R, ∀ y ∈ GLs n, R < lg y → κ y = 0) (f : Mat n → E.V) (hf : ContinuousOn f (GLs n))
    (x : Mat n) (hx : x ∈ GLs n) : Integrable (fun y : G n => κ y.val (f (x * y.val))) μ := by
  obtain ⟨R, hR⟩ := hs
  have hcont : Continuous (fun y : G n => κ y.val (f (x * y.val))) := by
    refine Continuous.clm_apply (hc.comp_continuous Units.continuous_val fun y => val_mem_GLs' y) ?_
    refine hf.comp_continuous (continuous_const.mul Units.continuous_val) fun y => ?_
    show det (x * y.val) ≠ 0
    rw [det_mul]
    exact mul_ne_zero hx (val_mem_GLs' y)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (UpperTheory.RealTr.lgCpt n R) ?_)
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  simp [hR _ (val_mem_GLs' y) hy]

theorem UpperTheory.RealTr.actEig :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T →
      ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  intro n _ _ μ _ E k val T hM χ f hf he x hx
  obtain ⟨m, c, w, g, ks, hks, hk, hval⟩ := hM
  have hf' := hf
  obtain ⟨hf1, hf2⟩ := hf'
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := fun i =>
    integrable_ker μ E (ks i) (hks i).2.1.continuousOn (hks i).2.2.1 f hf1.continuousOn x hx
  have hu := eigWave E χ f hf he
  have hact : ∀ i, act μ E (ks i) f x = (coshT (g i) (cas χ) * zVal (w i) χ) • f x := by
    intro i
    have key := (hks i).2.2.2.2 _ hu x hx
    have e1 : act μ E (ks i) f x =
        act μ E (ks i) (fun y => Complex.cosh (((0 : ℝ) : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) x := by
      simp
    have e2 : (fun x' => ∫ t : ℝ, ((g i t : ℝ) : ℂ) • (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f x')) =
        fun x' => coshT (g i) (cas χ) • f x' := by
      funext x'
      simp only [smul_smul]
      rw [integral_smul_const]
      rfl
    rw [e1]
    refine key.trans ((congrArg (fun F => zOp (w i) F x) e2).trans ?_)
    exact (UpperTheory.RealTr.zEig n E.V χ f hf1 he _).2 (w i) x hx
  have hk' : ∀ y : G n, k y.val = ∑ i, c i • ks i y.val := fun y => hk _ (val_mem_GLs' y)
  have hsum : act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
    simp only [act, hk', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [integral_finset_sum]
    · simp only [integral_smul]
    · intro i _
      exact (hint i).smul (c i)
  rw [hsum, hval]
  simp only [hact, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring
end
end
