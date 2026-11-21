import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ChainOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Eq

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_equiv (A : V ≃L[ℂ] V) (X : Mat n) (f : Mat n → V) : Rd X (fun x => A (f x)) = fun x => A (Rd X f x) := by
  funext g
  show fderiv ℝ (fun x => A (f x)) g (g * X) = A (fderiv ℝ f g (g * X))
  by_cases hf : DifferentiableAt ℝ f g
  · have h : HasFDerivAt (fun x => A (f x)) ((A.restrictScalars ℝ : V →L[ℝ] V).comp (fderiv ℝ f g)) g :=
      (A.restrictScalars ℝ : V →L[ℝ] V).hasFDerivAt.comp g hf.hasFDerivAt
    rw [h.fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (fun x => A (f x)) g := by
      intro h
      apply hf
      have h2 : DifferentiableAt ℝ (fun x => A.symm (A (f x))) g :=
        (A.symm.restrictScalars ℝ : V →L[ℝ] V).differentiableAt.comp g h
      simpa using h2
    rw [fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hf]
    simp

theorem eu_equiv (A : V ≃L[ℂ] V) (s : Bool) (a b : Fin n) (f : Mat n → V) :
    Eu s a b (fun x => A (f x)) = fun x => A (Eu s a b f x) := by
  unfold Eu
  rw [rd_equiv, rd_equiv]
  funext x
  by_cases hs : s = true <;> simp [hs, map_add, map_smul]

theorem epow_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) (f : Mat n → V),
    Epow s m a b (fun x => A (f x)) = fun x => A (Epow s m a b f x) := by
  induction m with
  | zero =>
    intro a b f
    rw [Epow.eq_1]
    funext x
    split_ifs <;> simp
  | succ m ih =>
    intro a b f
    rw [Epow.eq_2]
    simp only [ih, eu_equiv]
    funext x
    simp [Finset.sum_apply, map_sum]

theorem gel_equiv (A : V ≃L[ℂ] V) (s : Bool) (m : ℕ) (f : Mat n → V) :
    gel s m (fun x => A (f x)) = fun x => A (gel s m f x) := by
  unfold gel
  simp only [epow_equiv]
  funext x
  simp [Finset.sum_apply, map_sum]

theorem om_equiv (A : V ≃L[ℂ] V) (f : Mat n → V) : Om (fun x => A (f x)) = fun x => A (Om f x) := by
  unfold Om
  rw [gel_equiv, gel_equiv]
  funext x
  simp [map_add, map_nsmul]

theorem zop_equiv (A : V ≃L[ℂ] V) : ∀ (w : List (Bool × ℕ)) (f : Mat n → V),
    zOp w (fun x => A (f x)) = fun x => A (zOp w f x) := by
  intro w
  induction w with
  | nil =>
    intro f
    simp [zOp.eq_1]
  | cons p w ih =>
    intro f
    rw [zOp.eq_2]
    simp only [ih, gel_equiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Eq
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Loc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') U := by
  intro x hx
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') U := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h _ hx, rd_congr hU h _ hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (Epow s m a b f) (Epow s m a b f') U := by
  induction m with
  | zero =>
    intro a b f f' h x hx
    simp only [Epow]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro a b f f' h x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (ih c b h) s a c hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') U := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx

theorem zop_congr {U : Set (Mat n)} (hU : IsOpen U) : ∀ (w : List (Bool × ℕ)) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (zOp w f) (zOp w f') U := by
  intro w
  induction w with
  | nil => intro f f' h; exact h
  | cons p w ih => intro f f' h; exact gel_congr hU (ih h) p.1 p.2

theorem integrable_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (hF : ContinuousOn F (GLs n))
    (hc : Cpt F) : Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hc
  have hcont : Continuous fun y : G n => F y.val := by
    refine hF.comp_continuous (Units.continuous_val) fun y => ?_
    show (y.val).det ≠ 0
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
  have hlg : ContinuousOn (lg (n := n)) (GLs n) := (hL n).2.2.2.1.continuousOn
  have hK : IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1 R
  have hclosed : IsClosed {y : G n | lg y.val ≤ R} := by
    have : Continuous fun y : G n => lg y.val :=
      hlg.comp_continuous Units.continuous_val fun y => (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero
    exact isClosed_le this continuous_const
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hK ?_
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  exact hR _ ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero) hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Loc
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Gam

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem iteratedDeriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (k : ℕ)
    (t : ℝ) : iteratedDeriv k (fun s => A (φ s)) t = A (iteratedDeriv k φ t) := by
  have h := (A.restrictScalars ℝ).iteratedFDeriv_comp_left (f := φ) (x := t) (i := k)
  have h2 := congrArg (fun L => L (fun _ : Fin k => (1 : ℝ))) h
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem deriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (t : ℝ) :
    deriv (fun s => A (φ s)) t = A (deriv φ t) := by
  have := iteratedDeriv_equiv A φ 1 t
  simpa only [iteratedDeriv_one] using this

theorem wave_equiv (E : KMod n) (A : E.V ≃L[ℂ] E.V) (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v))
    (u : ℝ → Mat n → E.V) (hu : IsWave E u) : IsWave E fun t x => A (u t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn h1
  · intro t
    refine ⟨(A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn (h2 t).1, ?_⟩
    intro g hg k
    simp only
    rw [(h2 t).2 g hg k, hA]
  · intro t g hg
    rw [iteratedDeriv_equiv A (fun s => u s g) 2 t, h3 t g hg, om_equiv]
  · intro g hg
    rw [deriv_equiv A (fun s => u s g) 0, h4 g hg, map_zero]

theorem act_equiv (hWE : WaveEx) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : E.V ≃L[ℂ] E.V)
    (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v)) (w : List (Bool × ℕ)) (g : ℝ → ℝ)
    (ks : Mat n → (E.V →L[ℂ] E.V)) (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (fun x => A (f x)) 1 = A (act μ E ks f 1) := by
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have hAu := wave_equiv E A hA u hu
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have key : ∀ F F' : Mat n → E.V, Set.EqOn F F' (GLs n) → act μ E ks F 1 = act μ E ks F' 1 := by
    intro F F' h
    unfold act
    congr 1
    funext y
    rw [h]
    simp only [GLs, Set.mem_setOf_eq, one_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  rw [key (fun x => A (f x)) (fun x => A (u 0 x)) (fun x hx => by simp only [hu0 x hx]),
    key f (u 0) (fun x hx => (hu0 x hx).symm),
    hks.2.2.2 _ hAu 1 hone, hks.2.2.2 _ hu 1 hone]
  refine Eq.trans ?_ (congrFun (zop_equiv A w _) 1)
  congr 2
  funext x'
  rw [← A.integral_comp_comm]
  congr 1
  funext t
  exact ((A : E.V →L[ℂ] E.V).map_smul_of_tower (g t) (u t x')).symm

end PositivityTheory.RgBcC.LfSt.ChainPf.Gam
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) :
    Set.EqOn (DC ε Fr f) (DC ε Fr f') U := by
  intro x hx
  have hev : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  simp only [DC, Rd, hev.fderiv_eq, h hx]

theorem cont_partial {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (x : Mat n) (hx : x ∈ GLs n) (X : Mat n) :
    Continuous (fun t => u t x) ∧ Continuous (fun t => Rd X (u t) x) := by
  have hs : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod (isOpen_GLs n)
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ GLs n) :=
    hu.continuousOn_fderiv_of_isOpen hs (by simp)
  have key : ∀ t, fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n)) := by
    intro t
    have hd : DifferentiableAt ℝ (Function.uncurry u) (t, x) :=
      (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ⟨Set.mem_univ _, hx⟩)
    exact (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hline : Continuous fun t : ℝ => ((t, x) : ℝ × Mat n) := continuous_id.prodMk continuous_const
  constructor
  · exact hu.continuousOn.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)
  · simp only [Rd, key, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (hc.comp_continuous hline (fun t => ⟨Set.mem_univ _, hx⟩)).clm_apply continuous_const

theorem bump_cpt (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T) : HasCompactSupport fun t => (g t : ℂ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
  intro t ht
  simp only [Complex.ofReal_eq_zero]
  exact hgb.2.2 t (by simpa [Real.norm_eq_abs, not_le] using ht)

theorem int_bump {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (φ : ℝ → V) (hφ : Continuous φ) : Integrable fun t => (g t : ℂ) • φ t := by
  refine ((Complex.continuous_ofReal.comp hgb.1.continuous).smul hφ).integrable_of_hasCompactSupport ?_
  exact (bump_cpt g T hgb).smul_right

theorem param_dc {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) (u : ℝ → Mat n → V)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)) (g : ℝ → ℝ) (T : ℝ) (hgb : IsBump g T)
    (hRd : ∀ X, ∀ x ∈ GLs n, Rd X (fun x' => ∫ t, (g t : ℂ) • u t x') x = ∫ t, (g t : ℂ) • Rd X (u t) x)
    (x : Mat n) (hx : x ∈ GLs n) :
    ∫ t, (g t : ℂ) • DC ε Fr (u t) x = DC ε Fr (fun x' => ∫ t, (g t : ℂ) • u t x') x := by
  have hc := fun X => cont_partial u hu x hx X
  have ia : ∀ X, Integrable (fun t => (g t : ℂ) • Rd X (u t) x) := fun X => int_bump g T hgb _ (hc X).2
  have ib : Integrable (fun t => (g t : ℂ) • u t x) := int_bump g T hgb _ (hc 0).1
  have iab : ∀ p : Fin n × Fin n, Integrable (fun t => (g t : ℂ) • Rd (hb p) (u t) x +
      (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) :=
    fun p => (ia _).add ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib)
  have hpt : ∀ t, (g t : ℂ) • DC ε Fr (u t) x = ∑ p : Fin n × Fin n, ε (hb p)
      ((g t : ℂ) • Rd (hb p) (u t) x + (fderiv ℝ Fr 1 (hb p)) ((g t : ℂ) • u t x)) := by
    intro t
    simp only [DC, Finset.smul_sum, map_add, map_smul, smul_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finset_sum _ (fun p _ => (ε (hb p)).integrable_comp (iab p))]
  simp only [DC, hRd _ x hx]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [(ε (hb p)).integral_comp_comm (iab p),
    integral_add (ia _) ((fderiv ℝ Fr 1 (hb p)).integrable_comp ib),
    (fderiv ℝ Fr 1 (hb p)).integral_comp_comm ib]

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_of (y : G n) : y.val ∈ GLs n := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero

theorem mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem act_congr [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    {F F' : Mat n → E.V} (h : Set.EqOn F F' (GLs n)) {x : Mat n} (hx : x ∈ GLs n) : act μ E k F x = act μ E k F' x := by
  simp only [act]
  exact integral_congr_ae (Eventually.of_forall fun y => by
    show (k y.val) (F (x * y.val)) = (k y.val) (F' (x * y.val))
    rw [h (mul_mem_GLs hx (mem_GLs_of y))])

theorem act_dc (hDW : DCwave) (hP : ParamInt) (hZ : ZopDC) (hG : GelComm) (hWE : WaveEx) {lam : Fin n → ℤ} {E : KMod n}
    {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T' : ℝ) (hgb : IsBump g T') (ks : Mat n → (E.V →L[ℂ] E.V))
    (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (DC ε Fr f) 1 = DC ε Fr (act μ E ks f) 1 := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hDu := hDW hG n lam E Fr ε ι S Γ T hC u hu
  have hk1 := hks.2.2.2 _ hDu 1 h1
  obtain ⟨hPs, hPd⟩ := hP n E u hu g T' hgb
  have eqA : Set.EqOn (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') (GLs n) :=
    fun x hx => param_dc ε Fr u hu.1 g T' hgb hPd x hx
  have hz := hZ hG n lam E Fr ε ι S Γ T hC (fun x' => ∫ t, (g t : ℂ) • u t x') hPs w
  have eqB : Set.EqOn (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') (act μ E ks f) (GLs n) := by
    intro x hx
    rw [← hks.2.2.2 u hu x hx]
    exact act_congr μ E ks (fun y hy => hu0 y hy) hx
  have eq0 : Set.EqOn (DC ε Fr f) (DC ε Fr (u 0)) (GLs n) :=
    dc_congr ε Fr (isOpen_GLs n) fun y hy => (hu0 y hy).symm
  calc act μ E ks (DC ε Fr f) 1 = act μ E ks (DC ε Fr (u 0)) 1 := act_congr μ E ks eq0 h1
    _ = zOp w (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') 1 := hk1
    _ = zOp w (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') 1 := zop_congr (isOpen_GLs n) w eqA h1
    _ = DC ε Fr (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') 1 := hz.2 1 h1
    _ = DC ε Fr (act μ E ks f) 1 := dc_congr ε Fr (isOpen_GLs n) eqB h1

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Ker

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem int_of_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt f) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem act_one [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (F : Mat n → E.V) : act μ E k F 1 = ∫ y : G n, k y.val (F y.val) ∂μ := by
  simp only [act, one_mul]

theorem gamma_of_comm (hKZ : KerZero) (hL : LgFacts) {E : KMod n} (Γ : E.V →L[ℂ] E.V)
    (hΓρ : ∀ k, Γ * E.ρ k = E.ρ k * Γ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n))
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hΓ : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1)) :
    ∀ y ∈ GLs n, Γ * k y = k y * Γ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hz := hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub
      (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by
        simp only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by
      have hfcont : ContinuousOn f (GLs n) := hf.1.continuousOn
      have i1 := int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc
      have i2 := int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub i1 i2]
      have e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1 := by
        rw [act_one]; rfl
      have e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1) := by
        rw [act_one]
        exact ContinuousLinearMap.integral_comp_comm Γ
          (int_of_cpt hL μ k f hkc hfcont hfc)
      rw [e1, e2, hΓ f hf, sub_self])
  intro y hy
  have := hz y hy
  exact (sub_eq_zero.1 this).symm

theorem rd_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Rd X f) (GLs n) :=
  (hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_id.matrix_mul continuous_const).continuousOn

theorem ld_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Ld X f) (GLs n) :=
  ((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_const.matrix_mul continuous_id).continuousOn).neg

def mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
  (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip A

theorem rd_mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V))
    (hk : ContDiffOn ℝ ∞ k (GLs n)) (A : V →L[ℂ] V) (X : Mat n) (y : Mat n) (hy : y ∈ GLs n) :
    Rd X (fun y => k y * A) y = Rd X k y * A := by
  have hd : DifferentiableAt ℝ k y := (hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)
  have e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k := rfl
  have hd2 := (((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [Rd]
  rw [e]
  exact congrArg (fun L => L (y * X)) hd2

theorem kapL_int (hA : ActDer) (hU : Unimod) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    DC ε Fr (act μ E k f) 1 = ∫ y : G n, kapL ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hD := (hA hU n μ E k f hks hkc hf).2
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc
  have iK : Integrable (fun y : G n => k y.val (f y.val)) μ := int_of_cpt hL μ _ f hks.continuousOn hfc' hfc
  have iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ := fun p =>
    ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val))) := by
    intro y
    simp [kapL]
  simp_rw [ek]
  rw [integral_finset_sum _ fun p _ => iP p]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ :=
    integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)
  have e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ =
      ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ iK
  rw [e1, e2, e3, hD _ 1 h1, act_one]
  simp only [one_mul]

theorem int_of_cptK (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt K) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem kapR_int (hI : IBPAct) (hU : Unimod) (hR : RCalc) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    act μ E k (DC ε Fr f) 1 = ∫ y : G n, kapR ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n) := fun p => by
    have e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k := rfl
    rw [e]
    exact ((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks
  have hkc' : ∀ p, Cpt fun y => k y * ε (hb p) := fun p => by
    obtain ⟨R, hR⟩ := hkc
    exact ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ := fun p =>
    int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)
  have iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc
  have iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc
  have eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [DC, map_sum, map_add]
  have eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [kapR]
  rw [act_one]
  simp_rw [eL, eR]
  have sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finset_sum _ fun p _ => (iA p).add (iB p)
  have sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finset_sum _ fun p _ => (iC p).neg.add (iB p)
  rw [sL, sR]
  refine Finset.sum_congr rfl fun p _ => ?_
  have a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iA p) (iB p)
  have a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iC p).neg (iB p)
  rw [a1, a2, integral_neg]
  congr 1
  have hibp := hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1
  simp only [one_mul] at hibp
  rw [hibp]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)
  rw [rd_mr k hks _ _ _ (mem_GLs_of y)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Ker
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Top

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem dc_of_comm (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hKZ : KerZero) (hU : Unimod) (hR : RCalc)
    (hL : LgFacts) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)]
    [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V))
    (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hD : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1) :
    ∀ y ∈ GLs n, kapL ε Fr k y = kapR ε Fr k y := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨cL, cR, heq⟩ := hK n lam E Fr ε ι S Γ T hC k hks hke
  have hz := hKZ n μ E (fun y => kapL ε Fr k y - kapR ε Fr k y) (cL.sub cR)
    (fun y hy k₂ => by simp only [(heq y hy k₂).1, (heq y hy k₂).2, sub_mul]) (fun f hf hfc => by
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub (int_of_cpt hL μ _ f cL hf.1.continuousOn hfc) (int_of_cpt hL μ _ f cR hf.1.continuousOn hfc),
        ← kapL_int hA hU hL Fr ε μ k hks hkc f hf.1 hfc, ← kapR_int hI hU hR hL Fr ε μ k hks hkc f hf.1 hfc, hD f hf,
        sub_self])
  exact fun y hy => sub_eq_zero.1 (hz y hy)

end PositivityTheory.RgBcC.LfSt.ChainPf.Top
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (X : Mat n) : EqOn (Rd X f) (Rd X f') (GLs n) := by
  intro g hg
  have he : f =ᶠ[nhds g] f' := Filter.eventually_of_mem ((isOpen_GLs n).mem_nhds hg) h
  simp only [Rd, he.fderiv_eq]

theorem eu_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_congr h _ hg]

theorem epow_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b, EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | succ m ih =>
    intro a b g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (ih c b) s a c hg

theorem gel_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem rd_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf

end Ops

theorem gel_sum (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type} [Fintype ι]
    (F : ι → Mat n → V) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    ∀ g ∈ GLs n, gel s m (fun y => ∑ i, F i y) g = ∑ i, gel s m (F i) g := by
  classical
  intro g hg
  let Φ : Mat n → (ι → V) := fun y i => F i y
  have hΦ : ContDiffOn ℝ ∞ Φ (GLs n) := contDiffOn_pi.2 hF
  have hsum := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (∑ i, ContinuousLinearMap.proj (R := ℂ) i)
  have hproj : ∀ i, gel s m (F i) g = gel s m Φ g i := by
    intro i
    have := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (ContinuousLinearMap.proj (R := ℂ) i)
    simpa [Φ] using this
  have e : (fun y => ∑ i, F i y) = fun y => (∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => V) i) (Φ y) := by
    funext y; simp [Φ]
  rw [e, hsum]
  simp [hproj]

theorem gel_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (_h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ x ∈ GLs n, gel s m (DC ε Fr f) x = DC ε Fr (gel s m f) x := by
  intro x hx
  have hR : ∀ p, ContDiffOn ℝ ∞ (Rd (hb p) f) (GLs n) := fun p => rd_smooth hf _
  have hD : ∀ p, ContDiffOn ℝ ∞ (fun y => fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hGp : ∀ p, ContDiffOn ℝ ∞ (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => (hR p).add (hD p)
  have hFp : ∀ p, ContDiffOn ℝ ∞ (fun y => ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y))) (GLs n) :=
    fun p => ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (hGp p)
  have e1 : DC ε Fr f = fun y => ∑ p, ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) := rfl
  rw [e1, gel_sum hG _ hFp s m x hx]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [((hG n E.V E.V s m _ (hGp p)).2 x hx).2.2 (ε (hb p))]
  congr 1
  have h2 := gel_sum hG (fun (i : Fin 2) y => if i = 0 then Rd (hb p) f y else fderiv ℝ Fr 1 (hb p) (f y))
    (fun i => by fin_cases i <;> simp [hR p, hD p]) s m x hx
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false] at h2
  have h2' : gel s m (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) x =
      gel s m (Rd (hb p) f) x + gel s m (fun y => fderiv ℝ Fr 1 (hb p) (f y)) x := by
    simpa using h2
  rw [h2', ((hG n E.V E.V s m f hf).2 x hx).2.2 (fderiv ℝ Fr 1 (hb p)), ((hG n E.V E.V s m f hf).2 x hx).1 (hb p)]

theorem zopDC : ZopDC := by
  intro hG n lam E Fr ε ι S Γ T hCx h hh w
  induction w with
  | nil => exact ⟨hh, fun x _ => rfl⟩
  | cons p w ih =>
    obtain ⟨ihs, ihc⟩ := ih
    refine ⟨(hG n E.V E.V p.1 p.2 _ ihs).1, fun x hx => ?_⟩
    show gel p.1 p.2 (zOp w (DC ε Fr h)) x = DC ε Fr (gel p.1 p.2 (zOp w h)) x
    rw [gel_congr (fun y hy => ihc y hy) p.1 p.2 hx]
    exact gel_DC hG hCx (zOp w h) ihs p.1 p.2 x hx

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Set Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Partial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_snd' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) (v : Mat n) :
    fderiv ℝ (fun y => U (s, y)) x v = fderiv ℝ U (s, x) (0, v) := by
  have h : HasFDerivAt (fun y : Mat n => U (s, y)) ((fderiv ℝ U (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) x :=
    hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [h.fderiv]
  rfl

theorem hasDerivAt_fst' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) :
    HasDerivAt (fun t => U (t, x)) (fderiv ℝ U (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × Mat n)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hU.hasFDerivAt.comp_hasDerivAt s hp

theorem fderiv_apply_const' {F : ℝ × Mat n → (ℝ × Mat n →L[ℝ] W)} {q : ℝ × Mat n} (hF : DifferentiableAt ℝ F q)
    (w d : ℝ × Mat n) : fderiv ℝ (fun q' => F q' w) q d = fderiv ℝ F q d w := by
  have h : HasFDerivAt (fun q' => F q' w) ((ContinuousLinearMap.apply ℝ W w).comp (fderiv ℝ F q)) q :=
    (ContinuousLinearMap.apply ℝ W w).hasFDerivAt.comp q hF.hasFDerivAt
  exact congrFun (congrArg DFunLike.coe h.fderiv) d

theorem mixed' {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) (a b : ℝ × Mat n) :
    fderiv ℝ (fun q' => fderiv ℝ U q' a) q b = fderiv ℝ (fun q' => fderiv ℝ U q' b) q a := by
  have hd := hU.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hdq : DifferentiableAt ℝ (fderiv ℝ U) q :=
    (hd.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hs := (hU.contDiffAt (hO.mem_nhds hq)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  rw [fderiv_apply_const' hdq, fderiv_apply_const' hdq]
  exact hs b a

theorem pd_smooth {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) (a : ℝ × Mat n) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ U q a) O :=
  (hU.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem diffAt_of {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) : DifferentiableAt ℝ U q :=
  (hU.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)

end Partial

theorem dc_add_smul (hG : GelComm) {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    (F₁ F₂ : Mat n → E.V) (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) (c : ℂ) :
    ∀ x ∈ GLs n, DC ε Fr (c • (F₁ + F₂)) x = c • (DC ε Fr F₁ x + DC ε Fr F₂ x) := by
  intro x hx
  have hs : ContDiffOn ℝ ∞ (F₁ + F₂) (GLs n) := h₁.add h₂
  simp only [DC]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GlobalTheory.CompanionTheory.RCalc.Rd_smul c (hb p) hs hx, Pi.smul_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add (hb p) h₁ h₂ hx, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, map_add, map_smul, smul_add]
  abel

theorem om_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ∀ x ∈ GLs n, Om (DC ε Fr f) x = DC ε Fr (Om f) x := by
  intro x hx
  have ht := (hG n E.V E.V true 2 f hf).1
  have hfa := (hG n E.V E.V false 2 f hf).1
  have e : Om f = (2 : ℂ) • (gel true 2 f + gel false 2 f) := rfl
  rw [e, dc_add_smul hG _ _ ht hfa 2 x hx]
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [gel_DC hG h f hf true 2 x hx, gel_DC hG h f hf false 2 x hx]

theorem dCwave_of (hin : DCinCE) : DCwave := by
  intro hG n lam E Fr ε ι S Γ T hCx u hu
  obtain ⟨hsm, hCE, heq, h0⟩ := hu
  set O : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hOdef
  have hO : IsOpen O := isOpen_univ.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs
  set Ψ : ℝ × Mat n → E.V := Function.uncurry u with hΨ
  have hmem : ∀ s, ∀ x ∈ GLs n, ((s, x) : ℝ × Mat n) ∈ O := fun s x hx => ⟨Set.mem_univ _, hx⟩
  set A : ℝ × Mat n → E.V := fun q => fderiv ℝ Ψ q (1, 0) with hA
  have hAs : ContDiffOn ℝ ∞ A O := pd_smooth hO hsm (1, 0)
  set B : ℝ × Mat n → E.V := fun q => fderiv ℝ A q (1, 0) with hB
  have hBs : ContDiffOn ℝ ∞ B O := pd_smooth hO hAs (1, 0)
  set D : Fin n × Fin n → (E.V →L[ℂ] E.V) := fun p => fderiv ℝ Fr 1 (hb p) with hD

  have hslice : ∀ s, ∀ x ∈ GLs n, DC ε Fr (u s) x =
      ∑ p, ε (hb p) (fderiv ℝ Ψ (s, x) (0, x * hb p) + D p (Ψ (s, x))) := by
    intro s x hx
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show u s = fun y => Ψ (s, y) from rfl, fderiv_snd' (diffAt_of hO hsm (hmem s x hx))]

  have hΨA : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => u t x) (A (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := Ψ) (diffAt_of hO hsm (hmem s x hx))
  have hAB : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => A (t, x)) (B (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := A) (diffAt_of hO hAs (hmem s x hx))
  have hBom : ∀ s, ∀ x ∈ GLs n, B (s, x) = Om (u s) x := by
    intro s x hx
    rw [← heq s x hx, iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun t => u t x) = fun t => A (t, x) := funext fun t => (hΨA t x hx).deriv
    rw [h1, (hAB s x hx).deriv]
  have hdpsi : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ Ψ (t, x) w) (fderiv ℝ A (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ Ψ q w) (s, x) := diffAt_of hO (pd_smooth hO hsm w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hsm (hmem s x hx) w (1, 0)] at this
  have hdA : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ A (t, x) w) (fderiv ℝ B (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ A q w) (s, x) := diffAt_of hO (pd_smooth hO hAs w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hAs (hmem s x hx) w (1, 0)] at this
  refine ⟨?_, fun t => hin n lam E Fr ε ι S Γ T hCx (u t) (hCE t), ?_, ?_⟩
  ·
    have hsm' : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n =>
        ∑ p, ε (hb p) (fderiv ℝ Ψ q (0, q.2 * hb p) + D p (Ψ q))) O := by
      refine ContDiffOn.sum fun p _ => ?_
      refine ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn ?_
      refine ContDiffOn.add ?_ (((D p).restrictScalars ℝ).contDiff.comp_contDiffOn hsm)
      have hv : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((0 : ℝ), q.2 * hb p)) :=
        contDiff_const.prodMk ((GlobalTheory.CompanionTheory.RCalc.mulR (hb p)).contDiff.comp contDiff_snd)
      exact (hsm.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply hv.contDiffOn
    refine hsm'.congr fun q hq => ?_
    obtain ⟨s, x⟩ := q
    exact hslice s x hq.2
  · intro t g hg
    have hf : ∀ s, (fun s => DC ε Fr (u s) g) s = ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
      fun s => hslice s g hg
    have hf1 : ∀ s, HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g)))) s := by
      intro s
      have : (fun s => DC ε Fr (u s) g) = fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
        funext hf
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdpsi _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hΨA s g hg)))
    have hf2 : ∀ s, HasDerivAt (fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))))
        (∑ p, ε (hb p) (fderiv ℝ B (s, g) (0, g * hb p) + D p (B (s, g)))) s := by
      intro s
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdA _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hAB s g hg)))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have e1 : deriv (fun s => DC ε Fr (u s) g) =
        fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))) := funext fun s => (hf1 s).deriv
    rw [e1, (hf2 t).deriv]
    have hu2 : ContDiffOn ℝ ∞ (u t) (GLs n) := (hCE t).1
    have hom : ContDiffOn ℝ ∞ (Om (u t)) (GLs n) := by
      have ht := (hG n E.V E.V true 2 (u t) hu2).1
      have hfa := (hG n E.V E.V false 2 (u t) hu2).1
      exact (ht.add hfa).const_smul (2 : ℂ)
    rw [om_DC hG hCx (u t) hu2 g hg]
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hBe : EqOn (fun y => B (t, y)) (Om (u t)) (GLs n) := fun y hy => hBom t y hy
    have hev : (fun y => B (t, y)) =ᶠ[𝓝 g] Om (u t) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) hBe
    rw [← fderiv_snd' (diffAt_of hO hBs (hmem t g hg)), hev.fderiv_eq, hBom t g hg]
  · intro g hg
    have hf1 : HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (0, g) (0, g * hb p) + D p (A (0, g)))) 0 := by
      have : (fun s => DC ε Fr (u s) g) =
          fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) := funext fun s => hslice s g hg
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
        ((hdpsi _ 0 g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hΨA 0 g hg)))
    rw [hf1.deriv]
    have hA0 : ∀ x ∈ GLs n, A (0, x) = 0 := fun x hx => by rw [← (hΨA 0 x hx).deriv]; exact h0 x hx
    have hev : (fun y => A (0, y)) =ᶠ[𝓝 g] fun _ => (0 : E.V) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hA0 y hy
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← fderiv_snd' (diffAt_of hO hAs (hmem 0 g hg)), hev.fderiv_eq, hA0 g hg]
    simp

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Fin

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  show det k.1 ≠ 0
  intro h0
  have hd := Matrix.det_of_mem_unitary k.2
  rw [h0] at hd
  have h1 : star (0 : ℂ) * 0 = 1 := hd.1
  simp at h1

theorem act_sum (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) {m : ℕ} (c : Fin m → ℂ) (ks : Fin m → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V))
    (hsum : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) (hcont : ∀ i, ContinuousOn (ks i) (GLs n)) (hcpt : ∀ i, Cpt (ks i))
    (F : Mat n → E.V) (hF : ContinuousOn F (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    act μ E k F x = ∑ i, c i • act μ E (ks i) F x := by
  unfold act
  have hFx : ContinuousOn (fun z => F (x * z)) (GLs n) :=
    hF.comp (continuous_const.mul continuous_id).continuousOn (fun z hz => mul_mem_GLs hx hz)
  have hint : ∀ i, Integrable (fun y : G n => (ks i ↑y) (F (x * ↑y))) μ :=
    fun i => int_of_cptK hL μ (ks i) (fun z => F (x * z)) (hcont i) hFx (hcpt i)
  have hint' : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun y : G n => c i • (ks i ↑y) (F (x * ↑y))) μ :=
    fun i _ => (hint i).smul (c i)
  have hfun : (fun y : G n => (k ↑y) (F (x * ↑y))) = fun (y : G n) => ∑ i, c i • (ks i ↑y) (F (x * ↑y)) := by
    funext y
    rw [hsum _ (mem_GLs_of y)]
    simp [ContinuousLinearMap.sum_apply]
  rw [hfun, integral_finset_sum _ hint']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul]

theorem dc_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {m : ℕ} (c : Fin m → ℂ) (h : Fin m → Mat n → V)
    (hd : ∀ i, DifferentiableAt ℝ (h i) 1) :
    DC ε Fr (fun x => ∑ i, c i • h i x) 1 = ∑ i, c i • DC ε Fr (h i) 1 := by
  have hsd : HasFDerivAt (fun x => ∑ i, c i • h i x) (∑ i, c i • fderiv ℝ (h i) 1) 1 :=
    HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt.const_smul (c i)
  simp only [DC, Rd, hsd.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sum,
    map_smul, Finset.smul_sum, smul_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add, map_smul]

end PositivityTheory.RgBcC.LfSt.ChainPf.Fin
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Done

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top
  PositivityTheory.RgBcC.LfSt.ChainPf.Fin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem chainOf'_of (hDC : DCinCE) (hP : ParamInt) (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hU : Unimod)
    (hR : RCalc) (hL : LgFacts) : ChainOf' := by
  intro hWE _hWS hG hKZ n lam E Fr ε ι S Γ T hC _ _ μ _ k val τ hk
  haveI := FiniteDimensional.complete ℂ E.V
  have hDW : DCwave := PositivityTheory.RgBcC.LfSt.ChainOf2.dCwave_of hDC
  have hZ : ZopDC := PositivityTheory.RgBcC.LfSt.ChainOf2.zopDC
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hk
  have hks1 : ∀ i, ContDiffOn ℝ ∞ (ks i) (GLs n) := fun i => (hks i).2.1
  have hkc1 : ∀ i, Cpt (ks i) := fun i => (hks i).2.2.1
  have hke1 : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ks i (y * k₂.1) = ks i y * E.ρ k₂ := by
    intro i y hy k₂
    have := (hks i).2.2.2.1 y hy 1 k₂
    simpa using this

  have hsm : ContDiffOn ℝ ∞ k (GLs n) :=
    (ContDiffOn.sum fun i _ => (hks1 i).const_smul (c i)).congr fun y hy => hsum y hy
  have hcp : Cpt k := by
    choose R hR using hkc1
    refine ⟨∑ i, max (R i) 0, fun y hy hlt => ?_⟩
    rw [hsum y hy]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ j, max (R j) 0 :=
      (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (R j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i))
    rw [hR i y hy (lt_of_le_of_lt hle hlt), smul_zero]
  have hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂ := by
    intro y hy k₂
    rw [hsum _ (mul_mem_GLs hy (unitary_mem_GLs k₂)), hsum y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hke1 i y hy k₂, smul_mul_assoc]
  have hcont : ∀ i, ContinuousOn (ks i) (GLs n) := fun i => (hks1 i).continuousOn
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]

  let ΓE : E.V ≃L[ℂ] E.V := ContinuousLinearEquiv.equivOfInverse Γ Γ
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
  have hΓρ : ∀ k₀ : Matrix.unitaryGroup (Fin n) ℂ, Γ * E.ρ k₀ = E.ρ k₀ * Γ := by
    intro k₀
    have := hC.ΓFr k₀.1 (unitary_mem_GLs k₀)
    rwa [hC.onK] at this
  have hA' : ∀ (k₀ : Matrix.unitaryGroup (Fin n) ℂ) v, ΓE (E.ρ k₀ v) = E.ρ k₀ (ΓE v) := by
    intro k₀ v
    show Γ (E.ρ k₀ v) = E.ρ k₀ (Γ v)
    rw [← ContinuousLinearMap.mul_apply, hΓρ]
    rfl
  have hΓc : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1) := by
    intro f hf
    have hfΓ : ContinuousOn (fun x => Γ (f x)) (GLs n) := continuousOn_const.clm_apply hf.1.continuousOn
    rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hfΓ 1 h1, act_sum hL μ E c ks k hsum hcont hkc1 _ hf.1.continuousOn 1 h1,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    exact act_equiv hWE μ E ΓE hA' (w i) (g i) (ks i) (hks i).2 f hf

  have hDc : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1 := by
    intro f hf
    have hDf := hDC n lam E Fr ε ι S Γ T hC f hf
    have hsmooth : ∀ i, ContDiffOn ℝ ∞ (act μ E (ks i) f) (GLs n) := fun i =>
      (hA hU n μ E (ks i) f (hks1 i) (hkc1 i) hf.1).1
    have eqk : Set.EqOn (act μ E k f) (fun x => ∑ i, c i • act μ E (ks i) f x) (GLs n) := fun x hx =>
      act_sum hL μ E c ks k hsum hcont hkc1 f hf.1.continuousOn x hx
    rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hDf.1.continuousOn 1 h1, dc_congr ε Fr (isOpen_GLs n) eqk h1,
      dc_sum ε Fr c _ fun i => ((hsmooth i).differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds h1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_dc hDW hP hZ hG hWE hC μ (w i) (g i) τ (hks i).1 (ks i) (hks i).2 f hf]
  intro y hy
  refine ⟨gamma_of_comm hKZ hL Γ hΓρ μ k hsm.continuousOn hke hΓc y hy, ?_⟩
  exact dc_of_comm hA hI hK hKZ hU hR hL hC μ k hsm hcp hke hDc y hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Done
end
end
