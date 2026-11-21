import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEqStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QInertHolds
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.StandardTraceAddCharIsStandardCharOfAdmissibleCM

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.TauSpanIdentities

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem fin_smul_eq (z : AEF F E) :
    (pairA F 0 1 : AF F) • z = (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id (finPartF F E z) : AEF F E) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]; rfl
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    show _ = TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (a ⊗ₜ[F] e))
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add z z' hz hz' => rw [smul_add, hz, hz', map_add (finPartF F E)]; exact (map_add (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id) _ _).symm

theorem inf_smul_eq (z : AEF F E) :
    (pairA F 1 0 : AF F) • z = (TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id (infPartF F E z) : AEF F E) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]; rfl
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    show _ = TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (a ⊗ₜ[F] e))
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' => rw [smul_add, hz, hz', map_add (infPartF F E)]; exact (map_add (TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id) _ _).symm

theorem finIdem_mul_of_fin {z : AEF F E} (hz : infPartF F E z = 0) : finIdem F E * z = z := by
  have h1 : (pairA F 0 1 : AF F) + pairA F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := inf_smul_eq z
  rw [hz, map_zero] at h2
  rw [finIdem, ← Algebra.smul_def]
  calc (pairA F 0 1 : AF F) • z = pairA F 0 1 • z + pairA F 1 0 • z := by rw [h2]; exact (add_zero _).symm
    _ = z := by rw [← add_smul, h1, one_smul]

theorem finIdem_mul_of_real {z : AEF F E} (hz : finPartF F E z = 0) : finIdem F E * z = 0 := by
  rw [finIdem, ← Algebra.smul_def, fin_smul_eq, hz, map_zero]; rfl

theorem finPartF_finIdem : finPartF F E (finIdem F E) = 1 := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem cAF_inc (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  simp [cAF, incAF, sigR, inclR]

theorem finIdem_smul_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : finIdem F E • u = u := by
  funext i j
  exact finIdem_mul_of_fin (congrFun (congrFun hu i) j)

theorem finIdem_smul_of_real {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) : finIdem F E • u = 0 := by
  funext i j
  exact finIdem_mul_of_real (congrFun (congrFun hu i) j)

theorem piWF_iotaVF (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : piWF θ (iotaVF ι v) = v := by
  funext p
  exact hι.comp _ p.2

theorem piWF_ratWF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := by
  funext p
  exact PositivityTheory.ThKW.RealC.theta_inc (C.inf p.2) _

theorem finIdem_add_iota (hι : IsChartF θ ι) (x : WOF F E nS nT) : x = finIdem F E • x + iotaVF ι (piWF θ x) := by
  funext i j
  show x i j = finIdem F E * x i j + ι (fun w => θ w (infPartF F E (x i j)))
  refine (sub_eq_zero.1 (hι.ext _ ?_ ?_)).symm.symm
  · simp only [map_sub, map_add, map_mul, finPartF_finIdem, one_mul, hι.fin, add_zero, sub_self]
  · intro w
    simp only [map_sub, map_add, map_mul, infPartF_finIdem, zero_mul, zero_add, hι.comp, sub_self]

theorem continuous_piWF (C : Ctx σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  continuous_pi fun p => (PositivityTheory.ThKW.RealC.continuous_theta (C.inf p.2)).comp
    ((continuous_apply p.1.2).comp (continuous_apply p.1.1))

theorem beta_iota_right (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).1
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_left, h0, zero_add,
    GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring

theorem beta_iota_left (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).2
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_right, h0, zero_add,
    GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring

theorem piWF_add (x y : WOF F E nS nT) : piWF θ (x + y) = piWF θ x + piWF θ y := (piWA θ).map_add x y

theorem piWF_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : piWF θ u = 0 := by
  funext p
  show θ p.2 (infPartF F E (u p.1.1 p.1.2)) = 0
  rw [show infPartF F E (u p.1.1 p.1.2) = 0 from congrFun (congrFun hu p.1.1) p.1.2, map_zero]

theorem actOF_fin (g : GAF σ JS) (h : GAF σ JT) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) :
    (actOF σ JS JT g h u).map (infPartF F E) = 0 := by
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem piWF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x := by
  have hx := finIdem_add_iota C.chart x
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.actOF_add, piWF_add, piWF_of_fin (actOF_fin g h (finIdem_smul_fin x)), zero_add,
    GlobalTheory.T.adelicHomAction_realCoordinates_eq F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart g h, piWF_iotaVF C.chart]

theorem hOF_rat (x y : Matrix (Fin nT) (Fin nS) E) :
    hOF σ JS JT (ratWF (F := F) x) (ratWF (F := F) y) = incAF F E (hRatF σ JS JT x y) := by
  simp only [hOF, hRatF, ratWF, Matrix.map_apply, cAF_inc, map_sum, map_mul]

theorem trace_inc (e : E) :
    Algebra.trace (AF F) (AEF F E) (incAF F E e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem symplOHF_rat (x y : Matrix (Fin nT) (Fin nS) E) :
    symplOHF σ JS JT ξ₀ (ratWF (F := F) x) (ratWF (F := F) y) =
      algebraMap F (AF F) (1 / 2 * Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)) := by
  rw [symplOHF, symplOF, hOF_rat, ← map_mul, trace_inc, ← map_mul]

theorem psi_rat (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 := by
  rw [symplOHF_rat]
  exact C.good.std.2.1 _

theorem rhoFF_finRatF {g : GAF σ JS} {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) : rhoFF σ JS JT (g⁻¹, h⁻¹) (finRatF F y) = finRatF F (b * y * a) := by
  apply XFF.ext
  show actOF σ JS JT g⁻¹ h⁻¹ (finIdem F E • ratWF (F := F) y) = finIdem F E • ratWF (F := F) (b * y * a)
  unfold actOF
  rw [inv_inv, ha, hb, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [ratWF, ratWF, Matrix.map_mul, Matrix.map_mul]

theorem infRatF_injective (B : Base F E) : Function.Injective (infRatF (nS := nS) (nT := nT) (tauB B)) := by
  intro x y hxy
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  funext i j
  exact (tauB B w).injective (congrFun hxy ((i, j), w))

theorem sum3 {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ b, ∑ c, ∑ d, f b c d = ∑ d, ∑ c, ∑ b, f b c d :=
  calc ∑ b, ∑ c, ∑ d, f b c d = ∑ c, ∑ b, ∑ d, f b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, f b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, f b c d := Finset.sum_comm

theorem hOF_trace (x y : WOF F E nS nT) :
    hOF σ JS JT x y = Matrix.trace (JS⁻¹.map (incAF F E) * (y.map (cAF σ))ᵀ * JT.map (incAF F E) * x) := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => sum3 _

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have hg : (((mtF σ JS g⁻¹).map (cAF σ))ᵀ * JS.map (incAF F E)) * mtF σ JS g⁻¹ = JS.map (incAF F E) := (g⁻¹).2
  have hh : (((mtF σ JT h).map (cAF σ))ᵀ * JT.map (incAF F E)) * mtF σ JT h = JT.map (incAF F E) := h.2
  rw [hOF_trace, hOF_trace]
  unfold actOF
  set G := mtF σ JS g⁻¹
  set H := mtF σ JT h
  set Si := JS⁻¹.map (incAF F E)
  set Sm := JS.map (incAF F E)
  set Tm := JT.map (incAF F E)
  have hi1 : Si * Sm = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hi2 : Sm * Si = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK' : (Si * (G.map (cAF σ))ᵀ * Sm) * G = 1 := by
    have e : Si * (G.map (cAF σ))ᵀ * Sm * G = Si * ((G.map (cAF σ))ᵀ * Sm * G) := by simp only [Matrix.mul_assoc]
    rw [e, hg, hi1]
  have hK : G * (Si * (G.map (cAF σ))ᵀ * Sm) = 1 := by
    first | exact mul_eq_one_comm.1 hK' | exact Matrix.mul_eq_one_comm.1 hK' | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hK'
  have hGJ : G * Si * (G.map (cAF σ))ᵀ = Si := by
    calc G * Si * (G.map (cAF σ))ᵀ = G * (Si * (G.map (cAF σ))ᵀ * Sm) * Si := by
          simp only [Matrix.mul_assoc, hi2, Matrix.mul_one]
      _ = Si := by rw [hK, Matrix.one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have e1 : Si * ((G.map (cAF σ))ᵀ * ((y.map (cAF σ))ᵀ * (H.map (cAF σ))ᵀ)) * Tm * (H * x * G) =
      (Si * (G.map (cAF σ))ᵀ * (y.map (cAF σ))ᵀ * ((H.map (cAF σ))ᵀ * Tm * H) * x) * G := by
    simp only [Matrix.mul_assoc]
  rw [e1, hh, Matrix.trace_mul_comm]
  have e2 : G * (Si * (G.map (cAF σ))ᵀ * (y.map (cAF σ))ᵀ * Tm * x) =
      (G * Si * (G.map (cAF σ))ᵀ) * ((y.map (cAF σ))ᵀ * Tm * x) := by
    simp only [Matrix.mul_assoc]
  rw [e2, hGJ]
  simp only [Matrix.mul_assoc]

theorem symplOF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF C.hS]

theorem symplOF_eq_add (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y := by
  rw [symplOHF, ← add_mul, ← map_add]
  norm_num

theorem gamQF_eq_one_iff (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔
      ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z := by
  have hx : ratWF (F := F) x = finIdem F E • ratWF (F := F) x + iotaVF ι (infRatF (tauB B) x) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) x); rwa [piWF_ratWF C] at this
  have hy : ratWF (F := F) y = finIdem F E • ratWF (F := F) y + iotaVF ι (infRatF (tauB B) y) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) y); rwa [piWF_ratWF C] at this
  have cross : ∀ (a : WOF F E nS nT) (b : IxF F nS nT → ℂ), a.map (infPartF F E) = 0 →
      symplOHF σ JS JT ξ₀ a (iotaVF ι b) = 0 ∧ symplOHF σ JS JT ξ₀ (iotaVF ι b) a = 0 :=
    fun a b ha => GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ a (iotaVF ι b) ha (real_iotaVF C.chart b)
  have hr := psi_rat C x y
  rw [hx, hy, GlobalTheory.RealWeilF.symplOHF_add_left, GlobalTheory.RealWeilF.symplOHF_add_right, GlobalTheory.RealWeilF.symplOHF_add_right,
    (cross _ _ (finIdem_smul_fin _)).1, (cross _ _ (finIdem_smul_fin _)).2, add_zero, zero_add,
    AddChar.map_add_eq_mul, beta_iota_right C, piWF_iotaVF C.chart] at hr
  set om := omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y)
  set P := B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y))
  have hg : gamQF σ JS JT ξ₀ B.ψ x y = P * P := by
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    rw [symplOF_eq_add, AddChar.map_add_eq_mul]
  have hP : P = Complex.exp (Real.pi * Complex.I * (om : ℂ)) := by
    calc P = P * (Complex.exp (-(Real.pi * Complex.I) * (om : ℂ)) * Complex.exp (Real.pi * Complex.I * (om : ℂ))) := by
          rw [← Complex.exp_add, show -(Real.pi * Complex.I) * (om : ℂ) + Real.pi * Complex.I * (om : ℂ) = 0 by ring,
            Complex.exp_zero, mul_one]
      _ = _ := by rw [← mul_assoc, hr, one_mul]
  rw [hg, hP, ← Complex.exp_add, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 : ℂ) * (Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    have : (om : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩

section Lin

variable {κ : Type} [Fintype κ]

theorem dot_conj (M : Matrix κ κ ℂ) (x y : κ → ℂ) : star y ⬝ᵥ (Mᴴ *ᵥ x) = star (star x ⬝ᵥ (M *ᵥ y)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem dot_mul (s H : Matrix κ κ ℂ) (x y : κ → ℂ) : star (s *ᵥ y) ⬝ᵥ (H *ᵥ x) = star y ⬝ᵥ ((sᴴ * H) *ᵥ x) := by
  first
  | rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  | (simp only [dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
     rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun _ _ => ?_
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem omV_laws [DecidableEq κ] {H s : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) :
    (∀ x y, omV H x y = -omV H y x) ∧ (∀ v, jV s (jV s v) = -v) ∧ (∀ x y, omV H x (jV s y) = omV H y (jV s x)) ∧
      ∀ v, v ≠ 0 → 0 < omV H v (jV s v) := by
  have hM : (H * s)ᴴ = H * s := hQ.1
  have hsH : sᴴ * H = H * s := by rw [← hM, Matrix.conjTranspose_mul, hH]
  have hj : ∀ x y, omV H x (jV s y) = (star y ⬝ᵥ ((H * s) *ᵥ x)).re := by
    intro x y
    rw [omV_apply, jV_apply, star_smul, smul_dotProduct, dot_mul, hsH, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_I, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    ring
  refine ⟨fun x y => ?_, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [omV_apply, omV_apply]
    have := dot_conj H x y
    rw [hH] at this
    rw [this, Complex.star_def, Complex.conj_im]
  · rw [jV_apply, jV_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul, Complex.I_mul_I,
      neg_one_smul]
  · rw [hj, hj]
    have := dot_conj (H * s) y x
    rw [hM] at this
    rw [this, Complex.star_def, Complex.conj_re]
  · rw [hj]
    have hp : 0 < star v ⬝ᵥ ((H * s) *ᵥ v) := by
      first | exact hQ.2 v hv | exact hQ.dotProduct_mulVec_pos hv | exact hQ.2 hv
    exact (Complex.pos_iff.1 hp).1

end Lin

theorem sig_sig (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])

theorem trace_places [IsTotallyReal F] (t : F) :
    algebraMap ℚ ℂ (Algebra.trace ℚ F t) = ∑ w : InfinitePlace F, w.embedding t := by
  first | rw [trace_eq_sum_embeddings (E := ℂ)] | rw [trace_eq_sum_embeddings ℂ]
  symm
  refine Fintype.sum_equiv (Equiv.ofBijective (fun w : InfinitePlace F => w.embedding.toRatAlgHom) ⟨?_, ?_⟩) _ _
    (fun w => rfl)
  · intro w w' h
    have := congrArg (fun φ : F →ₐ[ℚ] ℂ => InfinitePlace.mk (φ : F →+* ℂ)) h
    simpa [InfinitePlace.mk_embedding] using this
  · intro φ
    refine ⟨InfinitePlace.mk (φ : F →+* ℂ), ?_⟩
    have hr : ComplexEmbedding.IsReal (φ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have he : (InfinitePlace.mk (φ : F →+* ℂ)).embedding = (φ : F →+* ℂ) := by
      first
      | exact InfinitePlace.embedding_mk_eq_of_isReal hr
      | exact (InfinitePlace.embedding_mk_eq (φ : F →+* ℂ)).elim id (fun e => e.trans (ComplexEmbedding.isReal_iff.1 hr))
    ext x
    show (InfinitePlace.mk (φ : F →+* ℂ)).embedding x = φ x
    rw [he]
    rfl

theorem gamQF_eq_one_iff' (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n := by
  haveI : IsTotallyReal F := C.good.cm.1
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : gamQF σ JS JT ξ₀ B.ψ x y =
      B.ψ (pairA F 0 (algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)))) := by
    have := LatC.sympl_ft (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (sig_sig C.good) 1 1 x y
    rw [one_mul, one_mul] at this
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    exact congrArg B.ψ this
  have h2 : ∀ t : F, pairA F 0 (algebraMap F (Af F) t) = algebraMap F (AF F) t + pairA F (-(algebraMap F (Ainf F) t)) 0 := by
    intro t
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) t + -(algebraMap F (Ainf F) t)
      rw [add_neg_cancel]
    · show algebraMap F (Af F) t = algebraMap F (Af F) t + 0
      rw [add_zero]
  have h3 : ∀ t : F, B.ψ (pairA F (-(algebraMap F (Ainf F) t)) 0) =
      Complex.exp (2 * Real.pi * Complex.I * algebraMap ℚ ℂ (Algebra.trace ℚ F t)) := by
    intro t
    have hw : ∀ w, θ w ((-(algebraMap F (Ainf F) t)) ⊗ₜ[F] (1 : E)) = -(w.embedding t) := by
      intro w
      have e : (algebraMap F (Ainf F) t) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E t := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [TensorProduct.neg_tmul, map_neg, e, (C.inf w).1]
      exact congrArg Neg.neg (RingHom.congr_fun (B.emb w).2 t)
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA C.good.std, ← GlobalTheory.StdCharWeilDatum.sum_infFam B θ C.inf, trace_places]
    congr 1
    simp only [hw, Finset.sum_neg_distrib]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, C.good.std.2.1, one_mul, h3, Complex.exp_eq_one_iff, Algebra.trace_trace]
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y)) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by linear_combination hn)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h4
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, map_intCast]; ring⟩

section Span

def wE (B : Base F E) (w : InfinitePlace F) : InfinitePlace E := InfinitePlace.mk (B.emb w).1

def cw (B : Base F E) (w : InfinitePlace F) : ℂ →ₗ[ℝ] ℂ :=
  if (wE B w).embedding = (B.emb w).1 then LinearMap.id else Complex.conjAe.toLinearEquiv.toLinearMap

theorem cw_emb (B : Base F E) (w : InfinitePlace F) (e : E) : cw B w ((wE B w).embedding e) = (B.emb w).1 e := by
  unfold cw
  split_ifs with h
  · rw [h]; rfl
  · have h' := (InfinitePlace.embedding_mk_eq (B.emb w).1).resolve_left h
    show Complex.conjAe ((InfinitePlace.mk (B.emb w).1).embedding e) = (B.emb w).1 e
    rw [h']
    simp [ComplexEmbedding.conjugate_coe_eq]

theorem cw_cw (B : Base F E) (w : InfinitePlace F) (z : ℂ) : cw B w (cw B w z) = z := by
  unfold cw
  split_ifs
  · rfl
  · simp

theorem wE_comap (B : Base F E) (w : InfinitePlace F) : (wE B w).comap (algebraMap F E) = w := by
  rw [wE, InfinitePlace.comap_mk, (B.emb w).2, InfinitePlace.mk_embedding]

def Lm (B : Base F E) [IsTotallyComplex E] : mixedEmbedding.mixedSpace E →ₗ[ℝ] (InfinitePlace F → ℂ) :=
  LinearMap.pi fun w => (cw B w).comp ((LinearMap.proj (R := ℝ) (φ := fun _ : {W : InfinitePlace E // W.IsComplex} => ℂ)
    ⟨wE B w, IsTotallyComplex.isComplex _⟩).comp (LinearMap.snd ℝ _ _))

theorem span_tau (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) = ⊤ := by
  haveI : IsTotallyComplex E := hB.cm.2.1
  have hall : ∀ z ∈ Submodule.span ℝ (Set.range (mixedEmbedding E)),
      Lm B z ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨e, ?_⟩
      funext w
      show (B.emb w).1 e = cw B w ((wE B w).embedding e)
      rw [cw_emb]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have htop : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq (mixedEmbedding.latticeBasis E).span_eq.symm) (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (mixedEmbedding.latticeBasis_apply E i).symm⟩
  rw [eq_top_iff]
  rintro f -
  let z : mixedEmbedding.mixedSpace E :=
    (0, fun W => cw B (W.1.comap (algebraMap F E)) (f (W.1.comap (algebraMap F E))))
  have hz : Lm B z = f := by
    funext w
    show cw B w (cw B ((wE B w).comap (algebraMap F E)) (f ((wE B w).comap (algebraMap F E)))) = f w
    rw [wE_comap, cw_cw]
  rw [← hz]
  exact hall z (htop ▸ Submodule.mem_top)

theorem span_infRatF (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ := by
  set V := Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B)))
  have key : ∀ (q : Fin nT × Fin nS) (g : InfinitePlace F → ℂ),
      (fun p : IxF F nS nT => if p.1 = q then g p.2 else 0) ∈ V := by
    intro q g
    have hg : g ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
      rw [span_tau hB]; trivial
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨Matrix.of fun a b => if (a, b) = q then e else 0, ?_⟩
      funext p
      show (B.emb p.2).1 (if (p.1.1, p.1.2) = q then e else 0) = if p.1 = q then (B.emb p.2).1 e else 0
      by_cases h : p.1 = q
      · rw [if_pos h, if_pos (by rw [← h])]
      · rw [if_neg h, if_neg (by intro h'; exact h (by rw [← h'])), map_zero]
    | zero =>
      convert V.zero_mem using 1
      funext p
      split_ifs <;> rfl
    | add g g' _ _ hg hg' =>
      convert V.add_mem hg hg' using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
    | smul c g _ hg =>
      convert V.smul_mem c hg using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ q : Fin nT × Fin nS, (fun p : IxF F nS nT => if p.1 = q then v (q, p.2) else 0) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [hv]
  exact V.sum_mem fun q _ => key q (fun w => v (q, w))

end Span

end PositivityTheory.ThKW.TauSpanIdentities

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem beta_iota_right (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) :=
  TauSpanIdentities.beta_iota_right C x v

theorem beta_iota_left (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) = Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) :=
  TauSpanIdentities.beta_iota_left C v x

theorem piWF_iotaVF (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : piWF θ (iotaVF ι v) = v :=
  TauSpanIdentities.piWF_iotaVF hι v

theorem piWF_ratWF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y :=
  TauSpanIdentities.piWF_ratWF C y

theorem finIdem_add_iota (hι : IsChartF θ ι) (x : WOF F E nS nT) : x = finIdem F E • x + iotaVF ι (piWF θ x) :=
  TauSpanIdentities.finIdem_add_iota hι x

theorem finIdem_smul_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : finIdem F E • u = u :=
  TauSpanIdentities.finIdem_smul_of_fin hu

theorem finIdem_smul_of_real {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) : finIdem F E • u = 0 :=
  TauSpanIdentities.finIdem_smul_of_real hu

theorem continuous_piWF (C : Ctx σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  TauSpanIdentities.continuous_piWF C

theorem piWF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x :=
  TauSpanIdentities.piWF_actOF C g h x

theorem symplOF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y :=
  TauSpanIdentities.symplOF_actOF C g h x y

theorem psi_rat (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 :=
  TauSpanIdentities.psi_rat C x y

theorem rhoFF_finRatF {g : GAF σ JS} {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) : rhoFF σ JS JT (g⁻¹, h⁻¹) (finRatF F y) = finRatF F (b * y * a) :=
  TauSpanIdentities.rhoFF_finRatF ha hb y

theorem gamQF_eq_one_iff (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z :=
  TauSpanIdentities.gamQF_eq_one_iff C x y

theorem gamQF_eq_one_iff' (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n :=
  TauSpanIdentities.gamQF_eq_one_iff' C x y

theorem infRatF_injective (B : Base F E) : Function.Injective (infRatF (nS := nS) (nT := nT) (tauB B)) :=
  TauSpanIdentities.infRatF_injective B

theorem span_infRatF (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ :=
  TauSpanIdentities.span_infRatF hB

theorem omV_laws {κ : Type} [Fintype κ] [DecidableEq κ] {H s : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) :
    (∀ x y, omV H x y = -omV H y x) ∧ (∀ v, jV s (jV s v) = -v) ∧ (∀ x y, omV H x (jV s y) = omV H y (jV s x)) ∧
      ∀ v, v ≠ 0 → 0 < omV H v (jV s v) :=
  TauSpanIdentities.omV_laws hH hs hQ

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

namespace AutLatA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}

theorem one_int : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem sgsg (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

theorem finRatF_mem_of {y : Matrix (Fin nT) (Fin nS) E} (hy : y ∈ Λ) : finRatF F y ∈ latF F E nS nT Λ :=
  AddSubgroup.subset_closure ⟨1, one_int, y, hy, rfl⟩

theorem mem_iff (C : Ctx σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ :=
  ⟨fun h => (hR y).2 fun M' hM' => (gamQF_eq_one_iff' C y M').1 ((hA _).1 h _ (finRatF_mem_of hM')),
    finRatF_mem_of⟩

theorem sdQ (C : Ctx σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ) : SelfDual (gamQF σ JS JT ξ₀ B.ψ) Λ := fun x =>
  (hR x).trans (forall₂_congr fun y _ => (gamQF_eq_one_iff' C x y).symm)

theorem exists_denomM (hL : Λ.FG) : ∃ d : E, d ≠ 0 ∧ ∀ x ∈ Λ, ∀ i j, IsIntegral ℤ (d * x i j) := by
  obtain ⟨s, hs⟩ := hL
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin nT × Fin nS))).image fun p => p.1 p.2.1 p.2.2)
  refine ⟨(y : E), by exact_mod_cast hy0, fun x hx i j => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have := hy (x i j) (Finset.mem_image.2 ⟨(x, (i, j)), by simpa using hx, rfl⟩)
    simpa [zsmul_eq_mul] using this
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz =>
    have e : (y : E) * (x + z) i j = (y : E) * x i j + (y : E) * z i j := mul_add _ _ _
    rw [e]; exact hx.add hz
  | smul c x _ hx =>
    have : (y : E) * (c • x) i j = (c : E) * ((y : E) * x i j) := by
      change (y : E) * ((c : E) * x i j) = _
      ring
    rw [this]
    exact c.isIntegral_coe.mul hx

theorem norm_emb_eq (hB : B.IsGood σ) (φ : E →+* ℂ) (x : E) :
    ∃ v : InfinitePlace F, ‖φ x‖ = ‖tauB B v x‖ := by
  have hcm := hB.cm
  let ρ : F →+* ℂ := φ.comp (algebraMap F E)
  refine ⟨InfinitePlace.mk ρ, ?_⟩
  have hρ : ComplexEmbedding.IsReal ρ := by
    have := hcm.1.isReal (InfinitePlace.mk ρ)
    rwa [InfinitePlace.isReal_mk_iff] at this
  have he : (InfinitePlace.mk ρ).embedding = ρ := by
    rcases InfinitePlace.embedding_mk_eq ρ with h | h
    · exact h
    · rw [h]; exact hρ
  have hτ : (tauB B (InfinitePlace.mk ρ)).comp (algebraMap F E) = ρ := by
    exact (B.emb (InfinitePlace.mk ρ)).2.trans he
  obtain ⟨c, hc⟩ := PI.OmLocU.Red.fix_range σ hcm (y := x * σ x) (by rw [map_mul, sgsg hB, mul_comm])
  have key : ∀ τ : E →+* ℂ, τ.comp (algebraMap F E) = ρ → Complex.normSq (τ x) = ρ c := fun τ hτ => by
    rw [← hτ, RingHom.comp_apply, hc, map_mul, hcm.2.2.2 τ]
    exact (Complex.mul_conj (τ x)).symm
  have h2 := (key φ rfl).trans (key _ hτ).symm
  rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem finLat (hB : B.IsGood σ) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite := by
  obtain ⟨d, hd, hdi⟩ := exists_denomM hG.fg
  have hS := GlobalTheory.CompletedLatticeFinite.finite_of_denom d hd R
  refine (Set.Finite.pi fun _ : Fin nT => Set.Finite.pi fun _ : Fin nS => hS).subset ?_
  rintro y ⟨hy, hR⟩ i - j -
  refine ⟨hdi y hy i j, fun φ => ?_⟩
  obtain ⟨v, hv⟩ := norm_emb_eq hB φ (y i j)
  rw [hv]
  exact (norm_le_pi_norm (infRatF (tauB B) y) ((i, j), v)).trans hR

theorem nsmul_inv_smul' {M : Type} [AddCommGroup M] [Module (AEF F E) M] {N : ℕ} (hN : 0 < N) (x : M) :
    N • (incAF F E (N : E)⁻¹ • x) = x := by
  have h : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← Nat.cast_smul_eq_nsmul (AEF F E), smul_smul, ← map_natCast (incAF F E) N, ← map_mul, mul_inv_cancel₀ h, map_one,
    one_smul]

theorem level (hG : GoodLat Λ) (N : ℕ) (hN : 0 < N) : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
    ∀ u ∈ U, ∃ l ∈ latF F E nS nT Λ, finIdem F E • u = ((N • l : XFF F E nS nT) : WOF F E nS nT) := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let U : AddSubgroup (WOF F E nS nT) :=
    { carrier := {u | ∃ z ∈ latOF F E nS nT Λ, finIdem F E • u = N • z}
      add_mem' := by
        rintro a b ⟨z, hz, ea⟩ ⟨z', hz', eb⟩
        exact ⟨z + z', add_mem hz hz', by rw [smul_add, ea, eb, nsmul_add]⟩
      zero_mem' := ⟨0, zero_mem _, by rw [smul_zero, smul_zero]⟩
      neg_mem' := by
        rintro a ⟨z, hz, ea⟩
        exact ⟨-z, neg_mem hz, by rw [smul_neg, ea, smul_neg]⟩ }
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hG
  have hc : Continuous fun u : WOF F E nS nT => incAF F E (N : E)⁻¹ • finIdem F E • u :=
    (continuous_const_smul (incAF F E (N : E)⁻¹)).comp (continuous_const_smul (finIdem F E))
  have hm : (fun u : WOF F E nS nT => incAF F E (N : E)⁻¹ • finIdem F E • u) ⁻¹' V ∈ 𝓝 (0 : WOF F E nS nT) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hV
  refine ⟨U, AddSubgroup.isOpen_of_mem_nhds U (Filter.mem_of_superset hm fun u hu => ?_),
    fun u ⟨z, hz, e⟩ => ⟨XFF.mk z (lat_fin hz), hz, e⟩⟩
  exact ⟨_, hV' _ hu ((finSubF F E nS nT).smul_mem _ (finIdem_smul_fin u)), (nsmul_inv_smul' hN _).symm⟩

theorem inv_rho (g : GAF σ JS) (h : GAF σ JT) (x : XFF F E nS nT) :
    rhoFF σ JS JT (g, h) (rhoFF σ JS JT (g⁻¹, h⁻¹) x) = x ∧ rhoFF σ JS JT (g⁻¹, h⁻¹) (rhoFF σ JS JT (g, h) x) = x := by
  constructor
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

theorem mem_map_rho (A : Submodule (𝓞 E) (XFF F E nS nT)) (g : GAF σ JS) (h : GAF σ JT) (x : XFF F E nS nT) :
    x ∈ A.map (rhoFF σ JS JT (g, h)) ↔ rhoFF σ JS JT (g⁻¹, h⁻¹) x ∈ A :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← e, (inv_rho g h y).2], fun hx => ⟨_, hx, (inv_rho g h x).1⟩⟩

theorem isHeisQ (C : Ctx σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (hw : w + sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamQF σ JS JT ξ₀ B.ψ) fun x => opFF hc w (finRatF F x) := by
  have H := isHeis_opFF (sgsg C.good) C.hS C.hT C.hξ hc hw
  have e : ∀ x y, gamQF σ JS JT ξ₀ B.ψ x y = gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add, H.add_left],
    fun x y z => by rw [e, e, e, map_add, H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add]⟩

theorem idx_eq (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      Λ.toAddSubgroup.relIndex (Λ.toAddSubgroup.comap (GlobalTheory.RatAut.sandw b a).toAddMonoidHom) := by
  have hmem := mem_iff C hR hO.sd
  have hfin := hO.fin (g⁻¹, h⁻¹)
  have hmov : ∀ u ∈ latF F E nS nT Λ,
      idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u ∈
        (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := fun u hu => by
    rw [mem_map_rho, map_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem (latF F E nS nT Λ).toAddSubgroup (Submodule.mem_map_of_mem hu)
  rw [GlobalTheory.FinWeil.idx, ← GlobalTheory.RatLattice.relIndex_comap_comap (finRatF F (E := E) (nS := nS) (nT := nT)).toAddMonoidHom]
  · congr 1
    · ext x; exact hmem x
    · ext x
      show finRatF F x ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) ↔ b * x * a ∈ Λ
      rw [mem_map_rho, rhoFF_finRatF ha hb, hmem]
  · intro z hz
    have hN := Nat.pos_of_ne_zero hfin
    obtain ⟨γ, hγ⟩ := lat_approx hG _ (incAF F E ((idx (latF F E nS nT Λ)
      ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) : ℕ) : E)⁻¹ • z).fin
    obtain ⟨u, hu, e⟩ : ∃ u ∈ latF F E nS nT Λ, z = finRatF F (idx (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ) +
        idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u :=
      ⟨_, hγ, by rw [map_nsmul, ← nsmul_add, add_sub_cancel, nsmul_inv_smul' (F := F) (E := E) hN]⟩
    refine ⟨idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ, ?_, ?_⟩
    · show finRatF F _ ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hz (hmov u hu)
    · show z - finRatF F _ ∈ latF F E nS nT Λ
      rw [sub_eq_of_eq_add' e]
      exact nsmul_mem hu _

open GlobalTheory.RatAut in
theorem data (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  have sd := sdQ C hR
  obtain ⟨d, hd0, hdi⟩ := exists_denomM hG.fg
  have fg : Λ.toAddSubgroup.FG := GlobalTheory.RatLattice.fg_of_denom _ d hd0 hdi
  have full := hG.den
  rw [idx_eq C hG hR hO ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := Λ.toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    rw [← hs] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y => k (sandw b a y)) hx
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx
  have i1 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (isHeisQ C hc hO.hw) hO.good sd ((sandw b a).restrictScalars (𝓞 E))
    (fun x y => by
      show gamFF σ JS JT ξ₀ B.ψ (finRatF F (b * x * a)) (finRatF F (b * y * a)) =
        gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y)
      rw [← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb]
      unfold gamFF
      rw [coe_rhoFF, coe_rhoFF, symplOF_actOF C]) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩

end AutLatA

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem finRatF_mem_iff (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := AutLatA.mem_iff C hR hA y

theorem finite_lat (hB : B.IsGood σ) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite :=
  AutLatA.finLat hB hG R

theorem exists_level (hG : GoodLat Λ) (N : ℕ) (hN : 0 < N) : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
    ∀ u ∈ U, ∃ l ∈ latF F E nS nT Λ, finIdem F E • u = ((N • l : XFF F E nS nT) : WOF F E nS nT) :=
  AutLatA.level hG N hN

theorem finite_data (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| :=
  AutLatA.data C hG hR hO ha hb hΔ hd

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

open scoped ContDiff

namespace SerA

theorem sig_sig' (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

theorem piWF_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : piWF θ u = 0 := by
  funext p
  have h : infPartF F E (u p.1.1 p.1.2) = 0 := congrFun (congrFun hu p.1.1) p.1.2
  show θ p.2 (infPartF F E (u p.1.1 p.1.2)) = 0
  rw [h, map_zero]

theorem symplOHF_two' (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x (2 • y) = symplOF σ JS JT ξ₀ x y := by
  rw [two_nsmul, GlobalTheory.HeisLineF.symplOHF_add_right, symplOHF_add_self]

theorem phase_two' {ψ : AddChar (AF F) ℂ} (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)) (w : 𝓞 E)
    {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) : phaseF σ JS JT ξ₀ ψ w (2 • u) = 1 := by
  have h : ψ (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u) = 1 :=
    (hA _).1 ((latF F E nS nT Λ).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
    (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phaseF, h2, ← symplOHF_two']
  rfl

theorem quad (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    {w : 𝓞 E} (hw : w + sgOF σ w = 1) (y u : WOF F E nS nT) :
    -symplOHF σ JS JT ξ₀ (intAF F w • u) u +
        (symplOHF σ JS JT ξ₀ y u + symplOHF σ JS JT ξ₀ (intAF F w • (y + u)) (y + u)) =
      symplOHF σ JS JT ξ₀ (intAF F w • y) y + symplOF σ JS JT ξ₀ (intAF F w • y) u := by
  have h1 : intAF F w • y + cAF σ (intAF F w) • y = y := by
    rw [← add_smul, cAF_intAF, ← map_add, hw, map_one, one_smul]
  have h2 := congrArg (fun z => symplOHF σ JS JT ξ₀ z u) h1
  simp only [GlobalTheory.HeisLineF.symplOHF_add_left] at h2
  have h3 := symplOHF_smul σ JS JT hσ ξ₀ (intAF F w) u y
  rw [symplOHF_skew σ JS JT hσ hS hT ξ₀ hξ u (cAF σ (intAF F w) • y)] at h3
  rw [smul_add (intAF F w) y u]
  simp only [GlobalTheory.HeisLineF.symplOHF_add_left, GlobalTheory.HeisLineF.symplOHF_add_right]
  rw [← symplOHF_add_self]
  linear_combination h3 - h2

theorem chi_add_lat (C : Ctx σ B JS JT ξ₀ θ ι) (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hw : w + sgOF σ w = 1) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) (x : WOF F E nS nT) :
    phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ x u) * chiLatF σ JS JT ξ₀ B.ψ Λ w (x + u)) =
      chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  have hσ := sig_sig' C.good
  have e : finIdem F E • (x + (u : WOF F E nS nT)) = finIdem F E • x + u := by
    rw [smul_add, finIdem_smul_of_fin u.fin]
  have e2 : B.ψ (symplOHF σ JS JT ξ₀ x u) = B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • x) u) := by
    have hx := finIdem_add_iota C.chart x
    have h3 := beta_iota_left C (piWF θ x) (u : WOF F E nS nT)
    rw [piWF_fin u.fin, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h3
    conv_lhs => rw [hx]
    rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul, h3, mul_one]
  unfold chiLatF
  rw [e, e2]
  have hy := finIdem_smul_fin (F := F) (E := E) x
  generalize finIdem F E • x = y at hy ⊢
  by_cases h : y ∈ latOF F E nS nT Λ
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : B.ψ (symplOF σ JS JT ξ₀ (intAF F w • y) u) = 1 :=
      (hA _).1 ((latF F E nS nT Λ).smul_mem w (show XFF.mk y hy ∈ latF F E nS nT Λ from h)) u hu
    rw [phaseF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad hσ C.hS C.hT C.hξ hw,
      AddChar.map_add_eq_mul, h0, mul_one]
  · have h2 : y + (u : WOF F E nS nT) ∉ latOF F E nS nT Λ := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]

theorem main (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) := by
  have hσ := sig_sig' C.good
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B C.good).1
  have hA := hO.sd
  have hw := hO.hw
  obtain ⟨-, hJ, hsym, hpos⟩ := omV_laws
    (PositivityTheory.ThKW.hermitian_majorant_selfAdjoint_posDef F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ).1 hs.sq hs.pos
  have hl : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ (x + y) z) =
      B.ψ (symplOHF σ JS JT ξ₀ x z) * B.ψ (symplOHF σ JS JT ξ₀ y z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x (y + z)) =
      B.ψ (symplOHF σ JS JT ξ₀ x y) * B.ψ (symplOHF σ JS JT ξ₀ x z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ x : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x x) = 1 := fun x => by
    rw [symplOHF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WOF F E nS nT) (v : IxF F nS nT → ℂ), B.ψ (symplOHF σ JS JT ξ₀ x (iotaA ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWA θ x) v : ℝ)) :=
    fun x v => beta_iota_right C x v
  have fl : ∀ u ∈ latF F E nS nT Λ, ∀ x : WOF F E nS nT, phaseF σ JS JT ξ₀ B.ψ w u *
      (B.ψ (symplOHF σ JS JT ξ₀ x u) * serF σ JS JT ξ₀ B θ ι s Λ w a (x + u)) = serF σ JS JT ξ₀ B θ ι s Λ w a x :=
    fun u hu x => GlobalTheory.GaussSeriesVacuum.series_inv_scalar (G := WOF F E nS nT)
      (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) hl hr hd hβ a u (piWF_fin u.fin) _ (chi_add_lat C hA hw hu) x
  obtain ⟨U, hUo, hlev⟩ := exists_level (F := F) (E := E) (nS := nS) (nT := nT) hG 2 two_pos
  let U₀ : AddSubgroup (WOF F E nS nT) :=
    (latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E))
  obtain ⟨fc, fs, fv⟩ := GlobalTheory.GaussSeriesVacuum.series_regular (piWA θ) (iotaA ι)
    (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) U₀ U
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) (continuous_piWF C) (continuous_iotaVF C.chart) (piWF_iotaVF C.chart) hl hr hd
    (fun x y => hψ.2.1 _)
    (hψ.1.comp (GlobalTheory.RealWeilF.continuous_symplOHF σ JS JT ξ₀ continuous_fst continuous_snd)) hβ hJ hsym hpos
    (by
      rintro _ ⟨y, rfl⟩ h
      have e : piWF θ (ratWF (F := F) y) = 0 := h
      rw [piWF_ratWF C] at e
      have : y = 0 := infRatF_injective B (by rw [e, map_zero])
      subst this
      exact map_zero _)
    (fun R => by
      refine ((finite_lat C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      refine ⟨y, ⟨(finRatF_mem_iff C hG hR hA y).1 h1, ?_⟩, rfl⟩
      have e : piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := piWF_ratWF C y
      rw [← e]
      exact h2)
    (fun x hx => by unfold chiLatF; exact if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => by
      show chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = _
      unfold chiLatF
      rw [smul_add, finIdem_smul_of_real (real_iotaVF C.chart v), add_zero])
    hUo
    (fun u hu x => by
      obtain ⟨l, hl', e⟩ := hlev u hu
      have e3 : u - iotaA ι (piWA θ u) = ((2 • l : XFF F E nS nT) : WOF F E nS nT) :=
        (sub_eq_of_eq_add (finIdem_add_iota C.chart u)).trans e
      rw [e3]
      have e2 := chi_add_lat C hA hw (nsmul_mem hl' 2) x
      rw [phase_two' hA w hl', one_mul] at e2
      exact e2) a
  have hquasi : ∀ (γ : Matrix (Fin nT) (Fin nS) E) (x : WOF F E nS nT),
      serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x)) * serF σ JS JT ξ₀ B θ ι s Λ w a x := by
    intro γ x
    have e : B.ψ (symplOHF σ JS JT ξ₀ (ratWF γ) x) * serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        serF σ JS JT ξ₀ B θ ι s Λ w a x :=
      GlobalTheory.HeisenbergGaussianSeries.series_quasi (G := WOF F E nS nT) (p := piWA θ) (ι := iotaA ι)
        (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (om := omV (HMF JS JT ξ₀ (tauB B))) (J := jV s)
        (Γ := ratLF F E nS nT) (χ := chiLatF σ JS JT ξ₀ B.ψ Λ w) hl hr
        (by rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩; exact psi_rat C y y') a (ratWF γ) ⟨γ, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hlevel : ∀ u ∈ U, u.map (infPartF F E) = 0 →
      heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w a) = serF σ JS JT ξ₀ B θ ι s Λ w a := by
    intro u hu h
    obtain ⟨l, hl', e⟩ := hlev u hu
    rw [finIdem_smul_of_fin h] at e
    subst e
    funext x
    have e2 := fl _ (nsmul_mem hl' 2) x
    rw [phase_two' hA w hl', one_mul] at e2
    exact e2
  have hsm : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
      ∀ x, ContDiff ℝ ∞ fun t => serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t) := by
    intro k L hL hL0 x
    let c : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) := (piWA θ).comp L
    have hc : Continuous c := (continuous_piWF C).comp hL
    have hLc : ∀ t, L t = iotaA ι (c t) := fun t => by
      have := finIdem_add_iota C.chart (L t)
      rw [finIdem_smul_of_real (hL0 t), zero_add] at this
      exact this
    have h := (fs x).comp (c.toRealLinearMap hc).contDiff
    refine (congrArg (ContDiff ℝ ∞) (funext fun t => ?_)).mp h
    show _ = serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t)
    rw [hLc t]
    rfl
  refine ⟨⟨hquasi, ⟨U, hUo, hlevel⟩, fc, hsm⟩, fun u hu => Subtype.ext (funext fun x => ?_), fun x z => fv x z⟩
  rw [coe_opFF]
  exact fl u hu x

end SerA

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem ser_vacuum (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) :=
  SerA.main C hG hR hO hs a

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.Trc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem sgsg (C : Ctx σ B JS JT ξ₀ θ ι) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [C.good.cm.2.2.2 τ, C.good.cm.2.2.2 τ, star_star]

theorem piWF_add (x y : WOF F E nS nT) : piWF θ (x + y) = piWF θ x + piWF θ y := (piWA θ).map_add x y

theorem piWF_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : piWF θ u = 0 := by
  funext p
  show θ p.2 (infPartF F E (u p.1.1 p.1.2)) = 0
  rw [show infPartF F E (u p.1.1 p.1.2) = 0 from congrFun (congrFun hu p.1.1) p.1.2, map_zero]

theorem coe_finRatF (y : Matrix (Fin nT) (Fin nS) E) :
    (finRatF F y : WOF F E nS nT) = finIdem F E • ratWF (F := F) y := rfl

theorem iota_fin (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) : (iotaVF ι v).map (finPartF F E) = 0 := by
  funext i j
  exact C.chart.fin _

theorem symplOHF_act (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [symplOF_actOF C]

theorem actOF_zero' (g : GAF σ JS) (h : GAF σ JT) : actOF σ JS JT g h (0 : WOF F E nS nT) = 0 := by
  unfold actOF
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem symplOHF_zero_left' (y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ 0 y = 0 := by
  have h := GlobalTheory.HeisLineF.symplOHF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y
  rw [add_zero] at h
  linear_combination -h

theorem ratWF_eq (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    ratWF (F := F) y = iotaVF ι (infRatF (tauB B) y) + (finRatF F y : WOF F E nS nT) := by
  rw [add_comm, ← piWF_ratWF C y]
  exact finIdem_add_iota C.chart _

theorem beta_fin (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (finRatF F y)) *
      Complex.exp (-(Real.pi * Complex.I) *
        (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) : ℝ)) = 1 := by
  have h1 := psi_rat C x y
  have h2 := beta_iota_left C (infRatF (tauB B) x) (ratWF (F := F) y)
  have h3 := beta_iota_right C (finRatF F x : WOF F E nS nT) (infRatF (tauB B) y)
  rw [piWF_of_fin (finRatF F x).fin, LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at h3
  have d1 : symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y) =
      symplOHF σ JS JT ξ₀ (iotaVF ι (infRatF (tauB B) x)) (ratWF y) +
        symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (ratWF y) := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_left, ← ratWF_eq C]
  have d2 : symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (ratWF y) =
      symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (iotaVF ι (infRatF (tauB B) y)) +
        symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (finRatF F y) := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_right, ← ratWF_eq C]
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2, h3, one_mul, mul_comm, piWF_ratWF C] at h1
  exact h1

theorem chiLat_add_iota (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  unfold chiLatF
  rw [smul_add, finIdem_smul_of_real (iota_fin C v), add_zero]

theorem ratWF_injective (C : Ctx σ B JS JT ξ₀ θ ι) :
    Function.Injective (ratWF (F := F) : Matrix (Fin nT) (Fin nS) E → WOF F E nS nT) := fun x y h =>
  infRatF_injective B (by rw [← piWF_ratWF C, ← piWF_ratWF C, h])

def ratEquivF (C : Ctx σ B JS JT ξ₀ θ ι) : Matrix (Fin nT) (Fin nS) E ≃ ratLF F E nS nT :=
  Equiv.ofBijective (fun y => ⟨ratWF y, y, rfl⟩)
    ⟨fun _ _ h => ratWF_injective C (congrArg Subtype.val h), by rintro ⟨_, y, rfl⟩; exact ⟨y, rfl⟩⟩

theorem coe_ratEquivF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    (ratEquivF C y : WOF F E nS nT) = ratWF y := rfl

theorem piWA_apply (x : WOF F E nS nT) : piWA θ x = piWF θ x := rfl

theorem iotaA_apply (v : IxF F nS nT → ℂ) : iotaA (nS := nS) (nT := nT) ι v = iotaVF ι v := rfl

theorem serF_eq (C : Ctx σ B JS JT ξ₀ θ ι) (a : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    serF σ JS JT ξ₀ B θ ι s Λ w a x = ∑' y : Matrix (Fin nT) (Fin nS) E,
      B.ψ (symplOHF σ JS JT ξ₀ (ratWF y) x) * B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι a) (ratWF y + x)) *
        chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + x) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y + (a + piWF θ x))
          (jV s (infRatF (tauB B) y + (a + piWF θ x))) : ℝ)) := by
  unfold serF GlobalTheory.HeisenbergGaussianSeries.series
  rw [← (ratEquivF C).tsum_eq]
  simp only [coe_ratEquivF, piWA_apply, iotaA_apply, piWF_ratWF C]

section Act

variable {g : GAF σ JS} {h : GAF σ JT} {a : Matrix (Fin nS) (Fin nS) E} {b : Matrix (Fin nT) (Fin nT) E}

theorem act_eq (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (x : WOF F E nS nT) :
    actOF σ JS JT g⁻¹ h⁻¹ x = b.map (incAF F E) * x * a.map (incAF F E) := by
  have ha' : mtF σ JS g = a.map (incAF F E) := ha
  have hb' : mtF σ JT h⁻¹ = b.map (incAF F E) := hb
  unfold actOF
  rw [inv_inv, ha', hb']

theorem act_ratW (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (y : Matrix (Fin nT) (Fin nS) E) :
    actOF σ JS JT g⁻¹ h⁻¹ (ratWF (F := F) y) = ratWF (b * y * a) := by
  rw [act_eq ha hb, ratWF, ratWF, Matrix.map_mul, Matrix.map_mul]

theorem act_finRat (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (y : Matrix (Fin nT) (Fin nS) E) :
    actOF σ JS JT g⁻¹ h⁻¹ (finRatF F y : WOF F E nS nT) = finRatF F (b * y * a) := by
  rw [coe_finRatF, coe_finRatF, actOF_smul, act_ratW ha hb]

theorem act_iota (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) :
    actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) := by
  have e := finIdem_add_iota C.chart (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
  rw [← actOF_smul, finIdem_smul_of_real (iota_fin C v), actOF_zero', zero_add, piWF_actOF C,
    piWF_iotaVF C.chart] at e
  exact e

theorem omV_act (C : Ctx σ B JS JT ξ₀ θ ι) (u v : IxF F nS nT → ℂ) :
    omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) =
      omV (HMF JS JT ξ₀ (tauB B)) u v := by
  have key : ∀ t : ℝ, Complex.exp (-(Real.pi * Complex.I) *
      (omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (t • u)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (t • u) v : ℝ)) := by
    intro t
    have h1 := beta_iota_left C (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (t • u)) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
    have h2 := beta_iota_left C (t • u) (iotaVF ι v)
    rw [piWF_actOF C, piWF_iotaVF C.chart, ← act_iota C, symplOHF_act C] at h1
    rw [piWF_iotaVF C.chart] at h2
    exact h1.symm.trans h2
  by_contra hne
  have hd : omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) -
      omV (HMF JS JT ξ₀ (tauB B)) u v ≠ 0 := sub_ne_zero.2 hne
  have k := key (omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) -
      omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹
  rw [mulVec_smul, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at k
  have k2 := Complex.exp_sub (-(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ) : ℂ))
    (-(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) u v : ℝ) : ℂ))
  rw [k, div_self (Complex.exp_ne_zero _)] at k2
  have e : -(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ) : ℂ) -
      -(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) u v : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
    rw [← mul_sub, ← Complex.ofReal_sub, ← mul_sub, inv_mul_cancel₀ hd, Complex.ofReal_one, mul_one]
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I] at k2
  norm_num at k2

theorem actR_add_infRat (C : Ctx σ B JS JT ξ₀ θ ι) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) (v : IxF F nS nT → ℂ) :
    mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (infRatF (tauB B) y + v) =
      infRatF (tauB B) (b * y * a) + mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v := by
  rw [mulVec_add, ← piWF_ratWF C y, ← piWF_ratWF C (b * y * a), ← act_ratW ha hb, piWF_actOF C]

end Act

theorem phase_identity (C : Ctx σ B JS JT ξ₀ θ ι) {W : AEF F E} (hW : W + cAF σ W = 1) (U Y : WOF F E nS nT)
    (hi : symplOHF σ JS JT ξ₀ (W • (U + Y)) (U + Y) = symplOHF σ JS JT ξ₀ (W • Y) Y) :
    symplOHF σ JS JT ξ₀ (W • U) U + symplOHF σ JS JT ξ₀ (U + Y) Y = symplOF σ JS JT ξ₀ (cAF σ W • U) Y := by
  have hσ := sgsg C
  have h1 : symplOHF σ JS JT ξ₀ Y Y = 0 := by
    unfold symplOHF; rw [GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero]
  have h2 : symplOHF σ JS JT ξ₀ U Y = symplOHF σ JS JT ξ₀ (W • U) Y + symplOHF σ JS JT ξ₀ (cAF σ W • U) Y := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_left, ← add_smul, hW, one_smul]
  have h3 : symplOHF σ JS JT ξ₀ (W • Y) U = -symplOHF σ JS JT ξ₀ (cAF σ W • U) Y := by
    rw [symplOHF_smul σ JS JT hσ, symplOHF_skew σ JS JT hσ C.hS C.hT ξ₀ C.hξ]
  rw [smul_add, GlobalTheory.HeisLineF.symplOHF_add_left, GlobalTheory.HeisLineF.symplOHF_add_right,
    GlobalTheory.HeisLineF.symplOHF_add_right] at hi
  rw [GlobalTheory.HeisLineF.symplOHF_add_left, ← symplOHF_add_self]
  linear_combination hi + h1 + h2 - h3

theorem gam_periodic {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {s : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (H : IsHeis s w γ W) {A : Submodule R X}
    (hA : SelfDual γ A) (φ : X →ₗ[R] X) (hφ : ∀ x y, γ (φ x) (φ y) = γ x y) (r : R) {y c : X} (hy : φ y - y ∈ A)
    (hc : c ∈ A) (hc' : φ c ∈ A) : γ (r • (φ (y + c) - (y + c))) (y + c) = γ (r • (φ y - y)) y := by
  have e1 : φ (y + c) - (y + c) = (φ y - y) + (φ c - c) := by rw [map_add]; abel
  have e2 : γ (r • c) y = γ (r • φ c) y := by
    rw [← hφ, map_smul, ← sub_add_cancel (φ y) y, H.add_right, H.iso hA (A.smul_mem r hc') hy, one_mul]
  have e3 : γ (r • (φ c - c)) y = 1 := by
    rw [smul_sub, sub_eq_add_neg, H.add_left, H.neg_left, e2, mul_inv_cancel₀ (H.ne_zero _ _)]
  rw [H.add_right, H.iso hA (A.smul_mem r (e1 ▸ A.add_mem hy (A.sub_mem hc' hc))) hc, mul_one, e1, smul_add,
    H.add_left, e3, mul_one]

variable (σ JS JT ξ₀) in

def gaussQF (ψ : AddChar (AF F) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (a : Matrix (Fin nS) (Fin nS) E) (b : Matrix (Fin nT) (Fin nT) E) (y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  if b * y * a - y ∈ Λ then gamQF σ JS JT ξ₀ ψ (sgOF σ w • (b * y * a - y)) y else 0

section Left

variable {g : GAF σ JS} {h : GAF σ JT} {a : Matrix (Fin nS) (Fin nS) E} {b : Matrix (Fin nT) (Fin nT) E}

theorem chiLat_mul_exp (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hw : w + sgOF σ w = 1) (y : Matrix (Fin nT) (Fin nS) E) :
    chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF (b * y * a - y)) = gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
      Complex.exp (-(Real.pi * Complex.I) *
        (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) (b * y * a)) (infRatF (tauB B) y) : ℝ)) := by
  have hm : ∀ z, finIdem F E • ratWF (F := F) z ∈ latOF F E nS nT Λ ↔ z ∈ Λ := fun z =>
    finRatF_mem_iff C hG hR hA z
  unfold chiLatF gaussQF
  by_cases hy : b * y * a - y ∈ Λ
  · rw [if_pos ((hm _).2 hy), if_pos hy]
    show B.ψ (symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F (b * y * a - y) : WOF F E nS nT))
      (finRatF F (b * y * a - y))) = _
    have e : (finRatF F (b * y * a - y) : WOF F E nS nT) + finRatF F y = finRatF F (b * y * a) := by
      rw [← XFF.coe_add, ← map_add, sub_add_cancel]
    have h1 := phase_identity C (W := intAF F w) (by rw [cAF_intAF, ← map_add, hw, map_one])
      (finRatF F (b * y * a - y) : WOF F E nS nT) (finRatF F y)
      (by rw [e, ← act_finRat ha hb, ← actOF_smul, symplOHF_act C])
    have h2 : gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y =
        B.ψ (symplOF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y)) := by
      rw [gamQF, gamFF, map_smul, cAF_intAF]
      rfl
    rw [h2, ← h1, e, AddChar.map_add_eq_mul, mul_assoc, beta_fin C, mul_one]
  · rw [if_neg (fun h => hy ((hm _).1 h)), if_neg hy, zero_mul]

theorem left_side (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hw : w + sgOF σ w = 1) (halt : ∀ x y, omV (HMF JS JT ξ₀ (tauB B)) x y = -omV (HMF JS JT ξ₀ (tauB B)) y x)
    (hbij : Function.Bijective fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) (v : IxF F nS nT → ℂ) :
    serF σ JS JT ξ₀ B θ ι s Λ w (-v) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v)) =
      ∑' y, gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
        gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) (infRatF (tauB B) y + v) := by
  rw [act_iota C, serF_eq C, ← (Equiv.ofBijective _ hbij).tsum_eq]
  refine tsum_congr fun y => ?_
  have h0 := omV_act (g := g) (h := h) C (infRatF (tauB B) y) v
  have h1 := actR_add_infRat C ha hb y 0
  rw [mulVec_zero, add_zero, add_zero] at h1
  rw [h1] at h0
  rw [Equiv.ofBijective_apply, chiLat_add_iota C, chiLat_mul_exp C hG hR hA ha hb hw, beta_iota_right C,
    beta_iota_left C, gaussV, actR_add_infRat C ha hb, piWF_add, piWF_iotaVF C.chart, piWF_ratWF C, map_sub (infRatF (tauB B))]
  generalize mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v = u at h0 ⊢
  generalize infRatF (tauB B) (b * y * a) = z at h0 ⊢
  generalize infRatF (tauB B) y = x at h0 ⊢
  have e1 : z - x + (-v + u) = z + u - (x + v) := by abel
  have e2 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z - x) u : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (z - x + u) : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) z x : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z + u) (x + v) : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 3
    simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply]
    linarith [halt x u, halt v z, halt v x, halt v u]
  rw [e1, ← e2]
  ring

end Left

def coefQF (σ : E →ₐ[F] E) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (B : Base F E)
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E) (u : XFF F E nS nT)
    (y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ (ratWF y) u) *
    chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + (u : WOF F E nS nT)) *
    Complex.exp (-(Real.pi / 2 : ℂ) *
      (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y) (jV s (infRatF (tauB B) y)) : ℝ)))

theorem right_side (C : Ctx σ B JS JT ξ₀ θ ι)
    (halt : ∀ x y, omV (HMF JS JT ξ₀ (tauB B)) x y = -omV (HMF JS JT ξ₀ (tauB B)) y x)
    (u : XFF F E nS nT) (v : IxF F nS nT → ℂ) :
    (phaseF σ JS JT ξ₀ B.ψ w u • heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w (-v))) (iotaVF ι v) =
      ∑' y, coefQF σ JS JT ξ₀ B s Λ w u y *
        Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
  have hu : piWF θ (u : WOF F E nS nT) = 0 := piWF_of_fin u.fin
  rw [Pi.smul_apply, smul_eq_mul, heisOF, beta_iota_left C, hu, LinearMap.map_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, serF_eq C, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have e1 : ratWF (F := F) y + (iotaVF ι v + (u : WOF F E nS nT)) = (ratWF y + (u : WOF F E nS nT)) + iotaVF ι v := by
    abel
  have e2 : omV (HMF JS JT ξ₀ (tauB B)) v v = 0 := by linarith [halt v v]
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y) v : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (infRatF (tauB B) y + v) : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_add, map_neg, LinearMap.neg_apply, e2, halt v (infRatF (tauB B) y)]
    push_cast
    ring
  rw [coefQF, GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul, beta_iota_right C, beta_iota_left C,
    piWF_add, piWF_add, hu, piWF_iotaVF C.chart, piWF_ratWF C, add_zero, neg_add_cancel, add_zero, e1,
    chiLat_add_iota C, ← e3]
  ring

theorem summable_coefQF (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hpos : ∀ v, v ≠ 0 → 0 < omV (HMF JS JT ξ₀ (tauB B)) v (jV s v)) (w : 𝓞 E) (u : XFF F E nS nT) :
    Summable fun y => ‖coefQF σ JS JT ξ₀ B s Λ w u y‖ := by
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B C.good).1
  have h := GlobalTheory.HeisenbergGaussianSeries.summable_coeff (G := WOF F E nS nT) (piWA θ)
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT)
    ((latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E)))
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) hpos
    (by
      rintro _ ⟨y, rfl⟩ hy
      have : y = 0 := infRatF_injective B (((piWF_ratWF C y).symm.trans hy).trans (map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((finite_lat C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      exact ⟨y, ⟨(finRatF_mem_iff C hG hR hA y).1 h1, by rw [← piWF_ratWF C]; exact h2⟩, rfl⟩)
    (fun x hx => if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · simp)
    (fun y => B.ψ (symplOHF σ JS JT ξ₀ y u)) (fun y => hψ.2.1 _) u 0 0 0
  rw [← (ratEquivF C).summable_iff] at h
  refine h.congr fun y => ?_
  have e : ‖phaseF σ JS JT ξ₀ B.ψ w u‖ = 1 := hψ.2.1 _
  simp only [Function.comp_apply, coe_ratEquivF, piWA_apply, piWF_ratWF C, add_zero, zero_mul, Real.exp_zero,
    mul_one]
  rw [coefQF, norm_mul (phaseF σ JS JT ξ₀ B.ψ w u), e, one_mul]

theorem mem_of_coefQF_ne_zero {w : 𝓞 E} {u : XFF F E nS nT} {y : Matrix (Fin nT) (Fin nS) E}
    (h : coefQF σ JS JT ξ₀ B s Λ w u y ≠ 0) : finRatF F y + u ∈ latF F E nS nT Λ := by
  by_contra hn
  apply h
  have e : chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + (u : WOF F E nS nT)) = 0 := by
    unfold chiLatF
    rw [smul_add, finIdem_smul_of_fin u.fin]
    exact if_neg hn
  rw [coefQF, e, mul_zero, zero_mul, mul_zero]

theorem coefQF_zero (w : 𝓞 E) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) :
    coefQF σ JS JT ξ₀ B s Λ w u 0 = 1 := by
  have e : ratWF (F := F) (0 : Matrix (Fin nT) (Fin nS) E) = 0 := Matrix.map_zero _ (incAF F E).map_zero
  rw [coefQF, e, zero_add, map_zero, symplOHF_zero_left', AddChar.map_zero_eq_one, one_mul, map_zero,
    LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, chiLatF,
    finIdem_smul_of_fin u.fin, if_pos (mem_latF.1 hu), phaseF, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one]

def sandF (b : Matrix (Fin nT) (Fin nT) E) (a : Matrix (Fin nS) (Fin nS) E) :
    Matrix (Fin nT) (Fin nS) E →+ Matrix (Fin nT) (Fin nS) E :=
  AddMonoidHom.mk' (fun x => b * x * a) (fun x y => by rw [Matrix.mul_add, Matrix.add_mul])

theorem gauss_mul_integral_A (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ := by
  have hσ := sgsg C
  obtain ⟨hH, -⟩ := PositivityTheory.ThKW.hermitian_majorant_selfAdjoint_posDef F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  obtain ⟨halt, -, -, hpos⟩ := omV_laws (H := HMF JS JT ξ₀ (tauB B)) hH hs.sq hs.pos
  have hw := hO.hw
  have H := isHeis_opFF hσ C.hS C.hT C.hξ hc hw
  have hA := hO.sd
  have hB := hO.sd' (g, h)
  have hmem : ∀ y, finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := finRatF_mem_iff C hG hR hA
  obtain ⟨m, u, huB, huT⟩ := exists_transversal_of_idx_ne_zero _ _ (hO.fin (g, h))
  let Cg : AddSubgroup (Matrix (Fin nT) (Fin nS) E) :=
    Λ.toAddSubgroup ⊓ Λ.toAddSubgroup.comap (sandF b a)
  have hC : ∀ x, x ∈ Cg ↔ x ∈ Λ ∧ b * x * a ∈ Λ := fun x => Iff.rfl
  have hQ : ∀ y, b * y * a - y ∈ Λ →
      gaussQF σ JS JT ξ₀ B.ψ Λ w a b y = gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y := fun y hy => if_pos hy
  have hQ0 : ∀ y, b * y * a - y ∉ Λ → gaussQF σ JS JT ξ₀ B.ψ Λ w a b y = 0 := fun y hy => if_neg hy
  have h0 : κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) 0 = κ := by
    obtain ⟨i, hi, hi'⟩ := huT 0 (zero_mem _)
    rw [Finset.sum_eq_single i, coefQF_zero w (by simpa using hi), mul_one]
    · intro j _ hj
      by_contra hn
      exact hj (hi' j (by simpa using mem_of_coefQF_ne_zero hn))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  have key := GlobalTheory.T.unfold_poincareSeries_lattice_fourier (IxF F nS nT → ℂ) volume _ (infRatF (tauB B)) (infRatF_injective B) Cg
    (fun R => (finite_lat C.good hG R).subset fun c hc => ⟨((hC c).1 hc.1).1, hc.2⟩) ?_ n t
    (gaussQF σ JS JT ξ₀ B.ψ Λ w a b) ?_ ?_ ?_ _ hF
    (fun y => κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) y)
    (fun y => -omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨r, hr, e⟩ := key
    refine ⟨r, hr, ?_⟩
    rw [h0, Finset.sum_congr rfl fun k _ => hQ _ (ht k)] at e
    exact e
  · rw [eq_top_iff, ← span_infRatF C.good, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨N, hN, h1⟩ := hG.den y
    obtain ⟨M, hM, h2⟩ := hG.den (b * y * a)
    have h3 : (M * N) • y ∈ Cg := by
      refine (hC _).2 ⟨?_, ?_⟩
      · rw [mul_smul]
        exact Submodule.smul_of_tower_mem Λ M h1
      · have e : b * ((M * N) • y) * a = (N * M) • (b * y * a) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, mul_comm]
        rw [e, mul_smul]
        exact Submodule.smul_of_tower_mem Λ N h2
    have h4 : infRatF (tauB B) y = ((M * N : ℕ) : ℝ)⁻¹ • infRatF (tauB B) ((M * N) • y) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 (Nat.mul_pos hM hN).ne')]
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3, rfl⟩)
  · intro y hy
    have h1 : b * y * a - y ∈ Λ := by_contra fun hn => hy (hQ0 y hn)
    obtain ⟨k, hk, -⟩ := hu y h1
    refine ⟨k, (hC _).2 ⟨hk, ?_⟩⟩
    have e : b * (y - t k) * a = (b * y * a - y) - (b * t k * a - t k) + (y - t k) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]
    exact add_mem (sub_mem h1 (ht k)) hk
  · intro k k' hk
    exact ((hu (t k) (ht k)).unique (by rw [sub_self]; exact zero_mem _) ((hC _).1 hk).1)
  · intro y c hc
    obtain ⟨hc1, hc2⟩ := (hC c).1 hc
    have e : b * (y + c) * a - (y + c) = (b * y * a - y) + (b * c * a - c) := by
      rw [Matrix.mul_add, Matrix.add_mul]; abel
    have hc' : b * c * a - c ∈ Λ := sub_mem hc2 hc1
    by_cases hy : b * y * a - y ∈ Λ
    · rw [hQ _ hy, hQ _ (e ▸ add_mem hy hc'), gamQF, gamQF, map_smul, map_smul, map_sub, map_sub,
        ← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb, map_add (finRatF F)]
      refine gam_periodic H hA _ (fun x y => ?_) _ ?_ ((hmem c).2 hc1) ?_
      · unfold gamFF
        rw [coe_rhoFF, coe_rhoFF, symplOF_actOF C]
      · rw [rhoFF_finRatF ha hb, ← map_sub]; exact (hmem _).2 hy
      · rw [rhoFF_finRatF ha hb]; exact (hmem _).2 hc2
    · rw [hQ0 _ hy, hQ0]
      intro hn
      rw [e] at hn
      exact hy ((add_mem_cancel_right hc').1 hn)
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
      ((summable_sum fun i (_ : i ∈ Finset.univ) => summable_coefQF C hG hR hA hpos w (u i)).mul_left ‖κ‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  · simp
  · intro y hy hn
    have h1 : infRatF (tauB B) y ≠ 0 := fun h => hy (infRatF_injective B (h.trans (map_zero _).symm))
    have h2 := hpos _ h1
    rw [neg_eq_zero.1 hn] at h2
    exact lt_irrefl _ h2
  · intro y hy c hc
    obtain ⟨hc1, hc2⟩ := (hC c).1 hc
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
    have h1 : finRatF F c ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := by
      refine ⟨finRatF F (b * c * a), (hmem _).2 hc2, ?_⟩
      rw [← rhoFF_finRatF ha hb, ← Module.End.mul_apply, ← map_mul,
        show ((g, h) : GAF σ JS × GAF σ JT) * (g⁻¹, h⁻¹) = 1 from mul_inv_cancel (g, h), map_one,
        Module.End.one_apply]
    have h2 := H.iso hA (mem_of_coefQF_ne_zero hi) ((hmem c).2 hc1)
    rw [H.add_left, H.iso hB (huB i) h1, mul_one] at h2
    obtain ⟨z, hz⟩ := (gamQF_eq_one_iff C y c).1 h2
    exact ⟨-z, by rw [LinearMap.neg_apply, hz, Int.cast_neg]⟩
  · intro v
    obtain ⟨hf, hfix, hvac⟩ := ser_vacuum C hG hR hO hs (-v)
    have e := hκ ⟨_, hf⟩ hfix hvac (iotaVF ι v)
    rw [(sumOp_eq_sum_transversal H _ _ hB _ hfix _ u huB huT).1, Submodule.coe_sum, Finset.sum_apply] at e
    simp only [coe_opFF, right_side C halt, left_side C hG hR hA ha hb hw halt hbij] at e
    rw [e, ← Summable.tsum_finsetSum, ← tsum_mul_left]
    · refine tsum_congr fun y => ?_
      beta_reduce
      rw [← Finset.sum_mul, mul_assoc κ]
    · intro i _
      refine Summable.of_norm ((summable_coefQF C hG hR hA hpos w (u i)).congr fun y => ?_)
      have e1 : (2 * Real.pi * Complex.I *
          ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) =
          ((2 * Real.pi * (-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, mul_one]

end PositivityTheory.ThKW.Trc

end
end
