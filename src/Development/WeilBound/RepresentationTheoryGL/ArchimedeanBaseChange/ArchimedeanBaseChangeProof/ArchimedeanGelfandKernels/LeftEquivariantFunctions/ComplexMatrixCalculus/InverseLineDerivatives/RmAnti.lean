import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.AtTraceT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.DeterminantRankOneUpdate.DetOneAddSingle

section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  show IsOpen {g : Mat n | g.det ≠ 0}
  exact isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rm_diff (lam : Fin n → ℤ) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (Rm lam) x :=
  ((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)

theorem hasDerivAt_line {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Mat n → W} {x : Mat n}
    (hf : DifferentiableAt ℝ f x) (X : Mat n) :
    HasDerivAt (fun t : ℝ => f (x * (1 + t • X))) (fderiv ℝ f x (x * X)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => x * (1 + t • X)) (x * X) 0 := by
    have e : (fun t : ℝ => x * (1 + t • X)) = fun t => x + t • (x * X) := by
      funext t
      rw [mul_add, mul_one, Matrix.mul_smul]
    rw [e]
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (x * X)).const_add x
    rw [one_smul] at this
    exact this
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)

def entL {J : Type} [Fintype J] [DecidableEq J] (P N : Matrix J J ℂ) (i j : J) : Matrix J J ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (P * M * N) i j
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r M => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem entL_apply {J : Type} [Fintype J] [DecidableEq J] (P N M : Matrix J J ℂ) (i j : J) :
    entL P N i j M = (P * M * N) i j := rfl

theorem eventually_det (X : Mat n) : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X).det := by
  have hc : Continuous (fun t : ℝ => (1 + t • X).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0 : ℝ) • X).det ≠ 0 := by simp
  exact (hc.continuousAt.eventually_ne h0).mono fun t ht => isUnit_iff_ne_zero.mpr ht

theorem hasDerivAt_rm_one (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam (1 + t • X)) (∑ a, ∑ b, X a b • At lam a b) 0 := by
  have h := hasDerivAt_line (rm_diff lam (x := 1) (by show (1 : Mat n).det ≠ 0; simp)) X
  simp only [one_mul] at h
  convert h using 1
  all_goals first
    | rfl
    | exact (hD n lam hlam X).symm
    | (congr 1; exact (hD n lam hlam X).symm)

theorem rd_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam y * N) i j) x = (Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hf : DifferentiableAt ℝ (fun y => (Rm lam y * N) i j) x := by
    have := ((entL 1 N i j).differentiableAt).comp x (rm_diff lam hx)
    simp only [Function.comp_def, entL_apply, one_mul] at this
    exact this
  have h1 := hasDerivAt_line hf X
  have h2 : HasDerivAt (fun t : ℝ => (Rm lam x * Rm lam (1 + t • X) * N) i j)
      ((Rm lam x * (∑ a, ∑ b, X a b • At lam a b) * N) i j) 0 := by
    have := (entL (Rm lam x) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_one lam hD hlam X)
    simp only [Function.comp_def, entL_apply] at this
    exact this
  have h3 : (fun t : ℝ => (Rm lam (x * (1 + t • X)) * N) i j) =ᶠ[nhds 0]
      fun t => (Rm lam x * Rm lam (1 + t • X) * N) i j := by
    filter_upwards [eventually_det X] with t ht
    rw [Cxc.rm_mul lam x _ hxu ht]
  show fderiv ℝ (fun y => (Rm lam y * N) i j) x (x * X) = _
  exact h1.unique (h3.hasDerivAt_iff.mpr h2)

theorem sum_single {lam : Fin n → ℤ} (X : Mat n) (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (Matrix.single a b z : Mat n) c d • A c d = z • A a b := by
  simp [Matrix.single_apply, ite_and, ite_smul]

theorem eu_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam y * N) i j) x = if s then (Rm lam x * At lam a b * N) i j else 0 := by
  have e1 := rd_hol lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_hol lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single (0 : Mat n) a b (1 : ℂ) (At lam)] at e1
  rw [sum_single (0 : Mat n) a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e1, e2]
  cases s <;> simp [Matrix.mul_smul, Matrix.smul_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g : Mat n → V} {x : Mat n}
    (h : f =ᶠ[nhds x] g) (s : Bool) (a b : Fin n) : Eu s a b f x = Eu s a b g x := by
  have e : ∀ Y : Mat n, Rd Y f x = Rd Y g x := fun Y => by
    simp only [Rd, h.fderiv_eq]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, e]

theorem epow_hol (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow true m a b (fun y => (Rm lam y * M) i j))
      (fun y => (Rm lam y * (At lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y hy
    rw [Epow.eq_1]
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  | succ m ih =>
    intro a b y hy
    rw [show m + 1 = m.succ from rfl, Epow.eq_2]
    simp only [Finset.sum_apply]
    have key : ∀ c, Eu true a c (Epow true m c b (fun y => (Rm lam y * M) i j)) y
        = (Rm lam y * At lam a c * ((At lam ^ m) c b * M)) i j := fun c => by
      rw [eu_congr (g := fun z => (Rm lam z * ((At lam ^ m) c b * M)) i j) ?_ true a c]
      · rw [eu_hol lam hD hlam ((At lam ^ m) c b * M) i j hy true a c]
        exact if_pos rfl
      · filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        exact (ih c b hz).trans (congrFun (congrFun (Matrix.mul_assoc _ _ _) i) j)
    simp only [key]
    rw [pow_succ', Matrix.mul_apply (M := At lam) (N := At lam ^ m), Finset.mul_sum, Finset.sum_mul,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_assoc]

theorem rmHol_of (hT : AtTrace) (hD : AtDer) : RmHol := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_hol lam hD hlam M i j hg false a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_hol lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam g * (At lam ^ m) a a * M) i j = (Rm lam g * (At lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e, hT n lam hlam m]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
end
end

section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem updateRow_smooth (j : Fin n) (v : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Mat n => x.updateRow j v) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    have e : (fun x : Mat n => x.updateRow k v k) = fun _ => v := by funext x; simp [Matrix.updateRow_apply]
    rw [e]; exact contDiff_const
  · have e : (fun x : Mat n => x.updateRow j v k) = fun x : Mat n => (x : Fin n → Fin n → ℂ) k := by
      funext x; simp [Matrix.updateRow_apply, hk]
    rw [e]; exact contDiff_apply ℝ (Fin n → ℂ) k

theorem adjugate_smooth : ContDiff ℝ ∞ (fun x : Mat n => x.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun x : Mat n => x.adjugate i j) = fun x : Mat n => (x.updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [e]
  exact Cxc.det_smooth.comp (updateRow_smooth j _)

theorem inv_smooth : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun x : Mat n => Matrix.of fun i j => x.det ^ (-1 : ℤ) * x.adjugate i j) (GLs n) := by
    refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
    exact (Cxc.detPow_smooth (-1)).mul ((contDiff_apply_apply ℝ ℂ i j).comp adjugate_smooth).contDiffOn
  refine h.congr fun x hx => ?_
  ext i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp [_root_.zpow_neg_one]

def cTL : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }

theorem det_inv_ne {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹).det ≠ 0 := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero hx

theorem mem_theta {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  show ((x⁻¹)ᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact (star_ne_zero).2 (det_inv_ne hx)

theorem theta_diff {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (fun y : Mat n => (y⁻¹)ᴴ) x := by
  have h := (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  exact cTL.differentiableAt.comp x h

theorem hasDerivAt_mat_mul {m : Type} [Fintype m] [DecidableEq m] {P Q : ℝ → Matrix m m ℂ} {P' Q' : Matrix m m ℂ}
    (hP : HasDerivAt P P' 0) (hQ : HasDerivAt Q Q' 0) :
    HasDerivAt (fun t => P t * Q t) (P' * Q 0 + P 0 * Q') 0 := by
  have hP2 : ∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0 := fun i k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQ2 : ∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0 := fun k j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have h := HasDerivAt.sum (u := Finset.univ) fun k _ => (hP2 i k).mul (hQ2 k j)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  · funext t; simp [Finset.sum_apply]
  · simp [Finset.sum_add_distrib, mul_comm]

theorem hasDerivAt_inv_line (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hd : DifferentiableAt ℝ (fun x : Mat n => x⁻¹) (1 : Mat n) :=
    (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)
  have hu : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (fderiv ℝ (fun x : Mat n => x⁻¹) 1 X) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    exact this
  have hprod := hasDerivAt_mat_mul hc hu
  have hconst : (fun t : ℝ => (1 + t • X) * (1 + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n) := by
    filter_upwards [eventually_det X] with t ht
    exact Matrix.mul_nonsing_inv _ ht
  have h0 := (hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hconst
  have e := hprod.unique h0
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at e
  have e2 : fderiv ℝ (fun x : Mat n => x⁻¹) 1 X = -X := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
  rwa [e2] at hu

theorem hasDerivAt_rm_theta (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam ((1 + t • X)⁻¹)ᴴ) (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => ((1 + t • X)⁻¹)ᴴ) (-Xᴴ) 0 := by
    have := cTL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_inv_line X)
    exact this.congr_deriv (Matrix.conjTranspose_neg X)
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have h := (rm_diff lam h1).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  exact h.congr_deriv (hD n lam hlam _)

theorem rd_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = (Rm lam (x⁻¹)ᴴ * (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) * N) i j := by
  have hdf : DifferentiableAt ℝ (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x := by
    have : (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) = entL 1 N i j ∘ Rm lam ∘ fun y : Mat n => (y⁻¹)ᴴ := by
      funext y; simp [entL_apply]
    rw [this]
    exact (entL 1 N i j).differentiableAt.comp x ((rm_diff lam (mem_theta hx)).comp x (theta_diff hx))
  have h1 := hasDerivAt_line hdf X
  have h2 : HasDerivAt (fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ))
      (entL (Rm lam (x⁻¹)ᴴ) N i j (∑ a, ∑ b, (-Xᴴ) a b • At lam a b)) 0 :=
    (entL (Rm lam (x⁻¹)ᴴ) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_theta lam hD hlam X)
  have hxu : IsUnit ((x⁻¹)ᴴ).det := isUnit_iff_ne_zero.2 (mem_theta hx)
  have h3 : (fun t : ℝ => (Rm lam ((x * (1 + t • X))⁻¹)ᴴ * N) i j) =ᶠ[nhds 0]
      fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ) := by
    filter_upwards [eventually_det X] with t ht
    have ht' : IsUnit (((1 + t • X)⁻¹)ᴴ).det := by
      rw [Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact (isUnit_iff_ne_zero.2 (star_ne_zero.2 (inv_ne_zero (isUnit_iff_ne_zero.1 ht))))
    rw [entL_apply, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Cxc.rm_mul lam _ _ hxu ht']
  exact h1.unique (h2.congr_of_eventuallyEq h3)

theorem sum_single_neg {lam : Fin n → ℤ} (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (-(Matrix.single a b z : Mat n)ᴴ) c d • A c d = (-star z) • A b a := by
  rw [Matrix.conjTranspose_single]
  simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]
  rw [sum_single (lam := lam) 0 b a _ A]

theorem eu_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = if s then 0 else (Rm lam (x⁻¹)ᴴ * -At lam b a * N) i j := by
  have e1 := rd_anti lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_anti lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single_neg a b 1 (At lam)] at e1
  rw [sum_single_neg a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.add_apply, Pi.smul_apply, e1, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
  cases s <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def Bt (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) := Matrix.of fun a b => -(At lam b a)

theorem epow_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow false m a b (fun y => (Rm lam (y⁻¹)ᴴ * M) i j))
      (fun y => (Rm lam (y⁻¹)ᴴ * (Bt lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y _
    simp only [Epow, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro a b y hy
    simp only [Epow, Finset.sum_apply]
    have e : ∀ c, Eu false a c (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) y =
        (Rm lam (y⁻¹)ᴴ * Bt lam a c * ((Bt lam ^ m) c b * M)) i j := by
      intro c
      have hev : (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) =ᶠ[nhds y]
          fun y => (Rm lam (y⁻¹)ᴴ * ((Bt lam ^ m) c b * M)) i j := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        rw [ih c b hz]
        simp only [Matrix.mul_assoc]
      rw [eu_congr hev, eu_anti lam hD hlam _ i j hy]
      simp [Bt, Matrix.mul_assoc]
    simp only [e]
    have hp : (Bt lam ^ (m + 1)) a b = ∑ c, Bt lam a c * (Bt lam ^ m) c b := by rw [pow_succ', Matrix.mul_apply]
    show ∑ c, _ = (Rm lam (y⁻¹)ᴴ * (Bt lam ^ (m + 1)) a b * M) i j
    rw [hp, Matrix.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mul_assoc]

theorem rmAnti_of (hT : AtTraceT) (hD : AtDer) : RmAnti := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_anti lam hD hlam M i j hg true a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_anti lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m) a a * M) i j = (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e]
  have hB : (Bt lam ^ m).trace = GlobalTheory.Dec.gelfVal (infOf lam false) m • (1 : Matrix (Jd n lam) (Jd n lam) ℂ) :=
    hT n lam hlam m
  rw [hB]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
end
end

section
namespace PositivityTheory.RgBcC

theorem rmHol : RmHol := Cxd2.rmHol_of Cxd2.atTrace Cxd2.atDer

theorem rmAnti : RmAnti := Cxd2.rmAnti_of Cxd2.atTraceT Cxd2.atDer

end PositivityTheory.RgBcC
end
