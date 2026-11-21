import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
end

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernConnection_curvature_polyRep_eval : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧ curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  atlas_forward_decl GlobalTheory.GoodMetric.conn_curvPoly_ev
end

section
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RepBound

theorem poly_bound {σ : Type} (P : MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ‖aeval x P‖ ≤ C * B ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖(a : ℂ)‖, 0, norm_nonneg _, fun B _ x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    obtain ⟨C2, d2, h2, hq⟩ := hq
    refine ⟨C1 + C2, d1 + d2, by positivity, fun B hB x hx => ?_⟩
    rw [map_add]
    have e1 : B ^ d1 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    have e2 : B ^ d2 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    calc ‖aeval x p + aeval x q‖ ≤ ‖aeval x p‖ + ‖aeval x q‖ := norm_add_le _ _
      _ ≤ C1 * B ^ d1 + C2 * B ^ d2 := add_le_add (hp B hB x hx) (hq B hB x hx)
      _ ≤ C1 * B ^ (d1 + d2) + C2 * B ^ (d1 + d2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * B ^ (d1 + d2) := by ring
  | mul_X p s hp =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    refine ⟨C1, d1 + 1, h1, fun B hB x hx => ?_⟩
    rw [map_mul, aeval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hp B hB x hx) (hx s) (norm_nonneg _)
      (mul_nonneg h1 (pow_nonneg (by linarith) _))

theorem poly_bound_fam {κ σ : Type} [Fintype κ] (P : κ → MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ∀ k, ‖aeval x (P k)‖ ≤ C * B ^ d := by
  choose C d hC h using fun k => poly_bound (P k)
  refine ⟨∑ k, C k, ∑ k, d k, Finset.sum_nonneg fun k _ => hC k, fun B hB x hx k => ?_⟩
  exact (h k B hB x hx).trans (mul_le_mul
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ k))
    (pow_le_pow_right₀ hB (Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ k)))
    (pow_nonneg (by linarith) _) (Finset.sum_nonneg fun k _ => hC k))

variable {ι : Type} {m : ι → ℕ}

def adjPoly (m : ι → ℕ) (w : EntIx m) : MvPolynomial (EntIx m) ℤ :=
  Matrix.adjugate (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)) w.2.1 w.2.2

theorem aeval_adjPoly (A : Mat m ℂ) (w : EntIx m) :
    aeval (fun u : EntIx m => A u.1 u.2.1 u.2.2) (adjPoly m w) = (A w.1).adjugate w.2.1 w.2.2 := by
  have e : (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)).map
      (aeval fun u : EntIx m => A u.1 u.2.1 u.2.2) = A w.1 := by
    ext p q; simp
  rw [← e]
  exact congrFun (congrFun (RingHom.map_adjugate (aeval (R := ℤ) fun u : EntIx m => A u.1 u.2.1 u.2.2).toRingHom _) w.2.1) w.2.2

variable [Fintype ι]

def lieCoeff (ρ : PolyRep m) (i j : Fin ρ.M) (w : EntIx m) : ℂ :=
  aeval (fun u : EntIx m => (1 : Mat m ℂ) u.1 u.2.1 u.2.2) (pderiv w (ρ.ent i j))

theorem lie_apply (ρ : PolyRep m) (A : Mat m ℂ) (i j : Fin ρ.M) :
    ρ.lie A i j = ∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2 := rfl

def lieNorm (ρ : PolyRep m) : ℝ := ∑ i, ∑ j, ∑ w, ‖lieCoeff ρ i j w‖

theorem lieNorm_nonneg (ρ : PolyRep m) : 0 ≤ lieNorm ρ := by unfold lieNorm; positivity

theorem norm_lie_mul_le (ρ : PolyRep m) (A : Mat m ℂ) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ w : EntIx m, ‖A w.1 w.2.1 w.2.2‖ * t ≤ c) (i j : Fin ρ.M) :
    ‖ρ.lie A i j‖ * t ≤ lieNorm ρ * |c| := by
  have h1 : ‖ρ.lie A i j‖ * t ≤ ∑ w, ‖lieCoeff ρ i j w‖ * |c| := by
    rw [lie_apply]
    calc ‖∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖ * t
        ≤ (∑ w, ‖lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖) * t :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht
      _ = ∑ w, ‖lieCoeff ρ i j w‖ * (‖A w.1 w.2.1 w.2.2‖ * t) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w _ => ?_; rw [norm_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left ((h w).trans (le_abs_self c)) (norm_nonneg _)
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg c)
  unfold lieNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖lieCoeff ρ i j w‖)
    (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ∑ w, ‖lieCoeff ρ i j w‖) (fun j _ => by positivity)
    (Finset.mem_univ j)

theorem lie_neg (ρ : PolyRep m) (A : Mat m ℂ) : ρ.lie (fun τ => -A τ) = -ρ.lie A := by
  ext i j; simp [lie_apply, Finset.sum_neg_distrib]

theorem lie_sub (ρ : PolyRep m) (A B : Mat m ℂ) : ρ.lie (fun τ => A τ - B τ) = ρ.lie A - ρ.lie B := by
  ext i j; simp [lie_apply, mul_sub, Finset.sum_sub_distrib]

theorem mdel_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdel (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdel (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdel_apply, lie_apply]
  rw [del_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [del_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem mdbar_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdbar (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdbar (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdbar_apply, lie_apply]
  rw [dbar_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem poinWt_nonneg {n : ℕ} (S : Finset (Fin n)) (v : V n) (a : Fin n) : 0 ≤ poinWt S v a := by
  unfold poinWt; split_ifs <;> positivity

end GlobalTheory.RepBound

namespace GlobalTheory.RepBound

theorem le_mul_pow_of_le {x K c' L : ℝ} {e N' : ℕ} (hx : x ≤ K * L ^ e) (hK : K ≤ c') (hK0 : 0 ≤ K)
    (hL : 1 ≤ L) (he : e ≤ N') : x ≤ c' * L ^ N' :=
  hx.trans (mul_le_mul hK (pow_le_pow_right₀ hL he) (pow_nonneg (by linarith) _) (hK0.trans hK))

theorem goodBound_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ),
    ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) →
      (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) →
        GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  intro ι _ m ρ c N
  obtain ⟨C1, d1, hC1, h1⟩ := poly_bound_fam (fun p : Fin ρ.M × Fin ρ.M => ρ.ent p.1 p.2)
  obtain ⟨C2, d2, hC2, h2⟩ := poly_bound ρ.ent.det
  obtain ⟨C3, d3, hC3, h3⟩ := poly_bound_fam (adjPoly m)
  have hc₁ : 1 ≤ max c 1 := le_max_right _ _
  have hc₀ : 0 ≤ max c 1 := by linarith
  have hK1 : 0 ≤ C1 * max c 1 ^ d1 := mul_nonneg hC1 (pow_nonneg hc₀ _)
  have hK2 : 0 ≤ C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) :=
    mul_nonneg (mul_nonneg hC2 (pow_nonneg (by linarith) _)) (pow_nonneg hc₀ _)
  have hK3 : 0 ≤ lieNorm ρ * |c| := mul_nonneg (lieNorm_nonneg ρ) (abs_nonneg c)
  refine ⟨C1 * max c 1 ^ d1 + C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) + lieNorm ρ * |c|,
    N * d1 + N * ((d3 + 1) * d2), ?_⟩
  intro n S G v hG hdet hL hB
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := by linarith
  set B := max c 1 * L ^ N with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hc₁ (one_le_pow₀ hL)
  have hx : ∀ w : EntIx m, ‖G v w.1 w.2.1 w.2.2‖ ≤ B := fun w =>
    ((hB w.1).entry w.2.1 w.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
  have hu : ∀ τ, IsUnit (G v τ).det := fun τ => isUnit_iff_ne_zero.2 (hdet τ)
  have hcv := (GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ n G v hG hdet).1
  have hcvE : ∀ ξ, (fun u => conn (fun w => ρ.ev (G w)) u ξ) =ᶠ[𝓝 v]
      (fun u => ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) := fun ξ => hcv.mono fun u hu => hu ξ
  have hc1 : ∀ τ ξ, MContDiffAt 1 (fun u => conn (fun w => G w τ) u ξ) v :=
    fun τ ξ => (hG τ).conn (hu τ) (by norm_num) ξ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change ‖ρ.ev (G v) i j‖ ≤ _
    have := h1 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx (i, j)
    refine le_mul_pow_of_le (K := C1 * max c 1 ^ d1) (e := N * d1) ?_ (by linarith) hK1 hL (by omega)
    refine this.trans_eq ?_
    rw [hBdef, mul_pow, ← pow_mul]; ring
  · change ‖(ρ.ev (G v)).det‖⁻¹ ≤ _
    set Gi : Mat m ℂ := fun τ => (G v τ)⁻¹ with hGi
    have hmul : ρ.ev (G v) * ρ.ev Gi = 1 := by
      have e : G v * Gi = 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hu τ)
      rw [PolyRep.ev, PolyRep.ev, ← ρ.mul ℂ, e]
      exact ρ.one ℂ
    have hdm : (ρ.ev (G v)).det * (ρ.ev Gi).det = 1 := by rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hinv : ‖(ρ.ev (G v)).det‖⁻¹ = ‖(ρ.ev Gi).det‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right hdm]
    have hpoly : (ρ.ev Gi).det = aeval (fun w : EntIx m => Gi w.1 w.2.1 w.2.2) ρ.ent.det :=
      (AlgHom.map_det _ _).symm
    have hy : ∀ w : EntIx m, ‖Gi w.1 w.2.1 w.2.2‖ ≤ (C3 + 1) * B ^ (d3 + 1) := by
      intro w
      have ha := h3 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx w
      rw [aeval_adjPoly (G v) w] at ha
      have hd : ‖(G v w.1).det‖⁻¹ ≤ B :=
        ((hB w.1).det).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
      have e : Gi w.1 w.2.1 w.2.2 = ((G v w.1).det)⁻¹ * (G v w.1).adjugate w.2.1 w.2.2 := by
        simp [hGi, Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e, norm_mul, norm_inv]
      have hBd : 0 ≤ B ^ d3 := pow_nonneg (by linarith) _
      calc ‖(G v w.1).det‖⁻¹ * ‖(G v w.1).adjugate w.2.1 w.2.2‖ ≤ B * (C3 * B ^ d3) :=
            mul_le_mul hd ha (norm_nonneg _) (by linarith)
        _ ≤ (C3 + 1) * B ^ (d3 + 1) := by
            rw [pow_succ]; nlinarith [mul_nonneg hBd (by linarith : (0:ℝ) ≤ B)]
    have hB2 : 1 ≤ (C3 + 1) * B ^ (d3 + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hB1)
    have hd2 := h2 _ hB2 _ hy
    rw [hinv, hpoly]
    refine le_mul_pow_of_le (K := C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2))
      (e := N * ((d3 + 1) * d2)) ?_ (by linarith) hK2 hL (by omega)
    refine hd2.trans_eq ?_
    rw [hBdef, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  · intro a i j
    change ‖conn (fun u => ρ.ev (G u)) v (coordVec a) i j‖ * poinWt S v a ≤ _
    have e := (hcvE (coordVec a)).self_of_nhds
    simp only at e
    rw [e]
    exact (norm_lie_mul_le ρ _ (poinWt_nonneg S v a) (fun w => (hB w.1).form a w.2.1 w.2.2) i j).trans
      (by linarith)
  · intro a b i j
    have e : curv (fun u => ρ.ev (G u)) v (coordVec a) (coordVec b) =
        ρ.lie (fun τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)) := by
      rw [curv, mdbar_congr (hcvE (coordVec a)), mdbar_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_neg]
      rfl
    rw [e]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).dbar a b w.2.1 w.2.2) i j).trans (by linarith)
  · intro a b i j
    rw [mdel_congr (hcvE (coordVec b)), mdel_congr (hcvE (coordVec a)),
      mdel_lie ρ (fun τ => hc1 τ (coordVec b)), mdel_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_sub]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).del a b w.2.1 w.2.2) i j).trans (by linarith)

end GlobalTheory.RepBound
end
end

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) → GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  atlas_forward_decl GlobalTheory.RepBound.goodBound_ev
end

section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_inducedBundle_and_metric : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  first | exact @GlobalTheory.GoodMetric.RepBundle.exists_repBundle | exact GlobalTheory.GoodMetric.RepBundle.exists_repBundle | (intros; apply GlobalTheory.GoodMetric.RepBundle.exists_repBundle <;> assumption)
end

section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z
        rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ ℂ _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
end
end

section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  first | exact @GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | exact GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | (intros; apply GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top <;> assumption)
end

section
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodMetric

theorem hasChernIntegral_top_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  intro h F _ σ X ι _ m E H hH R
  obtain ⟨Y, E', φ, f, gr, -, hR, hg⟩ := Model.exists_flagSpace X E
  exact ⟨_, h F σ X Y ι m E E' φ f gr hR hg H hH R⟩

end GlobalTheory.GoodMetric
end

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_integrable_complexPoints_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  atlas_forward_decl GlobalTheory.GoodMetric.hasChernIntegral_top_of_chernWeil
end

section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ) (J : Type) [Fintype J] (M : J → ℕ) (E' : ∀ j, Fr (ratOf X) (fun _ : Unit => M j) 0) (H' : ∀ j, Mat (fun _ : Unit => M j) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => M j) ℂ) (R' : MvPolynomial (Unit × ℕ) ℝ) (a t : J → ℝ), IsMetricOn E O H → (∀ j, IsMetricOn (E' j) O (H' j)) → (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y), ∃ B : ∀ j, Mat (fun _ : Unit => M j) X.Fn, (∀ j, B j ∈ (E' j).S (under y)) ∧ chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ∑ j, a j * chernTop R' (fun v => H' j (B j) (c.e.symm v)) (c.e y)) → (∀ j, HasChernIntegral (E' j) O (H' j) R' (t j)) → HasChernIntegral E O H R (∑ j, a j * t j) := by
  first | exact @GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | exact GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | (intros; apply GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder ContDiff

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ}

theorem eventually_regAt_under {y : CxPts X.str σ} {g : X.Fn} (hg : RegAt (under y) g) :
    ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt_under (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt_under (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem CInfAt.contDiffAt_holoChart {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hy : y ∈ e.source) :
    ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  obtain ⟨W, κ, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := isOpen_over e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hl := e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev X.str σ W (g a) (e.symm w)) (e y) :=
    contDiffAt_pi.2 fun a => (contDiffOn_real ho (he W (g a))).contDiffAt (ho.mem_nhds (mem_over e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ G (fun a => ev X.str σ W (g a) (e.symm (e y))) := by
    rw [hl]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (e y) hg).congr_of_eventuallyEq ?_
  have := e.continuousAt_symm (e.map_source hy)
  rw [ContinuousAt, hl] at this
  exact this.eventually h₅

theorem IsMetricOn.mContDiffAt_two {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0} {O : X.X.Opens}
    {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ} (hH : IsMetricOn E O H) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) (τ : ι) :
    MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := fun i j => by
  obtain ⟨hre, him⟩ := hH.smooth y hy A hA τ i j
  have h1 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).re) (e y) :=
    (CInfAt.contDiffAt_holoChart hre he hye).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).im) (e y) :=
    (CInfAt.contDiffAt_holoChart him he hye).of_le (by norm_cast)
  have h3 : ContDiffAt ℝ 2 (fun v => ((H A (e.symm v) τ i j).re : ℂ) + ((H A (e.symm v) τ i j).im : ℂ) * Complex.I) (e y) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h1).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ h2).mul contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  exact (Complex.re_add_im _).symm

theorem curvPoly_polyRep {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {E : Fr (ratOf X) m 0}
    {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    {H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ} (hH : IsMetricOn E O H)
    (hρ : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y))
    {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) :
    curvPoly (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) (e y) =
      ρ.lie (fun τ => curvPoly (fun v => H A (e.symm v) τ) (e y)) := by
  have hG2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := hH.mContDiffAt_two hy hA he hye
  have hdet : ∀ τ, (H A (e.symm (e y)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hye]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y hy A hA τ).isUnit).ne_zero
  obtain ⟨-, hc⟩ := GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ X.dim (fun v => H A (e.symm v)) (e y) hG2 hdet
  rw [← hc]
  have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hye)
    rwa [ContinuousAt, e.left_inv hye] at this
  have heq : (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => ρ.ev (H A (e.symm v)) := by
    filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hy), ht.eventually (eventually_mem_frames hA)] with v h1 h2
    exact hρ _ h1 A h2
  simp only [curvPoly, curv_congr heq]

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.Bridge

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.GoodMetric.isGood_polyRep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (ρ : PolyRep m) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0) (O : X.X.Opens)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ),
    (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) → IsMetricOn E O H →
      (∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y)) →
        IsGood E O H → IsGood E' O H' := by
  intro F _ σ X ι _ m ρ E E' O H H' hS hH hρ hG y hy
  obtain ⟨e, S, he, hye, hS0, hSO, A, hA, c, N, hev⟩ := hG y hy
  obtain ⟨c', N', hgood⟩ := GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation ι m ρ c N
  refine ⟨e, S, he, hye, hS0, hSO, fun _ => ρ.ev A, hS _ A hA, c', N', ?_⟩
  obtain ⟨a₀, ha₀S, ha₀⟩ := (hSO y hye).1 hy
  have hcont : ContinuousAt (fun z => e z a₀) y :=
    (EuclideanSpace.proj (𝕜 := ℂ) a₀).continuous.continuousAt.comp (e.continuousAt hye)
  have hsmall : ∀ᶠ z in 𝓝 y, ‖e z a₀‖ < Real.exp (-1) := by
    have h0 : Tendsto (fun z => e z a₀) (𝓝 y) (𝓝 0) := by
      have := hcont.tendsto
      rwa [ha₀] at this
    exact h0.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
  filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds (e.open_source.mem_nhds hye),
    nhdsWithin_le_nhds (eventually_mem_frames hA), nhdsWithin_le_nhds hsmall] with z hz hzO hzs hzA hzsm
  rintro ⟨⟩
  have hz2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e z) := hH.mContDiffAt_two hzO hzA he hzs
  have hdet : ∀ τ, (H A (e.symm (e z)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hzs]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef z hzO A hzA τ).isUnit).ne_zero
  have hne : e z a₀ ≠ 0 := fun h0 => ((hSO z hzs).2 ⟨a₀, ha₀S, h0⟩) hzO
  have hpos : 0 < ‖e z a₀‖ := norm_pos_iff.2 hne
  have hlt : Real.log ‖e z a₀‖ < -1 := by rw [Real.log_lt_iff_lt_exp hpos]; exact hzsm
  have h1 : 1 ≤ |Real.log ‖e z a₀‖| := by rw [abs_of_neg (by linarith)]; linarith
  have hlog : 1 ≤ ∑ a ∈ S, |Real.log ‖e z a‖| :=
    h1.trans (Finset.single_le_sum (f := fun a => |Real.log ‖e z a‖|) (fun a _ => abs_nonneg _) ha₀S)
  have hb := hgood X.dim S (fun v => H A (e.symm v)) (e z) hz2 hdet hlog hz
  refine goodBound_congr_nhds X.dim (Fin ρ.M) S c' N' _ _ (e z) ?_ hb
  have ht : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    have := e.continuousAt_symm (e.map_source hzs)
    rwa [ContinuousAt, e.left_inv hzs] at this
  filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hzO), ht.eventually (eventually_mem_frames hzA)]
    with v h1 h2
  exact (hρ _ h1 A h2).symm

theorem _root_.GlobalTheory.GoodMetric.goodChernWeil_of_goodTopChernForm :
    GlobalTheory.Published.GoodTopChernForm → GlobalTheory.Published.ChernWeilNumbers → GlobalTheory.Published.FlagPushForward → GlobalTheory.Published.GoodChernWeil := by
  intro hT hCW hP
  refine ⟨?_, hP⟩
  intro F _ σ X Y ι _ m E E' φ f gr hRef hGr O H hH hG R
  obtain ⟨J, _, ρ, a, hAlg⟩ := GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_sum_representations ι m X.dim R
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety F σ X ι m E
  choose Eb hEbS hEbH using fun j => GlobalTheory.T.exists_polyRep_inducedBundle_and_metric F X ι m (ρ j) E
  choose H' hH' hH'eq using fun j => hEbH j σ O H hH
  choose H₀' hH₀' hH₀'eq using fun j => hEbH j σ ⊤ H₀ hH₀
  choose t ht using fun j => GlobalTheory.T.chernForm_integrable_complexPoints_of_chernWeil hCW F σ X Unit (fun _ => (ρ j).M) (Eb j) (H₀' j) (hH₀' j)
    (MvPolynomial.X ((), X.dim))
  have htO : ∀ j, HasChernIntegral (Eb j) O (H' j) (MvPolynomial.X ((), X.dim)) (t j) := fun j =>
    hT F σ X (ρ j).M (Eb j) O (H' j) (H₀' j) (hH' j)
      (isGood_polyRep F σ X ι m (ρ j) E (Eb j) O H (H' j) (hEbS j) hH (hH'eq j) hG) (hH₀' j) (t j) (ht j)

  have hdens : ∀ (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
      (H' : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => (ρ j).M) ℂ),
      IsMetricOn E O H →
      (∀ j, ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' j (fun _ => (ρ j).ev A) y () = (ρ j).ev (H A y)) →
      ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y),
        ∃ B : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn, (∀ j, B j ∈ (Eb j).S (under y)) ∧
          chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
            ∑ j, a j * chernTop (MvPolynomial.X ((), X.dim)) (fun v => H' j (B j) (c.e.symm v)) (c.e y) := by
    intro O H H' hH hH'eq y hy c hc
    obtain ⟨A, hA⟩ := E.nonempty (under y)
    refine ⟨A, hA, fun j _ => (ρ j).ev A, fun j => hEbS j _ A hA, ?_⟩
    have hcurv : ∀ j, curvPoly (fun v => H' j (fun _ => (ρ j).ev A) (c.e.symm v) ()) (c.e y) =
        (ρ j).lie (fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) := fun j =>
      curvPoly_polyRep (ρ j) hH (hH'eq j) hy hA c.holo hc
    have hhom : ∀ τ i j, ((fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) τ i j).IsHomogeneous 1 :=
      fun τ i j => by
        simp only [curvPoly, Matrix.of_apply]
        exact IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ _
    have key := hAlg _ hhom
    simp only [chernTop, chernPoly, aeval_X]
    rw [key]
    simp only [hcurv, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlinO := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E O H R J (fun j => (ρ j).M) Eb H' (MvPolynomial.X ((), X.dim)) a t hH hH'
    (hdens O H H' hH hH'eq) htO
  have hlinT := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E ⊤ H₀ R J (fun j => (ρ j).M) Eb H₀' (MvPolynomial.X ((), X.dim)) a t hH₀ hH₀'
    (hdens ⊤ H₀ H₀' hH₀ hH₀'eq) ht
  have hs := hCW F σ X Y ι m E E' φ f gr hRef hGr H₀ hH₀ R
  rw [hs.2.symm.trans hlinT.2]
  exact hlinO

end GlobalTheory.GoodMetric.Bridge
end
end
