import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN

section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

def LowUni {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) : Prop := by
  first | exact @Bl.FirstLemmaN.goal1 n L | exact @Bl.FirstLemmaN.goal1 n | exact @Bl.FirstLemmaN.goal1

def UpTri {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → U i j = 0

def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.lastCases (Fin.lastCases e row j) (fun i' => Fin.lastCases (col i') (fun j' => P i' j') j) i

@[simp] theorem blk_cc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk P col row e i.castSucc j.castSucc = P i j := by simp [blk]

@[simp] theorem blk_cl {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk P col row e i.castSucc (Fin.last n) = col i := by simp [blk]

@[simp] theorem blk_lc {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk P col row e (Fin.last n) j.castSucc = row j := by simp [blk]

@[simp] theorem blk_ll {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (col row : Fin n → ℂ) (e : ℂ) :
    blk P col row e (Fin.last n) (Fin.last n) = e := by simp [blk]

theorem det_lowUni {n : ℕ} {L : Matrix (Fin n) (Fin n) ℂ} (h : LowUni L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem exists_LU : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ k (hk : k < n), (g.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0) →
    ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g = L * U
  | 0, g, _ => ⟨1, g, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | n + 1, g, hg => by
    set A : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.castSucc Fin.castSucc with hA
    have hAk : ∀ k (hk : k < n), (A.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0 := by
      intro k hk
      have := hg k (by omega)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL', hU', hLU⟩ := exists_LU n A hAk
    have hdetA : A.det ≠ 0 := by
      have := hg n (by omega)
      convert this using 2
      ext i j; rfl
    have hdL : L'.det = 1 := det_lowUni hL'
    have hdU : U'.det ≠ 0 := by
      intro h0; apply hdetA; rw [hLU, Matrix.det_mul, h0, mul_zero]
    have iL : IsUnit L'.det := by rw [hdL]; exact isUnit_one
    have iU : IsUnit U'.det := isUnit_iff_ne_zero.2 hdU
    set c : Fin n → ℂ := fun j => g (Fin.last n) j.castSucc
    set b : Fin n → ℂ := fun i => g i.castSucc (Fin.last n)
    set r : Fin n → ℂ := Matrix.vecMul c U'⁻¹
    set q : Fin n → ℂ := L'⁻¹ *ᵥ b
    refine ⟨blk L' 0 r 1, blk U' q 0 (g (Fin.last n) (Fin.last n) - r ⬝ᵥ q), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL'.2 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hU' i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cl, blk_ll]
          simp [dotProduct]
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cc, blk_ll, blk_lc]
          have : (Matrix.vecMul r U') j = c j := by
            simp only [r, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ iU, Matrix.vecMul_one]
          simp only [Pi.zero_apply, mul_zero, add_zero]
          exact this.symm
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, Pi.zero_apply, zero_mul, add_zero]
          have : (L' *ᵥ q) i = b i := by
            simp only [q, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ iL, Matrix.one_mulVec]
          exact this.symm
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, blk_lc, Pi.zero_apply, zero_mul,
            add_zero]
          rw [← Matrix.mul_apply, ← hLU]; rfl

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section
noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

theorem eventually_not_mem_of_finite {F : Set ℂ} (hF : F.Finite) : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ∉ F := by
  have h1 : ∀ᶠ x in 𝓝 (0 : ℂ), x ∉ F \ {0} :=
    (hF.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx hx0
  exact fun hxF => hx ⟨hxF, hx0⟩

theorem det_add_smul_eventually {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (A + x • (1 : Matrix (Fin k) (Fin k) ℂ)).det ≠ 0 := by
  have hp : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  filter_upwards [eventually_not_mem_of_finite (Polynomial.finite_setOf_isRoot hp)] with x hx
  intro h0
  apply hx
  show Polynomial.IsRoot _ x
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply, sub_neg_eq_add, add_comm,
    ← Matrix.smul_one_eq_diagonal]
  exact h0

theorem dense_LU {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 ∧
      ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g + x • (1 : Matrix (Fin n) (Fin n) ℂ) = L * U := by
  have hsub : ∀ (x : ℂ) (m : ℕ) (hm : m ≤ n),
      (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm) =
        g.submatrix (Fin.castLE hm) (Fin.castLE hm) + x • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro x m hm
    simp only [Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply]
    rw [Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  have hmin : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ∀ m : Fin (n + 1),
      (g.submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2)) (Fin.castLE (Nat.lt_succ_iff.mp m.2)) +
        x • (1 : Matrix (Fin m) (Fin m) ℂ)).det ≠ 0 :=
    Filter.eventually_all.2 fun m => det_add_smul_eventually _
  filter_upwards [det_add_smul_eventually g, hmin] with x hdet hm
  refine ⟨hdet, PI.UnitaryGroupMassFormula.HwConjInf.exists_LU n _ (fun k hk => ?_)⟩
  rw [hsub]
  exact hm ⟨_, by omega⟩

theorem tendsto_add_smul {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝[≠] 0) (𝓝 g) := by
  have h : Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝 0)
      (𝓝 (g + (0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :=
    tendsto_const_nhds.add (tendsto_id.smul_const _)
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section
noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

def mPt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then M p.2.1 p.2.2 else (M⁻¹) p.2.2 p.2.1

theorem gPt_eq {n : ℕ} (g : GL (Fin n) ℂ) : gPt g = mPt g.val := by
  funext p
  unfold gPt mPt
  rw [Matrix.coe_units_inv]

theorem mPt_continuousAt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt mPt M := by
  rw [continuousAt_pi]
  rintro ⟨b, i, j⟩
  cases b
  · simp only [mPt, Bool.false_eq_true, if_false]
    have h1 : ContinuousAt (fun N : Matrix (Fin n) (Fin n) ℂ => N⁻¹) M :=
      continuousAt_matrix_inv M (by simpa [isUnit_iff_ne_zero] using hM)
    exact (continuous_apply_apply j i).continuousAt.comp h1
  · simp only [mPt, if_true]
    exact (continuous_apply_apply i j).continuousAt

def Rm {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix ι ι ℂ := fun i j => MvPolynomial.eval (mPt M) (Q i j)

theorem Rm_continuousAt {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt (Rm Q) M := by
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact ((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp (mPt_continuousAt M hM)

def dd {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t), Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)),
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add],
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add]⟩

theorem dd_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    (dd c t).val = Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t) := rfl

theorem dd_inv_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    ((dd c t)⁻¹).val = Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)) := rfl

theorem dd_tri {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : (dd c t).val.BlockTriangular id := by
  rw [dd_val]
  exact Matrix.blockTriangular_diagonal _

def phi {n : ℕ} (c lam : Fin n → ℤ) : ℤ := ∑ i, c i * lam i

theorem char_dd {n : ℕ} (c lam : Fin n → ℤ) (t : ℝ) :
    ∏ i, (dd c t).val i i ^ lam i = Complex.exp ((phi c lam : ℂ) * t) := by
  rw [dd_val]
  simp only [Matrix.diagonal_apply_eq]
  rw [show (phi c lam : ℂ) * t = ∑ i, (lam i : ℂ) * ((c i : ℂ) * t) by
    unfold phi
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Complex.exp_int_mul ((c i : ℂ) * t) (lam i)).symm

theorem tendsto_exp_neg {k : ℤ} (hk : k < 0) :
    Tendsto (fun t : ℝ => Complex.exp ((k : ℂ) * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun t : ℝ => ‖Complex.exp ((k : ℂ) * t)‖) = fun t => Real.exp ((k : ℝ) * t) := by
    funext t
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [h]
  apply Real.tendsto_exp_atBot.comp
  exact Filter.tendsto_id.const_mul_atTop_of_neg (by exact_mod_cast hk)

theorem wt_le {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j))
    (hmul : ∀ g h, R (g * h) = R g * R h)
    (S : Set (Matrix ι ι ℂ)) (hS : ∀ s ∈ S, ∀ g, s * R g = R g * s)
    (v u : ι → ℂ) (lam mu : Fin n → ℤ)
    (hv : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v)
    (hu : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u)
    (hmem : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)})
    (hu0 : u ≠ 0) (c : Fin n → ℤ) (hc : ∀ i j, i < j → c j < c i) :
    phi c mu ≤ phi c lam := by
  have hR : ∀ g : GL (Fin n) ℂ, R g = Rm Q g.val := by
    intro g; ext i j; rw [hRQ, Rm, gPt_eq]
  set f : (ι → ℂ) → ℝ → (ι → ℂ) := fun w t => Complex.exp (-((phi c lam : ℂ) * t)) • (R (dd c t) *ᵥ w) with hf
  let P : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∃ y, Tendsto (f w) atTop (𝓝 y)}
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        refine ⟨ya + yb, ?_⟩
        have e : f (a + b) = fun t => f a t + f b t := by funext t; simp [hf, Matrix.mulVec_add, smul_add]
        rw [e]; exact ha.add hb
      zero_mem' := ⟨0, by
        have e : f 0 = fun _ => 0 := by funext t; simp [hf]
        rw [e]; exact tendsto_const_nhds⟩
      smul_mem' := by
        rintro r a ⟨ya, ha⟩
        refine ⟨r • ya, ?_⟩
        have e : f (r • a) = fun t => r • f a t := by funext t; simp [hf, Matrix.mulVec_smul, smul_comm r]
        rw [e]; exact ha.const_smul r }

  have hgenL : ∀ s ∈ S, ∀ large₂ : GL (Fin n) ℂ, LowUni large₂.val → s *ᵥ (R large₂ *ᵥ v) ∈ P := by
    intro s hs large₂ hL
    have comm : ∀ g y, R g *ᵥ (s *ᵥ y) = s *ᵥ (R g *ᵥ y) := by
      intro g y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS s hs]
    have key : ∀ t, f (s *ᵥ (R large₂ *ᵥ v)) t = s *ᵥ (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
      intro t
      have e2 : dd c t * large₂ = (dd c t * large₂ * (dd c t)⁻¹) * dd c t := by group
      have inner : R (dd c t) *ᵥ (R large₂ *ᵥ v) =
          Complex.exp ((phi c lam : ℂ) * t) • (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← hmul, show R (dd c t * large₂) = R (dd c t * large₂ * (dd c t)⁻¹) * R (dd c t) by
          rw [← hmul, ← e2], ← Matrix.mulVec_mulVec, hv (dd c t) (dd_tri c t),
          char_dd, Matrix.mulVec_smul, hR]
      simp only [hf]
      rw [comm, inner, Matrix.mulVec_smul, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    have hM : Tendsto (fun t => (dd c t * large₂ * (dd c t)⁻¹).val) atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have hentry : ∀ t, (dd c t * large₂ * (dd c t)⁻¹).val i j =
          Complex.exp (((c i - c j : ℤ) : ℂ) * t) * large₂.val i j := by
        intro t
        rw [Units.val_mul, Units.val_mul, dd_val, dd_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
        rw [mul_comm (Complex.exp _) (large₂.val i j), mul_assoc, ← Complex.exp_add, mul_comm]
        congr 2; push_cast; ring
      simp only [hentry]
      rcases lt_trichotomy i j with h | h | h
      · rw [hL.1 i j h, Matrix.one_apply_ne h.ne]; simp
      · subst h; simp [hL.2]
      · rw [Matrix.one_apply_ne h.ne']
        simpa using (tendsto_exp_neg (sub_neg.2 (hc j i h))).mul_const (large₂.val i j)
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    refine ⟨s *ᵥ (Rm Q 1 *ᵥ v), ?_⟩
    rw [show f (s *ᵥ (R large₂ *ᵥ v)) = _ from funext key]
    exact (hcs.tendsto _).comp ((Rm_continuousAt Q 1 (by simp)).tendsto.comp hM)

  have hgen : ∀ s ∈ S, ∀ g : GL (Fin n) ℂ, s *ᵥ (R g *ᵥ v) ∈ P := by
    intro s hs g
    have hclosed : IsClosed (P : Set (ι → ℂ)) := Submodule.closed_of_finiteDimensional P
    have hdet : g.val.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun x : ℂ => s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v)) (𝓝[≠] 0) (𝓝 (s *ᵥ (R g *ᵥ v))) := by
      rw [hR]
      exact (hcs.tendsto _).comp ((Rm_continuousAt Q g.val hdet).tendsto.comp (tendsto_add_smul g.val))
    apply hclosed.mem_of_tendsto hlim
    filter_upwards [dense_LU g.val] with x hx
    obtain ⟨hdx, L, U, hL, hU, hLU⟩ := hx
    have hdL : L.det ≠ 0 := by rw [det_lowUni hL]; exact one_ne_zero
    have hdU : U.det ≠ 0 := by intro h; apply hdx; rw [hLU, Matrix.det_mul, h, mul_zero]
    set large₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdL
    set Ug := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdU
    have e : g.val + x • 1 = (large₂ * Ug).val := by rw [hLU]; rfl
    have hUg : Ug.val.BlockTriangular id := fun i j h => hU i j h
    show s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v) ∈ P
    rw [e, ← hR, hmul, ← Matrix.mulVec_mulVec, hv Ug hUg, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact P.smul_mem _ (hgenL s hs large₂ hL)
  have huP : u ∈ P := by
    refine Submodule.span_le.2 ?_ hmem
    rintro w ⟨s, hs, g, rfl⟩
    exact hgen s hs g
  obtain ⟨y, hy⟩ := huP
  by_contra hlt
  push Not at hlt
  have hfu : ∀ t, f u t = Complex.exp (((phi c mu - phi c lam : ℤ) : ℂ) * t) • u := by
    intro t
    simp only [hf]
    rw [hu (dd c t) (dd_tri c t), char_dd, smul_smul, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hnorm : Tendsto (fun t => ‖f u t‖) atTop atTop := by
    have e : (fun t => ‖f u t‖) = fun t => Real.exp (((phi c mu - phi c lam : ℤ) : ℝ) * t) * ‖u‖ := by
      funext t; rw [hfu, norm_smul, Complex.norm_exp]; simp
    rw [e]
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by exact_mod_cast sub_pos.2 hlt))).atTop_mul_const
      (norm_pos_iff.2 hu0)
  exact not_tendsto_atTop_of_tendsto_nhds hy.norm hnorm

theorem general_linear_reduction : GLStep := by
  intro n ι _ _ R Q hRQ hmul S hS v u lam mu hv hu hspv hspu hv0 hu0
  have memu : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} := by
    rw [hspv]; exact Submodule.mem_top
  have memv : v ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} := by
    rw [hspu]; exact Submodule.mem_top
  have key : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j < c i) → phi c mu = phi c lam := fun c hc =>
    le_antisymm (wt_le R Q hRQ hmul S hS v u lam mu hv hu memu hu0 c hc)
      (wt_le R Q hRQ hmul S hS u v mu lam hu hv memv hv0 c hc)
  funext k
  let c0 : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ)
  let ck : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ) + if i = k then 1 else 0
  have h0 := key c0 (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [c0]; omega)
  have h1 := key ck (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [ck]; split_ifs <;> omega)
  have hk : ∀ x : Fin n → ℤ, phi ck x = phi c0 x + x k := by
    intro x
    simp [phi, ck, c0, add_mul, Finset.sum_add_distrib]
  rw [hk, hk] at h1
  linarith

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
