import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.AvgData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.ColumnElementGluing

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Glue

private theorem blkAt_apply_lemma {a r : ℕ} (y : Fin (a + r)) :
    finSumFinEquiv.symm y =
      if hy : (y : ℕ) < a then Sum.inl ⟨y, hy⟩ else Sum.inr ⟨y - a, by have := y.2; omega⟩ := by
  refine Fin.addCases (fun p => ?_) (fun q => ?_) y <;> simp

theorem blkAt_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j =
      if hij : (i : ℕ) < n ∧ (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin N) (Fin N) k) i j := by
  simp only [blkAt, glCongr, blkGL, blkHom]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  rw [blkAt_apply_lemma, blkAt_apply_lemma]
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;>
    simp [hi, hj, Matrix.one_apply, Fin.ext_iff]
  · omega
  · omega
  · have e : ((i : ℕ) - n = (j : ℕ) - n) ↔ (i : ℕ) = j := by omega
    simp only [e]

theorem unip_apply (n : ℕ) (x : Multiplicative (Fin n → k)) (i j : Fin (n + 1)) :
    (unip k n x : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j +
        if hij : (j : ℕ) = n ∧ (i : ℕ) < n then x.toAdd ⟨i, hij.2⟩ else 0 := by
  show (1 + colMat k n (Multiplicative.toAdd x)) i j = _
  simp only [Matrix.add_apply, colMat]
  congr 1
  by_cases hj : (j : ℕ) = n
  · have e : j = Fin.last n := Fin.ext hj
    subst e
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp
  · have e : j ≠ Fin.last n := fun e => hj (by rw [e]; simp)
    simp [e, hj]

theorem glEmb_apply (n : ℕ) (g : GL (Fin n) k) (i j : Fin (n + 1)) :
    (glEmb k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      if hij : (i : ℕ) < n ∧ (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j = _
  simp only [glEmbMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.ext_iff]
  · have := j'.2
    omega
  · have := i'.2
    omega

def padV {m N : ℕ} (_h : m + 2 ≤ N) (x : Fin (m + 1) → k) : Fin N → k :=
  fun i => if hi : (i : ℕ) < m + 1 then x ⟨i, hi⟩ else 0

def cIdx {m N : ℕ} (h : m + 2 ≤ N) : Fin N := ⟨m + 1, by omega⟩

theorem colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j =
      (1 : Matrix (Fin N) (Fin N) k) i j + if j = cIdx h then padV h x i else 0 := by
  simp only [colEl, blkAt_apply, unip_apply, padV, cIdx, Fin.ext_iff, Matrix.one_apply,
    toAdd_ofAdd]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    by_cases hc : (j : ℕ) = m + 1 <;> by_cases hi' : (i : ℕ) < m + 1 <;>
    simp [hi, hj, hc, hi'] <;> omega

theorem colEl_add' {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

theorem colEl_zero' {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp [colEl]

theorem det_unip' (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one (fun i _ => ?_)
    rw [unip_apply]
    simp only [Matrix.one_apply_eq, add_eq_left]
    rw [dif_neg]
    omega
  · intro i j hij
    have hij' : j < i := hij
    rw [unip_apply, Matrix.one_apply_ne (ne_of_lt hij').symm, zero_add, dif_neg]
    intro hc
    have := Fin.lt_def.mp hij'
    omega

theorem det_glEmb' (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).det = _
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp [glEmbMat, Fin.succAbove_last]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, glEmbMat, Fin.lastCases_castSucc]

theorem blkAt_glEmb' {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  ext i j
  simp only [blkAt_apply, glEmb_apply, Matrix.one_apply, Fin.ext_iff]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    by_cases hi' : (i : ℕ) < m + 1 <;> by_cases hj' : (j : ℕ) < m + 1 <;>
    simp [hi, hj, hi', hj'] <;> omega

theorem colEl_inv {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    (colEl k m N h x)⁻¹ = colEl k m N h (-x) := by
  exact (eq_inv_of_mul_eq_one_left (by rw [← colEl_add', neg_add_cancel, colEl_zero'])).symm

theorem padV_neg {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : padV h (-x) = -padV h x := by
  funext i
  simp only [padV, Pi.neg_apply]
  split_ifs <;> simp

theorem padV_of_ge {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i : Fin N) (hi : m + 1 ≤ (i : ℕ)) :
    padV h x i = 0 := by
  simp only [padV]
  rw [dif_neg (by omega)]

theorem continuous_blkAt_apply (n N : ℕ) (h : n ≤ N) (i j : Fin N) :
    Continuous fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j := by
  simp only [blkAt_apply]
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp only [dif_pos hij]
    exact Units.continuous_val.matrix_elem _ _
  · simp only [dif_neg hij]
    exact continuous_const

theorem continuous_blkAt' (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  rw [Units.continuous_iff]
  have hc : Continuous fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k) :=
    continuous_pi fun i => continuous_pi fun j => continuous_blkAt_apply n N h i j
  refine ⟨hc, ?_⟩
  have e : (fun g : GL (Fin n) k => ((blkAt k n N h g)⁻¹ : GL (Fin N) k).val) =
      (fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k)) ∘ (fun g => g⁻¹) := by
    funext g
    simp [map_inv]
  rw [e]
  exact hc.comp continuous_inv

theorem continuous_colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (i j : Fin N) :
    Continuous fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j := by
  simp only [colEl_apply]
  refine continuous_const.add ?_
  by_cases hj : j = cIdx h
  · simp only [hj, if_true, padV]
    by_cases hi : (i : ℕ) < m + 1
    · simp only [dif_pos hi]
      exact continuous_apply _
    · simp only [dif_neg hi]
      exact continuous_const
  · simp only [hj, if_false]
    exact continuous_const

theorem continuous_colEl' {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  rw [Units.continuous_iff]
  have hc : Continuous fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k) :=
    continuous_pi fun i => continuous_pi fun j => continuous_colEl_apply h i j
  refine ⟨hc, ?_⟩
  have e : (fun x : Fin (m + 1) → k => ((colEl k m N h x)⁻¹ : GL (Fin N) k).val) =
      (fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k)) ∘ (fun x => -x) := by
    funext x
    simp [colEl_inv]
  rw [e]
  exact hc.comp continuous_neg

theorem mem_derUnip_iff {N n : ℕ} (u : GL (Fin N) k) : u ∈ derUnip k N n ↔
    ((∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (u : Matrix (Fin N) (Fin N) k) i i = 1) ∧
      ∀ i j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [derUnip, Subgroup.mem_inf, GlobalTheory.SmGL.mem_unipB]
  apply and_congr Iff.rfl
  show (∀ j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single j 1 = Pi.single j 1) ↔ _
  constructor
  · intro H i j hj
    have := congrFun (H j hj) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, Matrix.col] using this
  · intro H j hj
    funext i
    rw [Matrix.mulVec_single_one]
    simp [Matrix.col, H i j hj, Matrix.one_apply, Pi.single_apply]

theorem derUnip_anti {N n n' : ℕ} (hn : n ≤ n') : derUnip k N n' ≤ derUnip k N n := by
  intro u hu
  rw [mem_derUnip_iff] at hu ⊢
  exact ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩

theorem colEl_mem_derUnip' {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    colEl k m N h x ∈ derUnip k N (m + 1) := by
  rw [mem_derUnip_iff]
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => ?_⟩
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp

theorem lvlChar_apply (ψ : AddChar k Circle) (N n : ℕ) (u : derUnip k N n) :
    lvlChar k ψ N n u = Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n - 1 ≤ (p.1 : ℕ),
      (u : GL (Fin N) k).val p.1 p.2)) := rfl

theorem lvlChar_colEl' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    lvlChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip' h x⟩ = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) := by
  rw [lvlChar_apply]
  congr 2
  rw [Finset.sum_eq_single ((⟨m, by omega⟩, ⟨m + 1, by omega⟩) : Fin N × Fin N)]
  · simp [colEl_apply, cIdx, padV, xi0, Matrix.one_apply, Fin.ext_iff]
    rfl
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hp hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and] at hne
    simp only [colEl_apply, cIdx, padV, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro hnot
    exfalso
    apply hnot
    simp

theorem glEmbMat_mul_colMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k) :
    glEmbMat k n A * colMat k n x = colMat k n (A *ᵥ x) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mulVec, dotProduct]

theorem colMat_mul_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (y : Fin n → k) :
    colMat k n y * glEmbMat k n A = colMat k n y := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp

theorem glEmb_mul_unip (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    glEmb k n g * unip k n (Multiplicative.ofAdd x) =
      unip k n (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k) *ᵥ x)) * glEmb k n g := by
  apply Units.ext
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) *
      (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd x))) =
    (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k) *ᵥ x)))) *
      glEmbMat k n (g : Matrix (Fin n) (Fin n) k)
  simp only [toAdd_ofAdd, mul_add, add_mul, mul_one, one_mul, glEmbMat_mul_colMat, colMat_mul_glEmbMat]

theorem blkAt_conj_colEl' {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x * (blkAt k (m + 1) N (by omega) g)⁻¹ =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
  rw [← blkAt_glEmb' h g]
  simp only [colEl]
  rw [← map_mul, ← map_inv, ← map_mul, glEmb_mul_unip, mul_inv_cancel_right]

theorem scalAt_conj_colEl' {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x * (scalAt k (m + 1) N (by omega) z)⁻¹ =
      colEl k m N h ((z : k) • x) := by
  simp only [scalAt]
  rw [blkAt_conj_colEl']
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.algebraMap_matrix_apply]

theorem scalAt_comm_blkAt' {m N : ℕ} (h : m + 1 ≤ N) (z : kˣ) (g : GL (Fin (m + 1)) k) :
    scalAt k (m + 1) N h z * blkAt k (m + 1) N h g = blkAt k (m + 1) N h g * scalAt k (m + 1) N h z := by
  simp only [scalAt]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.commutes _ _

theorem colEl_mul_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k)
    (i j : Fin N) : ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j = M i j + padV h x i * M (cIdx h) j := by
  simp [Matrix.mul_apply, colEl_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

theorem mul_colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k)
    (i j : Fin N) : (M * (colEl k m N h x : Matrix (Fin N) (Fin N) k)) i j =
      M i j + if j = cIdx h then (M *ᵥ padV h x) i else 0 := by
  simp only [Matrix.mul_apply, colEl_apply, mul_add, Finset.sum_add_distrib]
  rw [← Matrix.mul_apply, Matrix.mul_one]
  congr 1
  split_ifs <;> simp [Matrix.mulVec, dotProduct]

theorem lvlChar_succ (ψ : AddChar k Circle) {N m : ℕ} (u : GL (Fin N) k) (hu : u ∈ derUnip k N (m + 2))
    (hu' : u ∈ derUnip k N (m + 1)) : lvlChar k ψ N (m + 1) ⟨u, hu'⟩ = lvlChar k ψ N (m + 2) ⟨u, hu⟩ := by
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  have B := (mem_derUnip_iff u).mp hu
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    omega
  · intro p hp hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hnp
    have h2 : (p.2 : ℕ) < m + 2 := by omega
    show (u : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
    rw [B.2 p.1 p.2 h2, Matrix.one_apply_ne]
    intro e
    rw [e] at hp
    omega

theorem derUnip_decomp' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (u : derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : derUnip k N (m + 2)), (u : GL (Fin N) k) = colEl k m N h x * u' ∧
      lvlChar k ψ N (m + 1) u = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) * lvlChar k ψ N (m + 2) u' := by
  obtain ⟨u, hu⟩ := u
  have B := (mem_derUnip_iff u).mp hu
  obtain ⟨x, hxd⟩ : ∃ x : Fin (m + 1) → k, ∀ i : Fin (m + 1),
      x i = (u : Matrix (Fin N) (Fin N) k) ⟨i, by have := i.2; omega⟩ (cIdx h) := ⟨_, fun _ => rfl⟩
  have hv1 : colEl k m N h (-x) * u ∈ derUnip k N (m + 1) :=
    Subgroup.mul_mem _ (colEl_mem_derUnip' h (-x)) hu
  have hv2 : colEl k m N h (-x) * u ∈ derUnip k N (m + 2) := by
    have A := (mem_derUnip_iff _).mp hv1
    rw [mem_derUnip_iff]
    refine ⟨A.1, fun i j hj => ?_⟩
    by_cases hjm : (j : ℕ) < m + 1
    · exact A.2 i j hjm
    · have hjc : j = cIdx h := Fin.ext (by simp only [cIdx]; omega)
      subst hjc
      rw [Units.val_mul, colEl_mul_apply, B.1.2 (cIdx h), mul_one]
      by_cases hi : (i : ℕ) < m + 1
      · have hne : i ≠ cIdx h := fun e => by rw [e] at hi; simp [cIdx] at hi
        rw [Matrix.one_apply_ne hne]
        simp only [padV, dif_pos hi, Pi.neg_apply, hxd]
        simp
      · rw [padV_of_ge h _ i (by omega), add_zero]
        by_cases hie : (i : ℕ) = m + 1
        · have e : i = cIdx h := Fin.ext (by simp [cIdx, hie])
          rw [e, B.1.2, Matrix.one_apply_eq]
        · have hlt : ((cIdx h : Fin N) : ℕ) < i := by simp only [cIdx]; omega
          rw [B.1.1 i (cIdx h) hlt, Matrix.one_apply_ne]
          intro e
          apply hie
          rw [e]
          rfl
  have hu_eq : u = colEl k m N h x * (colEl k m N h (-x) * u) := by
    rw [← colEl_inv, mul_inv_cancel_left]
  refine ⟨x, ⟨_, hv2⟩, hu_eq, ?_⟩
  have e : (⟨u, hu⟩ : derUnip k N (m + 1)) =
      ⟨colEl k m N h x, colEl_mem_derUnip' h x⟩ * ⟨_, hv1⟩ := Subtype.ext hu_eq
  rw [e, map_mul, lvlChar_colEl', lvlChar_succ ψ _ hv2 hv1]

theorem colEl_conj_derUnip' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k)
    (u' : derUnip k N (m + 2)) :
    ∃ hm : colEl k m N h x * (u' : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hm⟩ = lvlChar k ψ N (m + 2) u' := by
  obtain ⟨u, hu⟩ := u'
  have B := (mem_derUnip_iff u).mp hu
  have hu1 : u ∈ derUnip k N (m + 1) := derUnip_anti (by omega) hu
  have hcne : ∀ l : Fin N, (l : ℕ) < m + 1 → cIdx h ≠ l := fun l hl e => by
    have := congrArg Fin.val e
    simp only [cIdx] at this
    omega
  have hA : ∀ i l : Fin N, (l : ℕ) < m + 2 →
      ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i l =
        (1 : Matrix (Fin N) (Fin N) k) i l + padV h x i * (1 : Matrix (Fin N) (Fin N) k) (cIdx h) l := by
    intro i l hl
    rw [Units.val_mul, colEl_mul_apply, B.2 i l hl, B.2 (cIdx h) l hl]
  have hmv : ∀ i, (((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ padV h (-x)) i =
      padV h (-x) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hi : (i : ℕ) < m + 1
      · rw [hA i i (by omega), Matrix.one_apply_eq, Matrix.one_apply_ne (hcne i hi), mul_zero, add_zero,
          one_mul]
      · rw [padV_of_ge h _ i (by omega), mul_zero]
    · intro l _ hli
      by_cases hl : (l : ℕ) < m + 1
      · rw [hA i l (by omega), Matrix.one_apply_ne (Ne.symm hli), Matrix.one_apply_ne (hcne l hl), mul_zero,
          add_zero, zero_mul]
      · rw [padV_of_ge h _ l (by omega), mul_zero]
    · simp
  have hv : ∀ i j : Fin N,
      ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
        ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j +
          if j = cIdx h then padV h (-x) i else 0 := by
    intro i j
    rw [colEl_inv, Units.val_mul, mul_colEl_apply, hmv]
  have hmem : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2) := by
    have hv1 : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 1) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_derUnip' h x) hu1)
        (Subgroup.inv_mem _ (colEl_mem_derUnip' h x))
    have A := (mem_derUnip_iff _).mp hv1
    rw [mem_derUnip_iff]
    refine ⟨A.1, fun i j hj => ?_⟩
    rw [hv i j, hA i j hj]
    by_cases hjc : j = cIdx h
    · subst hjc
      rw [if_pos rfl, Matrix.one_apply_eq, mul_one, padV_neg, Pi.neg_apply, add_neg_cancel_right]
    · rw [if_neg hjc, Matrix.one_apply_ne (fun e => hjc e.symm), mul_zero, add_zero, add_zero]
  refine ⟨hmem, ?_⟩
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  show ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 =
    (u : Matrix (Fin N) (Fin N) k) p.1 p.2
  have hpc : p.2 ≠ cIdx h := fun e => by
    have := congrArg Fin.val e
    simp only [cIdx] at this
    omega
  rw [hv, if_neg hpc, add_zero, Units.val_mul, colEl_mul_apply, padV_of_ge h _ _ (by omega), zero_mul,
    add_zero]

end Glue

open Glue

theorem colEl_add {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  exact Glue.colEl_add' h x y

theorem colEl_zero {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  exact Glue.colEl_zero' h

theorem continuous_colEl {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  exact Glue.continuous_colEl' h

theorem continuous_blkAt (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  exact Glue.continuous_blkAt' n N h

theorem blkAt_glEmb {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  exact Glue.blkAt_glEmb' h g

theorem det_glEmb (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  exact Glue.det_glEmb' n g

theorem det_unip (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  exact Glue.det_unip' n x

theorem blkAt_conj_colEl {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x * (blkAt k (m + 1) N (by omega) g)⁻¹ =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
  exact Glue.blkAt_conj_colEl' h g x

theorem scalAt_conj_colEl {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x * (scalAt k (m + 1) N (by omega) z)⁻¹ =
      colEl k m N h ((z : k) • x) := by
  exact Glue.scalAt_conj_colEl' h z x

theorem colEl_mem_derUnip {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ derUnip k N (m + 1) := by
  exact Glue.colEl_mem_derUnip' h x

theorem lvlChar_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    lvlChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) := by
  exact Glue.lvlChar_colEl' ψ h x

theorem derUnip_decomp (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (u : derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : derUnip k N (m + 2)), (u : GL (Fin N) k) = colEl k m N h x * u' ∧
      lvlChar k ψ N (m + 1) u = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) * lvlChar k ψ N (m + 2) u' := by
  exact Glue.derUnip_decomp' ψ h u

theorem colEl_conj_derUnip (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k)
    (u' : derUnip k N (m + 2)) :
    ∃ hm : colEl k m N h x * (u' : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hm⟩ = lvlChar k ψ N (m + 2) u' := by
  exact Glue.colEl_conj_derUnip' ψ h x u'

theorem scalAt_comm_blkAt {m N : ℕ} (h : m + 1 ≤ N) (z : kˣ) (g : GL (Fin (m + 1)) k) :
    scalAt k (m + 1) N h z * blkAt k (m + 1) N h g = blkAt k (m + 1) N h g * scalAt k (m + 1) N h z := by
  exact Glue.scalAt_comm_blkAt' h z g

end PositivityTheory.RgUd.Form.ColumnElementGluing
end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir MeasureTheory

namespace PositivityTheory.RgUd.Form.ColumnElementGluing

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
variable (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin N) k) V)

theorem conj_circle_mul_self (z : Circle) : starRingEnd ℂ (z : ℂ) * (z : ℂ) = 1 := by
  rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

theorem sum_translate_transversal {X W : Type} [AddCommGroup X] [AddCommMonoid W] (A M : AddSubgroup X)
    (T : Finset X) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ M) (F : X → W)
    (hF : ∀ a, ∀ d ∈ M, F (a + d) = F a) (y : X) (hy : y ∈ A) :
    ∑ t ∈ T, F (t + y) = ∑ t ∈ T, F t := by
  classical
  have hσ : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + y) - s ∈ M := fun t ht => (hu _ (A.add_mem (hT t ht) hy)).exists
  have hτ : ∀ s ∈ T, ∃ t, t ∈ T ∧ (s - y) - t ∈ M := fun s hs => (hu _ (A.sub_mem (hT s hs) hy)).exists
  choose! σ hσT hσM using hσ
  choose! τ hτT hτM using hτ
  refine Finset.sum_nbij' σ τ hσT hτT ?_ ?_ ?_
  · intro t ht
    have hs := hσT t ht
    refine (hu _ (A.sub_mem (hT _ hs) hy)).unique ⟨hτT _ hs, hτM _ hs⟩ ⟨ht, ?_⟩
    have e : σ t - y - t = -((t + y) - σ t) := by abel
    rw [e]; exact M.neg_mem (hσM t ht)
  · intro s hs
    have ht := hτT s hs
    refine (hu _ (A.add_mem (hT _ ht) hy)).unique ⟨hσT _ ht, hσM _ ht⟩ ⟨hs, ?_⟩
    have e : τ s + y - s = -((s - y) - τ s) := by abel
    rw [e]; exact M.neg_mem (hτM s hs)
  · intro t ht
    have := hF (σ t) _ (hσM t ht)
    rw [← this]; congr 1; abel

def avgSub (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) :
    AddSubgroup (Fin (m + 1) → k) where
  carrier := {a | a ∈ A ∧ π (colEl k m N h a) v = v ∧ ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := ⟨A.zero_mem, by rw [colEl_zero, map_one, Module.End.one_apply], by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
    refine ⟨A.add_mem ha hb, ?_, ?_⟩
    · rw [colEl_add, map_mul, Module.End.mul_apply, hb', ha']
    · rw [dotProduct_add, AddChar.map_add_eq_mul, ha'', hb'', one_mul]
  neg_mem' := by
    rintro a ⟨ha, ha', ha''⟩
    refine ⟨A.neg_mem ha, ?_, ?_⟩
    · have e := colEl_add h (-a) a
      rw [neg_add_cancel, colEl_zero] at e
      conv_lhs => rw [← ha']
      rw [← Module.End.mul_apply, ← map_mul, ← e, map_one, Module.End.one_apply]
    · rw [dotProduct_neg, AddChar.map_neg_eq_inv, ha'', inv_one]

theorem avgData_exists (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) : ∃ p, AvgData ψ h π ξ A v p := by
  classical
  set M := avgSub ψ h π ξ A v with hMdef
  have hMA : M ≤ A := fun a ha => ha.1
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hdot : Continuous fun a : Fin (m + 1) → k => ξ ⬝ᵥ a := by unfold dotProduct; fun_prop
  have h1 : (A : Set (Fin (m + 1) → k)) ∈ nhds 0 := hA.2.mem_nhds A.zero_mem
  have h2 : colEl k m N h ⁻¹' {g | π g v = v} ∈ nhds 0 :=
    ((hπ v).preimage (continuous_colEl h)).mem_nhds (by simp [colEl_zero])
  have h3 : (fun a : Fin (m + 1) → k => ξ ⬝ᵥ a) ⁻¹' {y | ValuativeRel.valuation k y < γ} ∈ nhds 0 := by
    apply hdot.continuousAt.preimage_mem_nhds
    simpa using (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  have hMo : IsOpen (M : Set (Fin (m + 1) → k)) := by
    refine M.isOpen_of_mem_nhds (g := 0) ?_
    filter_upwards [h1, h2, h3] with a ha1 ha2 ha3
    exact ⟨ha1, ha2, hball _ ha3⟩
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA.1
  set M' := M.addSubgroupOf A
  have hM'o : IsOpen (M' : Set A) := hMo.preimage continuous_subtype_val
  have : Finite (A ⧸ M') := AddSubgroup.quotient_finite_of_isOpen M' hM'o
  have := Fintype.ofFinite (A ⧸ M')
  refine ⟨⟨M, Finset.univ.image (fun q : A ⧸ M' => ((Quotient.out q : A) : Fin (m + 1) → k))⟩,
    hMA, hMo, fun a ha => ha.2.1, fun a ha => ha.2.2, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨q, _, rfl⟩ := ht
    exact (Quotient.out q).2
  · intro a ha
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨a, ha⟩ : A ⧸ M') : A) : Fin (m + 1) → k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have e := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨a, ha⟩ : A ⧸ M')
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e
      simpa [sub_eq_neg_add] using e
    · rintro t ⟨ht, hat⟩
      simp only [Finset.mem_image] at ht
      obtain ⟨q, _, rfl⟩ := ht
      congr 2
      rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simpa [sub_eq_neg_add] using hat

theorem avg_spec (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) : ∃ p, AvgData ψ h π ξ A v p ∧ avg ψ h π ξ A v =
      ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  have hd : ∃ p, AvgData ψ h π ξ A v p := avgData_exists ψ h π hψ hπ ξ A hA v
  refine ⟨hd.choose, hd.choose_spec, ?_⟩
  rw [avg, dif_pos hd]

theorem avg_eigen (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) (y : Fin (m + 1) → k) (hy : y ∈ A) :
    π (colEl k m N h y) (avg ψ h π ξ A v) = ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • avg ψ h π ξ A v := by
  obtain ⟨p, ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  have hF : ∀ a, ∀ d ∈ p.1, (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) (a + d) =
      (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) a := by
    intro a d hd
    simp only
    rw [colEl_add, map_mul, Module.End.mul_apply, hMfix d hd, dotProduct_add, AddChar.map_add_eq_mul, hMchar d hd,
      mul_one]
  have key : ∀ t, starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h y) (π (colEl k m N h t) v) =
      ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) (t + y) := by
    intro t
    simp only
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, add_comm y t, smul_smul, dotProduct_add,
      AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    congr 1
    linear_combination (-starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * conj_circle_mul_self (ψ (ξ ⬝ᵥ y))
  rw [hav, map_smul, map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl (fun t _ => key t), ← Finset.smul_sum, smul_comm]
  congr 2
  exact sum_translate_transversal A p.1 p.2 hT hu
    (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) hF y hy

theorem sub_avg_mem (hψ : Continuous ψ) (hπ : IsSmooth π) (A : AddSubgroup (Fin (m + 1) → k)) (hA : IsLat A) (v : V) :
    v - avg ψ h π (xi0 k m) A v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) := by
  obtain ⟨p, ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩, hav⟩ := avg_spec ψ h π hψ hπ (xi0 k m) A hA v
  obtain ⟨t₀, ⟨ht₀, _⟩, _⟩ := hu 0 A.zero_mem
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht₀)
  have hv : v = (p.2.card : ℂ)⁻¹ • ∑ t ∈ p.2, v := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hav, show v - _ = (p.2.card : ℂ)⁻¹ • ∑ t ∈ p.2, (v - starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) •
      π (colEl k m N h t) v) from by rw [Finset.sum_sub_distrib, smul_sub, ← hv]]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => ?_)
  have hmem : π (colEl k m N h t) v - ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • v ∈
      twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) := by
    have := Submodule.subset_span (R := ℂ)
      (s := {w | ∃ (n : derUnip k N (m + 1)) (u : V), w = π (n : GL (Fin N) k) u - ((lvlChar k ψ N (m + 1) n : ℂˣ) : ℂ) • u})
      ⟨⟨colEl k m N h t, colEl_mem_derUnip h t⟩, v, rfl⟩
    rw [lvlChar_colEl] at this
    exact this
  have e : v - starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v =
      (-starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ)) •
        (π (colEl k m N h t) v - ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • v) := by
    rw [smul_sub, smul_smul, neg_mul, conj_circle_mul_self, neg_smul, neg_smul, one_smul]
    abel
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end

end PositivityTheory.RgUd.Form.ColumnElementGluing
end
end
