import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.TraceSingleMulSingle

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC.Cxi

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem map_diag_ιMulti {k : ℕ} (v : Md n → ℂ) (e : Fin k → Md n) :
    ExteriorAlgebra.map (Matrix.toLin' (diagonal v)) (ExteriorAlgebra.ιMulti ℂ k fun i => Pi.single (e i) (1 : ℂ)) =
      (∏ i, v (e i)) • ExteriorAlgebra.ιMulti ℂ k fun i => Pi.single (e i) (1 : ℂ) := by
  rw [ExteriorAlgebra.map_apply_ιMulti]
  have h : (⇑(Matrix.toLin' (diagonal v)) ∘ fun i => Pi.single (e i) (1 : ℂ)) =
      fun i => v (e i) • Pi.single (e i) (1 : ℂ) := by
    funext i
    ext j
    simp [Matrix.toLin'_apply, Pi.single_apply, diagonal_apply]
  rw [h, AlternatingMap.map_smul_univ]

private theorem exteriorAlgebra_map_diagonal_ιMulti_eq_prod_smul (v : Md n → ℂ) {k : ℕ} (s : Set.powersetCard (Md n) k) :
    ExteriorAlgebra.map (Matrix.toLin' (diagonal v))
        (ExteriorAlgebra.ιMulti_family ℂ k (Pi.basisFun ℂ (Md n)) s) =
      (∏ m ∈ s.val, v m) • ExteriorAlgebra.ιMulti_family ℂ k (Pi.basisFun ℂ (Md n)) s := by
  have hb : (⇑(Pi.basisFun ℂ (Md n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) =
      fun i => Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s i) (1 : ℂ) := by
    funext i
    simp
  have hs : s.val = Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding := by
    ext m
    have := Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s m
    simp only [Set.mem_range] at this
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding, this]
    first
      | rfl
      | exact Iff.rfl
  have hp : ∏ i, v (Set.powersetCard.ofFinEmbEquiv.symm s i) = ∏ m ∈ s.val, v m := by
    rw [hs, Finset.prod_map]
    rfl
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [hb, map_diag_ιMulti, hp]

theorem gam_diag (v : Md n → ℂ) : gamM (diagonal v) = diagonal fun A : Finset (Md n) => ∏ m ∈ A, v m := by
  have key : ∀ B : Finset (Md n),
      ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B) = (∏ m ∈ B, v m) • fb n B := by
    intro B
    have h1 : fb n B = ExteriorAlgebra.ιMulti_family ℂ B.card (Pi.basisFun ℂ (Md n))
        (Set.powersetCard.ofCard (s := B) rfl) := ExteriorAlgebra.basis_apply _ B
    rw [h1]
    exact exteriorAlgebra_map_diagonal_ιMulti_eq_prod_smul v _
  ext A B
  change (LinearMap.toMatrix (fb n) (fb n)
    (ExteriorAlgebra.map (toLin' (diagonal v))).toLinearMap) A B = _
  rw [LinearMap.toMatrix_apply]
  change (fb n).repr (ExteriorAlgebra.map (toLin' (diagonal v)) (fb n B)) A = _
  rw [key, map_smul, Module.Basis.repr_self, diagonal_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h2
  · subst h1
    rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

theorem trace_gam_diag (v : Md n → ℂ) : (gamM (diagonal v)).trace = ∏ m, (1 + v m) := by
  rw [gam_diag, trace_diagonal, Finset.prod_one_add, Finset.powerset_univ]

end PositivityTheory.RgBcC.Cxi
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC.Cxi

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem hbM_herm (m : Md n) : (hbM m).IsHermitian := (hbOrtho n).2 m

private theorem trace_single_mul_single_eq_ite (a b c d : Fin n) :
    (single a b (1 : ℂ) * single c d (1 : ℂ)).trace = if b = c ∧ a = d then 1 else 0 := by
  by_cases h : b = c
  · subst h
    rw [single_mul_single_same, one_mul]
    by_cases h' : a = d
    · subst h'
      simp [trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne, h']
  · rw [single_mul_single_of_ne (h := h)]
    simp [h]

private theorem trace_hb_mul_hb_eq_ite (p q : Fin n × Fin n) : (hb p * hb q).trace = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have hs : ((↑√2 : ℂ))⁻¹ * (↑√2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [hb, Prod.mk.injEq]
  split_ifs <;>
    (try simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, trace_single_mul_single_eq_ite, smul_eq_mul]) <;>
    (try split_ifs) <;>
    (try simp only [Fin.ext_iff, Fin.lt_def, not_and, not_lt] at *) <;>
    first
    | omega
    | ring1
    | linear_combination 2 * hs
    | linear_combination 2 * hs - 2 * (↑√2 : ℂ)⁻¹ * (↑√2 : ℂ)⁻¹ * Complex.I_sq

private theorem trace_hbM_mul_hbM_eq_ite (p q : Md n) : (hbM p * hbM q).trace = if p = q then 1 else 0 := by
  simp only [hbM, trace_hb_mul_hb_eq_ite, EmbeddingLike.apply_eq_iff_eq]

theorem hbM_li : LinearIndependent ℂ (hbM (n := n)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (fun X => (X * hbM i).trace) hg
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Matrix.zero_mul,
    Matrix.trace_zero, smul_eq_mul, trace_hbM_mul_hbM_eq_ite, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_ite_eq'] at h
  simpa [hi] using h

def hbB (n : ℕ) [Nonempty (Md n)] : Module.Basis (Md n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank hbM_li (by simp [Module.finrank_matrix])

theorem hbB_apply [Nonempty (Md n)] (m : Md n) : hbB n m = hbM m := by
  rw [hbB, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem hbB_repr [Nonempty (Md n)] (X : Mat n) (m : Md n) : (hbB n).repr X m = (X * hbM m).trace := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, hbB_apply, trace_hbM_mul_hbM_eq_ite,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def phiL (y : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := y * X * yᴴ
  map_add' X X' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem Mt_eq_toMatrix [Nonempty (Md n)] (y : Mat n) : Mt y = LinearMap.toMatrix (hbB n) (hbB n) (phiL y) := by
  ext p q
  rw [LinearMap.toMatrix_apply]
  have hH : (y * hbM q * yᴴ).IsHermitian := by
    simp only [IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hbM_herm q).eq,
      Matrix.mul_assoc]
  have hr : star (y * hbM q * yᴴ * hbM p).trace = (y * hbM q * yᴴ * hbM p).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, (hbM_herm p).eq, Matrix.trace_mul_comm]
  show (((y * hbM q * yᴴ * hbM p).trace.re : ℂ)) = (hbB n).repr (phiL y (hbB n q)) p
  rw [hbB_apply, hbB_repr]
  exact Complex.conj_eq_iff_re.1 hr

def stdB (n : ℕ) : Module.Basis (Md n) ℂ (Mat n) := (Matrix.stdBasis ℂ (Fin n) (Fin n)).reindex finProdFinEquiv

theorem stdB_apply (m : Md n) : stdB n m = single (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 1 := by
  simp [stdB, Matrix.stdBasis_eq_single]

theorem phiL_single (w : Fin n → ℂ) (i j : Fin n) :
    phiL (diagonal w) (single i j (1 : ℂ)) = (w i * conj (w j)) • single i j (1 : ℂ) := by
  ext a b
  simp only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, Pi.star_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [mul_one]
    rfl
  · simp

theorem phiL_stdB (w : Fin n → ℂ) (m : Md n) :
    phiL (diagonal w) (stdB n m) = (w (finProdFinEquiv.symm m).1 * conj (w (finProdFinEquiv.symm m).2)) • stdB n m := by
  rw [stdB_apply, phiL_single]

theorem toMatrix_stdB (w : Fin n → ℂ) : LinearMap.toMatrix (stdB n) (stdB n) (phiL (diagonal w)) =
    diagonal fun m => w (finProdFinEquiv.symm m).1 * conj (w (finProdFinEquiv.symm m).2) := by
  ext p q
  rw [LinearMap.toMatrix_apply, phiL_stdB, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    diagonal_apply]
  by_cases h : q = p
  · subst h; simp
  · simp [h, Ne.symm h]

end PositivityTheory.RgBcC.Cxi
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxi

private theorem gamM_mul' {n : ℕ} (A B : Matrix (Md n) (Md n) ℂ) :
    gamM (A * B) = gamM A * gamM B := by
  unfold gamM
  rw [Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]
  show LinearMap.toMatrix (fb n) (fb n)
      ((ExteriorAlgebra.map (toLin' A)).comp (ExteriorAlgebra.map (toLin' B))).toLinearMap =
    LinearMap.toMatrix (fb n) (fb n) (ExteriorAlgebra.map (toLin' A)).toLinearMap *
      LinearMap.toMatrix (fb n) (fb n) (ExteriorAlgebra.map (toLin' B)).toLinearMap
  rw [AlgHom.comp_toLinearMap]
  exact LinearMap.toMatrix_comp (fb n) (fb n) (fb n) _ _

private theorem gamM_one' {n : ℕ} : gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 := by
  unfold gamM
  rw [Matrix.toLin'_one, ExteriorAlgebra.map_id]
  exact LinearMap.toMatrix_id _

private theorem trace_gamM_conj_eq_of_mul_eq_one {n : ℕ} (A P Q : Matrix (Md n) (Md n) ℂ) (h : Q * P = 1) :
    (gamM (P * A * Q)).trace = (gamM A).trace := by
  rw [gamM_mul', gamM_mul', Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← gamM_mul', h,
    gamM_one', Matrix.one_mul]

theorem gamTrace : GamTrace := by
  intro n z hz
  have hz0 : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  have hinv : (diagonal z)⁻¹ = diagonal (fun a => (z a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hz0 a)
  have hc : ∀ a, conj (z a) = (z a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
    norm_num
  rw [hinv]
  rcases isEmpty_or_nonempty (Md n) with hn | hn
  · have h0 : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · exact (hn.false ⟨0, Nat.mul_pos h h⟩).elim
    subst h0
    have hM : (Mt (diagonal fun a => (z a)⁻¹))ᵀ = diagonal (fun _ => (0 : ℂ)) := by
      ext i
      exact hn.elim i
    rw [hM, Cxi.trace_gam_diag]
    simp
  · rw [Mt_eq_toMatrix,
      ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (hbB n) (stdB n) (hbB n) (stdB n),
      toMatrix_stdB, Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose,
      ← Matrix.mul_assoc,
      trace_gamM_conj_eq_of_mul_eq_one _ _ _ (by rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
        Matrix.transpose_one]),
      Cxi.trace_gam_diag,
      Fintype.prod_equiv finProdFinEquiv.symm _
        (fun p : Fin n × Fin n => 1 + (z p.1)⁻¹ * conj ((z p.2)⁻¹)) (fun m => rfl),
      Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
    rw [map_inv₀, hc, inv_inv]
    ring

end PositivityTheory.RgBcC
end
end
