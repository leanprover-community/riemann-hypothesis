import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.CurvSubQuotTautPairGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotConn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

section Leibniz

variable {p k : Type*} [Fintype k] {M : V → Matrix p k ℂ} {v : V → k → ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem diff_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (a : p) : DifferentiableAt ℝ (fun x => (M x *ᵥ v x) a) z := by
  simp only [mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun b _ => (hM.diff a b).fun_mul (hv b)

theorem del_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (ξ : V) (a : p) : del (fun x => (M x *ᵥ v x) a) z ξ =
      (M z *ᵥ (fun b => del (fun x => v x b) z ξ) + mdel M z ξ *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [del_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [del_mul (hM.diff a b) (hv b), mdel_apply]

theorem dbar_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (η : V) (a : p) : dbar (fun x => (M x *ᵥ v x) a) z η =
      (M z *ᵥ (fun b => dbar (fun x => v x b) z η) + mdbar M z η *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [dbar_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [dbar_mul (hM.diff a b) (hv b), mdbar_apply]

end Leibniz

section Blocks

variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem orthProj_transpose_mul (hs : IsUnit (subGram H).det) :
    (orthProj H)ᵀ * subGram H = H * incl m l := by
  conv_rhs => rw [← fromBlocks_toBlocks H]
  rw [orthProj, incl, transpose_fromCols, fromRows_mul, fromBlocks_mul_fromRows]
  congr 1
  · simp [subGram]
  · rw [orthCoeff, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      subGram, Matrix.mul_assoc, nonsing_inv_mul H.toBlocks₁₁ hs]
    simp

theorem mul_orthLift_conj (hh : H.IsHermitian) (hs : IsUnit (subGram H).det) :
    H * (orthLift H)ᴴᵀ = fromRows 0 (quotGram H) := by
  have := congrArg conjTranspose (orthLift_transpose_mul hs)
  rw [conjTranspose_mul, hh.eq] at this
  rw [show (orthLift H)ᴴᵀ = (orthLift H)ᵀᴴ from rfl, this]
  ext (a | a) b <;> simp [(isHermitian_quotGram hh).apply]

end Blocks

section Frame

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem mdel_orthLift (ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (η : V) :
    mdbar (fun x => orthLift (H x)) z η = fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
  ext (a | a) b <;> simp [orthLift, dbar_neg]

theorem quotMap_mul_mdel_orthLift (ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift]; simp [quotMap, fromCols_mul_fromRows]

theorem quotMap_mul_mdbar_orthLift (η : V) :
    quotMap m l * mdbar (fun x => orthLift (H x)) z η = 0 := by
  rw [mdbar_orthLift]; simp [quotMap, fromCols_mul_fromRows]

variable (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U)
include h hs hz

theorem conn_gramS (ξ : V) : conn (gramS H) z ξ = orthProj (H z) * conn H z ξ * incl m l := by
  refine (eq_conn_of_compatible (H := gramS H) (hs z hz) ?_).symm
  have e : mdel (gramS H) z ξ = (mdel H z ξ).toBlocks₁₁ := rfl
  rw [e, ← conn_transpose_mul (h.isUnit z hz), ← incl_transpose_mul_mul, transpose_mul,
    transpose_mul]
  simp only [gramS, Matrix.mul_assoc]
  rw [orthProj_transpose_mul (hs z hz)]

theorem conn_gramQ (ξ : V) :
    conn (gramQ H) z ξ = quotMap m l * conn H z ξ * orthLift (H z) := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  refine (eq_conn_of_compatible (H := gramQ H)
    (isUnit_det_quotGram (h.isUnit z hz) hsz) ?_).symm
  have hev : gramQ H =ᶠ[𝓝 z] fun x => (orthLift (H x))ᵀ * H x * (orthLift (H x))ᴴᵀ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [gramQ, orthLift, fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      transpose_fromCols]
  have hK : (quotMap m l)ᵀ * quotGram (H z) = fromRows 0 (quotGram (H z)) := by
    simp [quotMap, transpose_fromCols, fromRows_mul]
  rw [mdel_congr hev, mdel_mul (hL.transpose.mul hH1) hL.conjTranspose.transpose,
    mdel_mul hL.transpose hH1, mdel_transpose (fun x => (orthLift (H x))ᴴ), mdel_conjTranspose,
    mdel_transpose, orthLift_transpose_mul hsz, ← conn_transpose_mul (h.isUnit z hz),
    mdbar_orthLift, mdel_orthLift]
  simp only [Matrix.add_mul, Matrix.mul_assoc, mul_orthLift_conj (h.herm z hz) hsz, transpose_mul,
    gramQ, hK]
  simp [fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    transpose_fromRows]

theorem orthProj_mul_covDel_orthLift (ξ : V) :
    orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z)) = 0 := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hev : (fun x => (orthLift (H x))ᵀ * H x * incl m l) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [incl, fromCols_mul_fromRows]
  have h1 := mdel_congr hev ξ
  rw [mdel_const, mdel_mul (hL.transpose.mul hH1) (mContDiffAt_const _), mdel_const,
    Matrix.mul_zero, zero_add, mdel_mul hL.transpose hH1, mdel_transpose,
    ← conn_transpose_mul (h.isUnit z hz)] at h1
  set X := orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z))
  have h2 : Xᵀ * subGram (H z) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, orthProj_transpose_mul hsz, transpose_add, transpose_mul,
      ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have h3 : Xᵀ = 0 := by
    rw [← Matrix.mul_nonsing_inv_cancel_right (subGram (H z)) Xᵀ hsz, h2, Matrix.zero_mul]
  rw [← transpose_transpose X, h3, transpose_zero]

end Frame

theorem connBlocks_secondForm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := by
  have hH1 := h.one hz
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hI : MContDiffAt 1 (fun _ : V => incl m l) z := mContDiffAt_const _
  intro u q hu' hq'
  have e1 : ∀ ξ, covDel H (splitSec H u q) z ξ =
      incl m l *ᵥ (fun a => del (fun x => u x a) z ξ) +
        orthLift (H z) *ᵥ (fun a => del (fun x => q x a) z ξ) +
        mdel (fun x => orthLift (H x)) z ξ *ᵥ q z +
        conn H z ξ *ᵥ (incl m l *ᵥ u z + orthLift (H z) *ᵥ q z) := by
    intro ξ
    rw [covDel]
    congr 1
    funext a
    simp only [splitSec, Pi.add_apply]
    rw [del_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      del_mulVec hI hu' ξ a, del_mulVec hL hq' ξ a]
    simp [add_assoc]
  have e2 : ∀ η, secDbar (splitSec H u q) z η =
      incl m l *ᵥ (fun a => dbar (fun x => u x a) z η) +
        orthLift (H z) *ᵥ (fun a => dbar (fun x => q x a) z η) +
        mdbar (fun x => orthLift (H x)) z η *ᵥ q z := by
    intro η
    funext a
    simp only [secDbar, splitSec, Pi.add_apply]
    rw [dbar_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      dbar_mulVec hI hu' η a, dbar_mulVec hL hq' η a]
    simp [add_assoc]
  have kP := orthProj_mul_covDel_orthLift h hs hz
  refine ⟨fun ξ => ?_, fun ξ => ?_, fun η => ?_, fun η => ?_⟩
  · have k : orthProj (H z) * mdel (fun x => orthLift (H x)) z ξ =
        -(orthProj (H z) * conn H z ξ * orthLift (H z)) := by
      rw [Matrix.mul_assoc, eq_neg_iff_add_eq_zero, ← Matrix.mul_add, kP]
    rw [e1, covDel, conn_gramS h hs hz]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, k, neg_mulVec, ← Matrix.mul_assoc]
    abel
  · rw [e1, covDel, conn_gramQ h hs hz, secondForm, blockQS]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdel_orthLift, one_mulVec, zero_mulVec, ← Matrix.mul_assoc]
    abel
  · beta_reduce
    rw [e2, ← extForm_eq_neg_secondFormAdj hH1 (h.eventually_herm hz) hu hsz, extForm]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, add_zero]
    rfl
  · rw [e2]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdbar_orthLift, one_mulVec, zero_mulVec, zero_add, add_zero]
    rfl

example : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := @connBlocks_secondForm

end GlobalTheory.SubQuotConn
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_blocks_hermitian_frame : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := by
  atlas_forward_decl GlobalTheory.SubQuotConn.connBlocks_secondForm
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubGauss

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthProj_transpose_mul_subGram (K : Matrix (m ⊕ l) (m ⊕ l) ℂ)
    (hs : IsUnit (subGram K).det) : (orthProj K)ᵀ * subGram K = K * incl m l := by
  have hc : (orthCoeff K)ᵀ = K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ := by
    simp [orthCoeff, transpose_nonsing_inv]
  rw [orthProj, transpose_fromCols, transpose_one, fromRows_mul, hc,
    subGram, nonsing_inv_mul_cancel_right K.toBlocks₁₁ _ hs]
  conv_rhs => rw [← fromBlocks_toBlocks K]
  simp [incl, fromBlocks_mul_fromRows, subGram]

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_gramS {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {x : V} (hu : IsUnit (H x).det)
    (hs : IsUnit (subGram (H x)).det) (ξ : V) :
    conn (gramS H) x ξ = orthProj (H x) * (conn H x ξ * incl m l) := by
  refine (eq_conn_of_compatible (H := gramS H) hs ?_).symm
  have e : mdel (gramS H) x ξ = (mdel H x ξ).toBlocks₁₁ := by ext a b; rfl
  rw [e, ← incl_transpose_mul_mul, ← conn_transpose_mul hu, transpose_mul, transpose_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, gramS, orthProj_transpose_mul_subGram _ hs]
  simp only [Matrix.mul_assoc]

theorem mContDiffAt_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} {k : WithTop ℕ∞}
    (h : MContDiffAt k H z) (hs : IsUnit (subGram (H z)).det) :
    MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro a (b | b)
  · simpa [orthProj] using (contDiffAt_const : ContDiffAt ℝ k (fun _ : V => (1 : Matrix m m ℂ) a b) z)
  · simpa [orthProj] using hc a b

theorem mdbar_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (η : V) :
    mdbar (fun x => orthProj (H x)) z η = secondFormAdj H z η * quotMap m l := by
  have e1 : mdbar (fun x => orthProj (H x)) z η =
      fromCols 0 (mdbar (fun x => orthCoeff (H x)) z η) := by
    ext a (b | b) <;> simp [orthProj]
  have e2 : mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
    rw [← neg_neg (mdbar _ z η), ← extForm_eq_neg_mdbar, extForm_eq_neg_secondFormAdj h hh hu hs,
      neg_neg]
  rw [e1, e2, quotMap, mul_fromCols]
  simp

theorem curv_gramS {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := by
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hθ : MContDiffAt 1 (fun x => conn H x ξ) z :=
    h2.conn (h.isUnit z hz) (by norm_num) ξ
  have hP : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj h1 (hs z hz)
  have he : (fun x => conn (gramS H) x ξ) =ᶠ[𝓝 z]
      fun x => orthProj (H x) * (conn H x ξ * incl m l) :=
    Filter.mem_of_superset hU fun x hx => conn_gramS (h.isUnit x hx) (hs x hx) ξ
  have hB : mdbar (fun x => conn H x ξ * incl m l) z η = mdbar (fun x => conn H x ξ) z η * incl m l := by
    rw [mdbar_mul hθ (mContDiffAt_const _), mdbar_const, Matrix.mul_zero, zero_add]
  rw [curv, mdbar_congr he, mdbar_mul hP (hθ.mul (mContDiffAt_const _)), hB,
    mdbar_orthProj h1 (h.eventually_herm hz) (h.isUnit z hz) (hs z hz), blockSS, curv,
    wedgeAntiHol, secondForm, blockQS]
  simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_add]

end GlobalTheory.SubGauss
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_curvature_formula : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := by
  atlas_forward_decl GlobalTheory.SubGauss.curv_gramS
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.GaussQuot

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem quotMap_conjTranspose : (quotMap m l)ᴴ = (quotMap m l)ᵀ := by
  ext (a | a) b <;> simp [quotMap, Matrix.one_apply, apply_ite]

theorem quotMap_mul_conj_orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotMap m l * (orthLift H)ᴴᵀ = 1 := by
  have h := congrArg (fun M => (Mᴴ)ᵀ) (quotMap_mul_orthLift H)
  simp only [conjTranspose_mul, transpose_mul, conjTranspose_one, transpose_one] at h
  rw [← h, quotMap_conjTranspose, transpose_transpose]

theorem orthLift_transpose_mul_eq {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hs : IsUnit (subGram H).det) :
    (orthLift H)ᵀ * H = quotGram H * quotMap m l := by
  rw [orthLift_transpose_mul hs, quotMap, mul_fromCols]; simp

theorem mul_conj_orthLift {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hh : H.IsHermitian)
    (hs : IsUnit (subGram H).det) : H * (orthLift H)ᴴᵀ = (quotMap m l)ᵀ * quotGram H := by
  have h := congrArg conjTranspose (orthLift_transpose_mul_eq hs)
  simp only [conjTranspose_mul, hh.eq, (isHermitian_quotGram hh).eq, quotMap_conjTranspose] at h
  exact h

theorem mul_mdel_eq_zero {p : Type} [Fintype p] {P : Matrix l p ℂ} {L : V → Matrix p l ℂ} {x : V}
    (hL : MContDiffAt 1 L x) (h1 : ∀ y, P * L y = 1) (ξ : V) : P * mdel L x ξ = 0 := by
  have h := mdel_mul (mContDiffAt_const P) hL ξ (z := x)
  rw [show (fun y => P * L y) = fun _ => (1 : Matrix l l ℂ) from funext h1, mdel_const,
    mdel_const, Matrix.zero_mul, add_zero] at h
  exact h.symm

theorem mul_mdbar_eq_zero {p : Type} [Fintype p] {P : Matrix l p ℂ} {L : V → Matrix p l ℂ} {x : V}
    (hL : MContDiffAt 1 L x) (h1 : ∀ y, P * L y = 1) (η : V) : P * mdbar L x η = 0 := by
  have h := mdbar_mul (mContDiffAt_const P) hL η (z := x)
  rw [show (fun y => P * L y) = fun _ => (1 : Matrix l l ℂ) from funext h1, mdbar_const,
    mdbar_const, Matrix.zero_mul, add_zero] at h
  exact h.symm

theorem conn_gramQ {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {x : V} (h1 : MContDiffAt 1 H x)
    (hh : (H x).IsHermitian) (hu : IsUnit (H x).det) (hs : IsUnit (subGram (H x)).det) (ξ : V) :
    conn (gramQ H) x ξ = quotMap m l * conn H x ξ * orthLift (H x) := by
  symm
  refine eq_conn_of_compatible (H := gramQ H) (z := x) (ξ := ξ)
    (show IsUnit (gramQ H x).det from isUnit_det_quotGram hu hs) ?_
  have hL : MContDiffAt 1 (fun y => orthLift (H y)) x := GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift h1 hs
  have hL' : MContDiffAt 1 (fun y => (orthLift (H y))ᴴᵀ) x := hL.conjTranspose.transpose
  have hev : gramQ H =ᶠ[𝓝 x] fun y => (orthLift (H y))ᵀ * H y * (orthLift (H y))ᴴᵀ := by
    filter_upwards [h1.subGram.eventually_isUnit hs] with y hy
    rw [orthLift_transpose_mul_eq hy, Matrix.mul_assoc, quotMap_mul_conj_orthLift, Matrix.mul_one]
    rfl
  have e0 : (mdel (fun y => orthLift (H y)) x ξ)ᵀ * H x * (orthLift (H x))ᴴᵀ = 0 := by
    rw [Matrix.mul_assoc, mul_conj_orthLift hh hs, ← Matrix.mul_assoc, ← transpose_mul,
      mul_mdel_eq_zero hL fun _ => quotMap_mul_orthLift _, transpose_zero, Matrix.zero_mul]
  have e2 : (orthLift (H x))ᵀ * H x * mdel (fun y => (orthLift (H y))ᴴᵀ) x ξ = 0 := by
    rw [orthLift_transpose_mul_eq hs, Matrix.mul_assoc,
      mul_mdel_eq_zero hL' fun _ => quotMap_mul_conj_orthLift _, Matrix.mul_zero]
  have e1 : mdel (gramQ H) x ξ = (orthLift (H x))ᵀ * mdel H x ξ * (orthLift (H x))ᴴᵀ := by
    rw [mdel_congr hev, mdel_mul (hL.transpose.mul h1) hL', mdel_mul hL.transpose h1, e2,
      zero_add, Matrix.add_mul, mdel_transpose, e0, add_zero]
  rw [e1, ← conn_transpose_mul hu, transpose_mul, transpose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_conj_orthLift hh hs]
  rfl

theorem curv_gramQ {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) +
      wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := by
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z :=
    (h.two hz).conn (h.isUnit z hz) (by norm_num) ξ
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.one hz) (hs z hz)
  have hev : (fun x => conn (gramQ H) x ξ) =ᶠ[𝓝 z]
      fun x => quotMap m l * conn H x ξ * orthLift (H x) := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact conn_gramQ (h.one hx) (h.herm x hx) (h.isUnit x hx) (hs x hx) ξ
  have hd : mdbar (fun x => orthLift (H x)) z η = incl m l * extForm H z η := by
    have e := congrArg (· * mdbar (fun x => orthLift (H x)) z η) (incl_mul_orthProj_add (H z))
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      mul_mdbar_eq_zero hL (fun _ => quotMap_mul_orthLift _), Matrix.mul_zero, add_zero] at e
    rw [extForm, e]
  have hb : extForm H z η = -secondFormAdj H z η :=
    extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz) (hs z hz) η
  rw [curv, mdbar_congr hev, mdbar_mul ((mContDiffAt_const _).mul hc) hL,
    mdbar_mul (mContDiffAt_const _) hc, mdbar_const, Matrix.zero_mul, add_zero, hd, hb,
    blockQQ, curv, wedgeHolAnti, secondForm, blockQS]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_add, neg_neg]
  abel

end GlobalTheory.GaussQuot
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bundle_curvature_formula : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := by
  atlas_forward_decl GlobalTheory.GaussQuot.curv_gramQ
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.CurvSQ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthLift_transpose_mul_incl {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    (orthLift T)ᵀ * T * incl m l = 0 := by
  rw [orthLift_transpose_mul hu]; simp [incl, fromCols_mul_fromRows]

theorem mul_incl_eq {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    T * incl m l = (orthProj T)ᵀ * subGram T := by
  have hu' : IsUnit T.toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  conv_lhs => rw [← fromBlocks_toBlocks T]
  rw [incl, fromBlocks_mul_fromRows, orthProj, transpose_fromCols, fromRows_mul, orthCoeff,
    transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose, subGram,
    Matrix.mul_assoc, nonsing_inv_mul _ (show IsUnit T.toBlocks₁₁.det from hu)]
  simp

theorem mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : V) :
    mdbar (fun x => orthLift (H x)) z η = incl m l * extForm H z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
    ext (a | a) b <;> simp [orthLift, dbar_neg]
  rw [extForm, h, orthProj, fromCols_mul_fromRows, incl, fromRows_mul]
  simp

theorem quotMap_mul_mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift, quotMap, fromCols_mul_fromRows]; simp

theorem mdel_orthProj_mul_incl (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthProj (H x)) z ξ * incl m l = 0 := by
  have h : mdel (fun x => orthProj (H x)) z ξ = fromCols 0 (mdel (fun x => orthCoeff (H x)) z ξ) := by
    ext a (b | b) <;> simp [orthProj]
  rw [h, incl, fromCols_mul_fromRows]; simp

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem mContDiffAt_orthProj {k : WithTop ℕ∞} {z : V} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc := GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff h hs
  rintro a (b | b)
  exacts [contDiffAt_const, hc a b]

theorem orthProj_mul_covDel_orthLift (h : IsHermFrame U H)
    (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) {x : V} (hx : x ∈ U) (ξ : V) :
    orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) = 0 := by
  have hL : MContDiffAt 1 (fun y => orthLift (H y)) x :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.one hx) (hs x hx)
  have hA : MContDiffAt 1 (fun y => (orthLift (H y))ᵀ * H y) x := hL.transpose.mul (h.one hx)
  have hB : MContDiffAt 1 (fun _ : V => incl m l) x := mContDiffAt_const _
  have e0 : mdel (fun y => (orthLift (H y))ᵀ * H y * incl m l) x ξ = 0 := by
    rw [mdel_congr (B := fun _ => (0 : Matrix l m ℂ)) (mem_of_superset (h.isOpen.mem_nhds hx)
      fun y hy => orthLift_transpose_mul_incl (hs y hy)), mdel_const]
  rw [mdel_mul hA hB, mdel_const, Matrix.mul_zero, zero_add, mdel_mul hL.transpose (h.one hx),
    mdel_transpose, ← conn_transpose_mul (h.isUnit x hx)] at e0
  have e1 : (orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ +
      conn H x ξ * orthLift (H x)))ᵀ * subGram (H x) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, ← mul_incl_eq (hs x hx), ← e0, transpose_add,
      transpose_mul]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 := congrArg (· * (subGram (H x))⁻¹) e1
  simp only [Matrix.mul_assoc, mul_nonsing_inv _ (hs x hx), Matrix.mul_one, Matrix.zero_mul] at e2
  exact transpose_eq_zero.1 e2

theorem covDel_orthLift (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
    {x : V} (hx : x ∈ U) (ξ : V) :
    mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x) =
      orthLift (H x) * blockQQ (H x) (conn H x ξ) := by
  calc _ = (incl m l * orthProj (H x) + orthLift (H x) * quotMap m l) *
        (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) := by
          rw [incl_mul_orthProj_add, Matrix.one_mul]
    _ = _ := by
      rw [Matrix.add_mul, Matrix.mul_assoc, orthProj_mul_covDel_orthLift h hs hx,
        Matrix.mul_zero, zero_add, Matrix.mul_assoc, Matrix.mul_add,
        quotMap_mul_mdel_orthLift, zero_add, blockQQ, Matrix.mul_assoc]

theorem blockSQ_curv_eq_covDelAnti_extForm {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL2 : MContDiffAt 2 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.two hz) hsz
  have hL1 : MContDiffAt 1 (fun x => orthLift (H x)) z := hL2.of_le one_le_two
  have hP1 : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj (h.one hz) hsz
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := (h.two hz).conn hu (by norm_num) ξ
  have hdL : MContDiffAt 1 (fun x => mdel (fun y => orthLift (H y)) x ξ) z :=
    hL2.mdel (by norm_num) ξ
  have hbL : MContDiffAt 1 (fun x => mdbar (fun y => orthLift (H y)) x η) z :=
    hL2.mdbar (by norm_num) η
  have hM : MContDiffAt 1 (fun x => blockQQ (H x) (conn H x ξ)) z :=
    ((mContDiffAt_const _).mul hc).mul hL1
  have he : (fun x => mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) =ᶠ[𝓝 z]
      fun x => orthLift (H x) * blockQQ (H x) (conn H x ξ) :=
    mem_of_superset (h.isOpen.mem_nhds hz) fun x hx => covDel_orthLift h hs hx ξ
  have F1 := mdbar_congr he η
  rw [mdbar_add hdL (hc.mul hL1), mdbar_mdel hL2, mdbar_mul hc hL1, mdbar_mul hL1 hM] at F1
  have cS : conn (gramS H) z ξ = blockSS (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_sub hu hsz ξ
  have cQ : conn (gramQ H) z ξ = blockQQ (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_quot (h.one hz) hu hsz ξ
  have kB : mdbar (fun x => orthLift (H x)) z η =
      incl m l * (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := mdbar_orthLift H z η
  have k1 : orthProj (H z) * mdbar (fun x => conn H x ξ) z η * orthLift (H z) =
      orthProj (H z) * mdbar (fun x => orthLift (H x)) z η * blockQQ (H z) (conn H z ξ)
        - orthProj (H z) * mddbar (fun x => orthLift (H x)) z ξ η
        - orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η := by
    have e := congrArg (orthProj (H z) * ·) F1
    simp only [Matrix.mul_add] at e
    rw [← Matrix.mul_assoc (orthProj (H z)) (orthLift (H z)), orthProj_mul_orthLift,
      Matrix.zero_mul, zero_add] at e
    simp only [Matrix.mul_assoc]
    rw [← e]
    abel
  have k2 : mdel (fun x => orthProj (H x)) z ξ * mdbar (fun x => orthLift (H x)) z η = 0 := by
    rw [kB, ← Matrix.mul_assoc, mdel_orthProj_mul_incl, Matrix.zero_mul]
  have k3 : orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η =
      orthProj (H z) * conn H z ξ * incl m l *
        (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := by
    conv_lhs => rw [kB]
    simp only [Matrix.mul_assoc]
  simp only [covDelAnti, homDel, extForm]
  rw [mdel_mul hP1 hbL, mdel_mdbar hL2, k2, add_zero, cS, cQ, blockSQ, curv, Matrix.mul_neg,
    Matrix.neg_mul, k1, k3, blockSS]
  simp only [Matrix.mul_assoc]
  abel

end GlobalTheory.CurvSQ
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_off_diagonal_block : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η := by
  atlas_forward_decl GlobalTheory.CurvSQ.blockSQ_curv_eq_covDelAnti_extForm
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory

theorem blockQS_curv_eq_neg_dbarHol_extFormAdj {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  have e1 : blockQS (curv H z ξ η) = -mdbar (fun x => secondForm H x ξ) z η := by
    rw [blockQS_eq, curv]
    ext a b
    simp [secondForm, blockQS_eq, Matrix.toBlocks₂₁]
  have he : (fun x => extFormAdj H x ξ) =ᶠ[𝓝 z] fun x => -secondForm H x ξ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx)
      (hs x hx) ξ
  rw [e1, dbarHol, neg_neg, mdbar_congr he, mdbar_neg]

end GlobalTheory
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_quotient_sub_block : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η := by
  atlas_forward_decl GlobalTheory.blockQS_curv_eq_neg_dbarHol_extFormAdj
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section
namespace GlobalTheory.DbarExt

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem hasFDerivAt_fderiv_apply {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (u : V) :
    HasFDerivAt (fun x => fderiv ℝ f x u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z)) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z hD.hasFDerivAt

theorem dbar_dbar_comm {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v w : V) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  have key : ∀ u : V, HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        I • (ContinuousLinearMap.apply ℝ ℂ (I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
    intro u
    have := ((hasFDerivAt_fderiv_apply hf u).add
      ((hasFDerivAt_fderiv_apply hf (I • u)).const_smul I)).const_smul (1 / 2 : ℂ)
    exact this
  rw [dbar_eq_of_hasFDerivAt (key w), dbar_eq_of_hasFDerivAt (key v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (I • w), hs (I • v) w, hs (I • v) (I • w)]
  ring_nf

theorem dbarAnti_extForm_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V) :
    dbarAnti (extForm H) z η₁ η₂ = 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun x => orthCoeff (H x) a b) z := by
    intro a b
    have h1 := (GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)) (Sum.inl a) b
    have h2 : (fun x => orthCoeff (H x) a b) = fun x => -orthLift (H x) (Sum.inl a) b := by
      funext x; simp [orthLift]
    rw [h2]
    exact (h1.neg).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  simp only [dbarAnti, extForm_eq_neg_mdbar]
  ext a b
  simp only [Matrix.sub_apply, mdbar_apply, Matrix.neg_apply, Matrix.zero_apply, dbar_neg,
    ContinuousLinearMap.neg_apply]
  rw [dbar_dbar_comm (hc a b) η₁ η₂]
  simp

end GlobalTheory.DbarExt
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_extension_form_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V), dbarAnti (extForm H) z η₁ η₂ = 0 := by
  atlas_forward_decl GlobalTheory.DbarExt.dbarAnti_extForm_eq_zero
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotDelHol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_flat {n : Type*} [Fintype n] [DecidableEq n] {H : V → Matrix n n ℂ} {z : V}
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ₁ ξ₂ : V) :
    mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * conn H z ξ₂ - conn H z ξ₂ * conn H z ξ₁ = 0 := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have e : ∀ ζ ζ', mdel (fun x => conn H x ζ) z ζ' =
      (H z)ᵀ⁻¹ * (mdel (fun x => mdel H x ζ) z ζ')ᵀ +
        -((H z)ᵀ⁻¹ * (mdel H z ζ')ᵀ * (H z)ᵀ⁻¹) * (mdel H z ζ)ᵀ := by
    intro ζ ζ'
    simp only [conn]
    rw [mdel_mul (h1.transpose.inv hu') (h2.mdel (by norm_num) ζ).transpose,
      mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ζ), mdel_transpose]
  rw [e, e, mdel_mdel_comm h2 ξ₁ ξ₂]
  simp only [conn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  abel

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem covDelHol_extFormAdj_eq_zero {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
    (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V) :
    covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hγ : ∀ ζ, (fun x => extFormAdj H x ζ) =ᶠ[𝓝 z]
      fun x => -(quotMap m l * conn H x ζ * incl m l) := fun ζ => by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx) (hs x hx),
      secondForm, blockQS]
  have hc : ∀ ζ, MContDiffAt 1 (fun x => conn H x ζ) z := fun ζ => h2.conn hu (by norm_num) ζ
  have hd : ∀ ζ ζ', mdel (fun x => extFormAdj H x ζ) z ζ' =
      -(quotMap m l * mdel (fun x => conn H x ζ) z ζ' * incl m l) := by
    intro ζ ζ'
    rw [mdel_congr (hγ ζ), mdel_neg, mdel_mul ((mContDiffAt_const _).mul (hc ζ))
      (mContDiffAt_const _), mdel_mul (mContDiffAt_const _) (hc ζ)]
    simp
  have hv : ∀ ζ, extFormAdj H z ζ = -(quotMap m l * conn H z ζ * incl m l) :=
    fun ζ => (hγ ζ).self_of_nhds
  have hS : ∀ ζ, conn (gramS H) z ζ = orthProj (H z) * conn H z ζ * incl m l :=
    fun ζ => Model.conn_sub hu hsz ζ
  have hQ : ∀ ζ, conn (gramQ H) z ζ = quotMap m l * conn H z ζ * orthLift (H z) :=
    fun ζ => Model.conn_quot h1 hu hsz ζ
  have hF := conn_flat h2 hu ξ₁ ξ₂
  have key : quotMap m l * (mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₂ -
      conn H z ξ₂ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₁) *
      incl m l = 0 := by
    rw [incl_mul_orthProj_add, Matrix.mul_one, Matrix.mul_one, hF]; simp
  simp only [covDelHol, homDel, hd, hv, hS, hQ]
  rw [← neg_eq_zero, ← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, neg_neg, neg_sub, neg_add]
  abel

end GlobalTheory.SubQuotDelHol
end
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cov_del_hol_extension_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V), covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 := by
  atlas_forward_decl GlobalTheory.SubQuotDelHol.covDelHol_extFormAdj_eq_zero
end

section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotChTwo

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

section Calc

variable {m n : Type} [Fintype m] [Fintype n]

theorem dbar_trace_mul {X : V → Matrix n m ℂ} {Y : V → Matrix m n ℂ} {z : V}
    (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (η : V) :
    dbar (fun x => (X x * Y x).trace) z η = (mdbar X z η * Y z).trace + (X z * mdbar Y z η).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, dbar_sum (fun a _ => ((hX.mul hY).diff a a))]
  have := mdbar_mul hX hY η
  simp only [ContinuousLinearMap.sum_apply, Matrix.trace, Matrix.diag]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 := congrFun (congrFun this a) a
  simp only [mdbar_apply, Matrix.add_apply] at h2
  rw [h2, add_comm]

variable [DecidableEq m] [DecidableEq n]

theorem del_trace_mul {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {X : V → Matrix n m ℂ}
    {Y : V → Matrix m n ℂ} {z : V} (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (ξ : V) :
    del (fun x => (X x * Y x).trace) z ξ =
      (homDel A B X z ξ * Y z).trace + (X z * homDel B A Y z ξ).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, del_sum (fun a _ => (hX.mul hY).diff a a)]
  simp only [ContinuousLinearMap.sum_apply]
  have h1 : ∑ a, del (fun x => (X x * Y x) a a) z ξ = (mdel (fun x => X x * Y x) z ξ).trace := rfl
  rw [h1, mdel_mul hX hY]
  simp only [homDel, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (conn B z ξ)]
  simp only [Matrix.mul_assoc]
  ring

theorem mdbar_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ} {z : V}
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 2 B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt 2 T z) (ξ η : V) :
    mdbar (fun x => homDel A B T x ξ) z η =
      homDel A B (fun x => mdbar T x η) z ξ - curv B z ξ η * T z + T z * curv A z ξ η := by
  have hT1 : MContDiffAt 1 T z := hT.of_le one_le_two
  have hcA : MContDiffAt 1 (fun x => conn A x ξ) z := hA.conn hAu (by norm_num) ξ
  have hcB : MContDiffAt 1 (fun x => conn B x ξ) z := hB.conn hBu (by norm_num) ξ
  have hdT : MContDiffAt 1 (fun x => mdel T x ξ) z := hT.mdel (by norm_num) ξ
  show mdbar (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) z η = _
  rw [show (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) =
      fun x => (mdel T x ξ + conn B x ξ * T x) + -(T x * conn A x ξ) from
      funext fun x => sub_eq_add_neg _ _]
  rw [mdbar_add (hdT.add (hcB.mul hT1)) (hT1.mul hcA).neg, mdbar_neg,
    mdbar_add hdT (hcB.mul hT1), mdbar_mul hcB hT1, mdbar_mul hT1 hcA, mdbar_mdel hT]
  simp only [homDel, curv, mdel_mdbar hT, Matrix.neg_mul, Matrix.mul_neg]
  abel

theorem mContDiffAt_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ}
    {z : V} (hA : MContDiffAt ∞ A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt ∞ B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt ∞ T z) (ξ : V) :
    MContDiffAt 1 (fun x => homDel A B T x ξ) z := by
  have hA2 : MContDiffAt 2 A z := hA.of_le (by norm_cast)
  have hB2 : MContDiffAt 2 B z := hB.of_le (by norm_cast)
  have hT2 : MContDiffAt 2 T z := hT.of_le (by norm_cast)
  exact ((hT2.mdel (by norm_num) ξ).add ((hB2.conn hBu (by norm_num) ξ).mul
    (hT2.of_le one_le_two))).sub ((hT2.of_le one_le_two).mul (hA2.conn hAu (by norm_num) ξ))

end Calc

theorem chTwo_eq_trace {n : Type} [Fintype n] [DecidableEq n] (H : V → Matrix n n ℂ)
    (z ξ₁ η₁ ξ₂ η₂ : V) : chTwo H z ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 / 2 *
      ((curv H z ξ₁ η₁ * curv H z ξ₂ η₂).trace + (curv H z ξ₂ η₂ * curv H z ξ₁ η₁).trace
        - (curv H z ξ₁ η₂ * curv H z ξ₂ η₁).trace - (curv H z ξ₂ η₁ * curv H z ξ₁ η₂).trace) := by
  simp only [chTwo, wedge, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem trace_mul_eq_blocks (H K K' : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (K * K').trace = (blockSS H K * blockSS H K').trace + (blockSQ H K * blockQS K').trace +
      (blockQS K * blockSQ H K').trace + (blockQQ H K * blockQQ H K').trace := by
  have hP := incl_mul_orthProj_add (m := m) (l := l) H
  have e : K * K' = K * (incl m l * orthProj H + orthLift H * quotMap m l) * K' *
      (incl m l * orthProj H + orthLift H * quotMap m l) := by rw [hP]; simp
  rw [e]
  simp only [blockSS, blockSQ, blockQS, blockQQ, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    Matrix.mul_assoc, Matrix.trace_mul_comm (orthProj H), Matrix.trace_mul_comm (quotMap m l)]
  ring

section Deriv

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem ddbar_extTrace (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η ξ' η' : V) :
    ddbar (fun x => extTrace H x ξ' η') z ξ η = kappa *
      ((mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z η *
          extForm H z η').trace +
        (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') z ξ *
          mdbar (fun y => extForm H y η') z η).trace +
        (mdbar (fun y => extFormAdj H y ξ') z η *
          homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ).trace +
        (extFormAdj H z ξ' *
          (homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η') x η) z ξ -
            curv (gramS H) z ξ η * extForm H z η' + extForm H z η' * curv (gramQ H) z ξ η)).trace) := by
  have hS := h.sub hs
  have hQ := h.quot hs
  have hSu : ∀ x ∈ U, IsUnit (gramS H x).det := hs
  have hQu : ∀ x ∈ U, IsUnit (gramQ H x).det := fun x hx => hQ.isUnit x hx
  have sγ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extFormAdj H y ξ') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hx ξ'
  have sβ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extForm H y η') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hx η'
  have one : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 1 F x := fun hF => hF.of_le (by norm_cast)
  have two : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 2 F x := fun hF => hF.of_le (by norm_cast)
  have htr : ContDiffAt ℝ 2 (fun x => (extFormAdj H x ξ' * extForm H x η').trace) z := by
    have hM := (two (sγ z hz)).mul (two (sβ z hz))
    simp only [Matrix.trace, Matrix.diag]
    exact ContDiffAt.sum fun a _ => hM a a
  have e : (fun x => extTrace H x ξ' η') =
      fun x => kappa • (extFormAdj H x ξ' * extForm H x η').trace := rfl
  rw [e, ddbar_const_smul kappa htr, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ddbar_eq_dbar_del htr]
  congr 1
  have ev : (fun x => del (fun y => (extFormAdj H y ξ' * extForm H y η').trace) x ξ) =ᶠ[𝓝 z]
      fun x => (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ * extForm H x η').trace +
        (extFormAdj H x ξ' * homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ).trace := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact del_trace_mul (one (sγ x hx)) (one (sβ x hx)) ξ
  have hD1 : MContDiffAt 1 (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z :=
    mContDiffAt_homDel (hS.mContDiffAt hz) (hSu z hz) (hQ.mContDiffAt hz) (hQu z hz) (sγ z hz) ξ
  have hD2 : MContDiffAt 1 (fun x => homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ) z :=
    mContDiffAt_homDel (hQ.mContDiffAt hz) (hQu z hz) (hS.mContDiffAt hz) (hSu z hz) (sβ z hz) ξ
  have dtr : ∀ {F : V → Matrix l m ℂ} {G : V → Matrix m l ℂ}, MContDiffAt 1 F z →
      MContDiffAt 1 G z → DifferentiableAt ℝ (fun x => (F x * G x).trace) z := fun hF hG => by
    have hM := hF.mul hG
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun a _ => hM.diff a a
  rw [dbar_congr ev, dbar_add (dtr hD1 (one (sβ z hz))) (dtr (one (sγ z hz)) hD2),
    ContinuousLinearMap.add_apply, dbar_trace_mul hD1 (one (sβ z hz)),
    dbar_trace_mul (one (sγ z hz)) hD2,
    mdbar_homDel (A := gramQ H) (B := gramS H) (two (hQ.mContDiffAt hz)) (hQu z hz) (two (hS.mContDiffAt hz)) (hSu z hz)
      (two (sβ z hz)) ξ η]
  ring

end Deriv

theorem ddcForm_extTrace_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x)
    (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  intro V _ _ _ _ m l _ _ _ _ U H z h hs hz hb ξ₁ η₁ ξ₂ η₂
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz

  have hFD : ∀ η, mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) x ξ₁) z η =
      mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) x ξ₂) z η := by
    intro η
    refine mdbar_congr ?_ η
    filter_upwards [hU] with x hx
    exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hG : homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) z ξ₁ =
      homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) z ξ₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hBd : mdbar (fun y => extForm H y η₂) z η₁ = mdbar (fun y => extForm H y η₁) z η₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.1 η₁ η₂)
  have hHm : ∀ ξ, homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₂) x η₁) z ξ =
      homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₁) x η₂) z ξ := by
    intro ξ
    have ev : (fun x => mdbar (fun y => extForm H y η₂) x η₁) =ᶠ[𝓝 z]
        fun x => mdbar (fun y => extForm H y η₁) x η₂ := by
      filter_upwards [hU] with x hx
      exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.1 η₁ η₂)
    simp only [homDel]
    rw [mdel_congr ev ξ, hBd]

  obtain ⟨-, -, -, hSS, hSQ, hQS, hQQ, -, -⟩ := hb z hz
  have hK : ∀ ξ η ξ' η', (curv H z ξ η * curv H z ξ' η').trace =
      ((curv (gramS H) z ξ η + extForm H z η * extFormAdj H z ξ) *
        (curv (gramS H) z ξ' η' + extForm H z η' * extFormAdj H z ξ')).trace +
      (homDel (gramQ H) (gramS H) (fun y => extForm H y η) z ξ *
        mdbar (fun y => extFormAdj H y ξ') z η').trace +
      (mdbar (fun y => extFormAdj H y ξ) z η *
        homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ').trace +
      ((curv (gramQ H) z ξ η - extFormAdj H z ξ * extForm H z η) *
        (curv (gramQ H) z ξ' η' - extFormAdj H z ξ' * extForm H z η')).trace := by
    intro ξ η ξ' η'
    rw [trace_mul_eq_blocks (H z)]
    simp only [hSS, hSQ, hQS, hQQ, wedgeAntiHol, wedgeHolAnti, covDelAnti, dbarHol, neg_neg,
      sub_neg_eq_add]

  have c1 : ∀ (X : Matrix m m ℂ) (P : Matrix m l ℂ) (Q : Matrix l m ℂ),
      (X * (P * Q)).trace = (Q * (X * P)).trace := fun X P Q => by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have c3 : ∀ (Y : Matrix l l ℂ) (Q : Matrix l m ℂ) (P : Matrix m l ℂ),
      (Y * (Q * P)).trace = (Q * (P * Y)).trace := fun Y Q P => by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have c4 : ∀ (P : Matrix m l ℂ) (Q : Matrix l m ℂ), (P * Q).trace = (Q * P).trace :=
    fun P Q => Matrix.trace_mul_comm P Q
  simp only [ddcForm, ddbar_extTrace h hs hz, chTwo_eq_trace, hK]
  simp only [hFD, hG, hBd, hHm]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.mul_assoc]
  simp only [c1, c3, c4, Matrix.mul_assoc]
  ring

end GlobalTheory.SubQuotChTwo
end
end

section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_extension_trace_chern_forms : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  first | exact @GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq | exact GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq | (intros; apply GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq <;> assumption)
end

section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.HermFrame

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem secondForm_add_vec (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ ξ' : V) :
    secondForm H z (ξ + ξ') = secondForm H z ξ + secondForm H z ξ' := by
  rw [secondForm_eq, secondForm_eq, secondForm_eq, conn_add_vec]; rfl

theorem secondForm_smul_vec (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V) (c : ℂ) (ξ : V) :
    secondForm H z (c • ξ) = c • secondForm H z ξ := by
  rw [secondForm_eq, secondForm_eq, conn_smul_vec]; rfl

theorem isNonnegForm_extTrace {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
    (h : IsPosFrame U H) (hz : z ∈ U) : IsNonnegForm (extTrace H z) := by
  have h1 : MContDiffAt 1 H z := h.isHermFrame.one hz
  have hp : ∀ᶠ x in 𝓝 z, (H x).PosDef := Filter.eventually_of_mem (h.isOpen.mem_nhds hz) h.posDef
  have hS : (subGram (H z)).IsHermitian := (posDef_subGram hp.self_of_nhds).isHermitian
  have hQ : (quotGram (H z)).IsHermitian := (posDef_quotGram hp.self_of_nhds).isHermitian
  have e : ∀ ξ η, extTrace H z ξ η = kappa * (secondForm H z ξ * secondFormAdj H z η).trace :=
    extTrace_eq h1 hp
  refine ⟨⟨fun x x' y => ?_, fun c x y => ?_, fun x y y' => ?_, fun c x y => ?_⟩, fun ξ η => ?_,
    fun ξ => ?_⟩
  · simp only [e, secondForm_add_vec, Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondForm_smul_vec, Matrix.smul_mul, trace_smul, smul_eq_mul]; ring
  · simp only [e, secondFormAdj, adj, secondForm_add_vec, conjTranspose_add, Matrix.mul_add,
      Matrix.add_mul, trace_add, mul_add]
  · simp only [e, secondFormAdj, adj, secondForm_smul_vec, conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.star_def]; ring
  · have hk : conj kappa = -kappa := by
      rw [kappa, map_div₀, map_mul, conj_I, Complex.conj_ofReal, map_ofNat]; ring
    have ht : conj (secondForm H z ξ * secondFormAdj H z η).trace =
        (secondForm H z η * secondFormAdj H z ξ).trace := by
      rw [← Complex.star_def, ← trace_conjTranspose]
      simp only [secondFormAdj, adj, conjTranspose_mul, conjTranspose_conjTranspose,
        conjTranspose_nonsing_inv, hS.transpose.eq, hQ.transpose.eq, Matrix.mul_assoc]
      rw [trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, e, map_mul, hk, ht, neg_mul]
  · have : diagVal (fun _ _ : V => (0 : ℂ)) ξ = 0 := by simp [diagVal]
    rw [this]
    exact diagVal_extTrace_nonneg h1 hp ξ

end GlobalTheory.HermFrame
end
end

section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ext_trace_nonneg_of_pos_frame : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U), IsNonnegForm (extTrace H z) := by
  first | exact @GlobalTheory.HermFrame.isNonnegForm_extTrace | exact GlobalTheory.HermFrame.isNonnegForm_extTrace | (intros; apply GlobalTheory.HermFrame.isNonnegForm_extTrace <;> assumption)
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory.SqZeroLine

theorem trace_mul_eq_of_card_one {m l : Type} [Fintype m] [Fintype l]
    (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) :
    ∃ a : m, ∃ b : l, ∀ (A : Matrix l m ℂ) (B : Matrix m l ℂ), (A * B).trace = A b a * B a b := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hm
  obtain ⟨b, hb⟩ := Fintype.card_eq_one_iff.mp hl
  refine ⟨a, b, fun A B => ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_eq_single b (fun i hi => (hi (hb i)).elim)]
  rw [Fintype.sum_eq_single a (fun i hi => (hi (ha i)).elim)]

theorem wedge_self_of_product {V : Type} (α : V → V → ℂ) (g f : V → ℂ) (c : ℂ)
    (hα : ∀ ξ η, α ξ η = c * g ξ * f η) (ξ₁ η₁ ξ₂ η₂ : V) :
    wedge α α ξ₁ η₁ ξ₂ η₂ = 0 := by
  simp only [wedge, hα]; ring

end GlobalTheory.SqZeroLine

theorem GlobalTheory.extTrace_wedge_self_eq_zero_of_line : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 := by
  intro V _ _ _ _ m l _ _ _ _ U H z _ _ hm hl ξ₁ η₁ ξ₂ η₂
  obtain ⟨a, b, hab⟩ := GlobalTheory.SqZeroLine.trace_mul_eq_of_card_one hm hl
  exact GlobalTheory.SqZeroLine.wedge_self_of_product (extTrace H z)
    (fun ξ => extFormAdj H z ξ b a) (fun η => extForm H z η a b) kappa
    (fun ξ η => by simp only [extTrace, hab]; ring) ξ₁ η₁ ξ₂ η₂
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ext_trace_wedge_self_eq_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 := by
  atlas_forward_decl GlobalTheory.extTrace_wedge_self_eq_zero_of_line
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory.LineRankTwo

theorem chernOne_sub_quot_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H)
    (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1)
    (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η)
    (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η)
    (u : m → ℂ) (hu : u ≠ 0) (ξ η : V) :
    chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧
    chernOne (gramQ H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η := by
  have hzH : (H z).PosDef := h.posDef z hz
  have hS : (subGram (H z)).PosDef := posDef_subGram hzH
  have hsu : IsUnit (subGram (H z)).det := (isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSu : form (subGram (H z)) u u ≠ 0 := ((posDef_iff.1 hS).2 u hu).ne'
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hm
  have hvec : ∀ M : Matrix m m ℂ, M *ᵥ u = M.trace • u := by
    intro M
    funext i
    rw [ha i]
    simp only [mulVec, dotProduct, trace, diag, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj),
      Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj)]
  have hline : lineCurv H z (incl m l *ᵥ u) ξ η = kappa * (blockSS (H z) (curv H z ξ η)).trace := by
    have e1 : curv H z ξ η *ᵥ (incl m l *ᵥ u) = incl m l *ᵥ (blockSS (H z) (curv H z ξ η) *ᵥ u) +
        orthLift (H z) *ᵥ (quotMap m l *ᵥ (curv H z ξ η *ᵥ (incl m l *ᵥ u))) := by
      conv_lhs => rw [← Matrix.one_mulVec (curv H z ξ η *ᵥ _), ← incl_mul_orthProj_add (H z)]
      simp only [Matrix.add_mulVec, mulVec_mulVec, blockSS, Matrix.mul_assoc, Matrix.add_mul]
    rw [lineCurv, e1, form_add_left, form_orthLift_incl hsu, add_zero, form_incl, form_incl, hvec,
      form_smul_left, mul_div_assoc, div_self hSu, mul_one]
  have hp : ∀ᶠ x in 𝓝 z, (H x).PosDef :=
    Filter.eventually_of_mem (h.isOpen.mem_nhds hz) fun x hx => h.posDef x hx
  have hext : extTrace H z ξ η = kappa * (secondForm H z ξ * secondFormAdj H z η).trace :=
    extTrace_eq (h.isHermFrame.one hz) hp ξ η
  have h1 : chernOne (gramS H) z ξ η =
      lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η := by
    rw [chernOne, hg, hline, hext, wedgeAntiHol, trace_add, trace_neg,
      trace_mul_comm (secondFormAdj H z η)]
    ring
  refine ⟨h1, ?_⟩
  rw [hc ξ η, h1]
  ring

end GlobalTheory.LineRankTwo
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_bundle_curvature_rank_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (u : m → ℂ) (hu : u ≠ 0) (ξ η : V), chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧ chernOne (gramQ H) z ξ η = chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η := by
  atlas_forward_decl GlobalTheory.LineRankTwo.chernOne_sub_quot_line
end

section
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory

theorem ddcForm_extTrace_eq_rank_two
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1)
    (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η)
    (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂)
    (ξ₁ η₁ ξ₂ η₂ : V) :
    ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ := by
  have hz : ∀ {n : Type} [Fintype n] [DecidableEq n], Fintype.card n = 1 →
      ∀ G : V → Matrix n n ℂ, chernTwo G z ξ₁ η₁ ξ₂ η₂ = 0 := by
    intro n _ _ hn G
    have hs : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp hn.le
    have h : ∀ a b : n, curvMinor G z a b ξ₁ η₁ ξ₂ η₂ = 0 := fun a b => by
      rw [Subsingleton.elim b a]; exact curvMinor_self G z a ξ₁ η₁ ξ₂ η₂
    simp [chernTwo, h]
  rw [hd, chTwo_eq, chTwo_eq, chTwo_eq, hz hm, hz hl]
  simp only [wedge, hc]
  ring

end GlobalTheory
end

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_two_ddc_ext_trace : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ := by
  atlas_forward_decl GlobalTheory.ddcForm_extTrace_eq_rank_two
end

section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotCurv

theorem connBlocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) :=
  GlobalTheory.T.connection_blocks_hermitian_frame

theorem gaussS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η :=
  GlobalTheory.T.subbundle_curvature_formula

theorem gaussQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η :=
  GlobalTheory.T.quotient_bundle_curvature_formula

theorem curvSQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η :=
  GlobalTheory.T.curvature_off_diagonal_block

theorem curvQS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η :=
  GlobalTheory.T.curvature_quotient_sub_block

theorem dbarExt : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V), dbarAnti (extForm H) z η₁ η₂ = 0 :=
  GlobalTheory.T.dbar_extension_form_zero

theorem delExtAdj : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V), covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 :=
  GlobalTheory.T.cov_del_hol_extension_zero

theorem ddcAny : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.ddc_extension_trace_chern_forms

theorem nonneg : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U), IsNonnegForm (extTrace H z) :=
  GlobalTheory.T.ext_trace_nonneg_of_pos_frame

theorem sqZero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 :=
  GlobalTheory.T.ext_trace_wedge_self_eq_zero

theorem line_bundle_curvature_subquotient : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (u : m → ℂ) (hu : u ≠ 0) (ξ η : V), chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧ chernOne (gramQ H) z ξ η = chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η :=
  GlobalTheory.T.sub_bundle_curvature_rank_one

theorem ddcTwo : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.chern_two_ddc_ext_trace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem formTypes_secondForm (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : FormTypes (secondFormAdj H) (secondForm H) z := by
  refine ⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
    fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondFormAdj h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondForm h hz ξ⟩
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_add_vec, Matrix.mul_add,
      Matrix.add_mul, conjTranspose_add]
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_smul_vec, Matrix.mul_smul,
      Matrix.smul_mul, conjTranspose_smul, Complex.star_def]
  · simp only [secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul]
  · simp only [secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul]

theorem subQuotAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    SubQuotAt H z :=
  ⟨fun ξ _ => ⟨eq_conn_of_compatible (h.isUnit z hz),
      fun e => e ▸ conn_transpose_mul (h.isUnit z hz) ξ⟩,
    formTypes_secondForm h hs hz, fun ξ s q => form_secondForm (h.herm z hz) (hs z hz) ξ s q,
    connBlocks h hs hz, gaussS h hs hz, gaussQ h hs hz⟩

theorem extForm_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    extForm H z = fun η => -secondFormAdj H z η :=
  funext fun η => extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) η

theorem extFormAdj_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : extFormAdj H z = fun ξ => -secondForm H z ξ :=
  funext fun ξ => extFormAdj_eq_neg_secondForm (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) ξ

theorem extBlocksAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ExtBlocksAt H z := by
  have hh := h.herm z hz
  have eβ := extForm_eq h hs hz
  have eγ := extFormAdj_eq h hs hz
  have ft := formTypes_secondForm h hs hz
  have w1 : ∀ ξ η, wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η =
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := fun ξ η => by
    simp only [wedgeAntiHol, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have w2 : ∀ ξ η, wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η =
      wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := fun ξ η => by
    simp only [wedgeHolAnti, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine ⟨⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
      fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hz ξ⟩,
    fun ξ q s => form_adj (isHermitian_quotGram hh) (isUnit_det_quotGram (h.isUnit z hz) (hs z hz))
      (isHermitian_subGram hh) _ q s, ?_, fun ξ η => ?_, curvSQ h hs hz, curvQS h hs hz,
    fun ξ η => ?_, dbarExt h hs hz, delExtAdj h hs hz⟩
  · rw [eβ]; simp only [ft.1 η η', neg_add]
  · rw [eβ]; simp only [ft.2.1 c η, smul_neg]
  · rw [eγ]; simp only [ft.2.2.1 ξ ξ', neg_add]
  · rw [eγ]; simp only [ft.2.2.2.1 c ξ, smul_neg]
  · have e2 : (fun ξ => -extFormAdj H z ξ) = secondForm H z := by
      rw [eγ]; funext ξ; simp
    rw [eβ, e2]; exact connBlocks h hs hz
  · rw [w1, gaussS h hs hz]; abel
  · rw [w2, gaussQ h hs hz]; abel

theorem chernOne_add (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η : V) :
    chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η := by
  rw [chernOne, chernOne, chernOne, GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.trace_eq_blocks (H z), gaussS h hs hz, gaussQ h hs hz]
  simp only [wedgeAntiHol, wedgeHolAnti, trace_add, trace_neg,
    trace_mul_comm (secondForm H z ξ)]
  ring

theorem subQuotCurvature : SubQuotCurvature := by
  intro V _ _ _ _ _ m l _ _ _ _ U H
  refine ⟨fun h hs => ⟨h.sub hs, h.quot hs, fun z hz => subQuotAt h hs hz⟩, fun hp => ?_⟩
  have h := hp.isHermFrame
  have hs : ∀ z ∈ U, IsUnit (subGram (H z)).det := fun z hz => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub hp z hz
  refine ⟨hp.sub, hp.quot, fun z hz => ⟨fun ξ s => ?_, extBlocksAt h hs hz,
    nonneg hp hz, chernOne_add h hs hz, ddcAny h hs hz (fun x hx => extBlocksAt h hs hx)⟩,
    fun hm hl z hz => ⟨nonneg hp hz, sqZero hp hz hm hl,
      fun u hu ξ η => line_bundle_curvature_subquotient hp hz hm hl (gaussS h hs hz) (chernOne_add h hs hz) u hu ξ η,
      ddcTwo hm hl (chernOne_add h hs hz) (ddcAny h hs hz (fun x hx => extBlocksAt h hs hx))⟩⟩
  have hh := h.herm z hz
  simp only [wedgeAntiHol, gramS, gramQ]
  rw [form_secondFormAdj_mul hh (hs z hz) ξ s, form_self (posDef_quotGram (hp.posDef z hz)).posSemidef]

end GlobalTheory.SubQuotCurv
end
end
