import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧ ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K := by
  first | exact @GlobalTheory.ScalarAnnih.exists_compact_of_annih | exact GlobalTheory.ScalarAnnih.exists_compact_of_annih | (intros; apply GlobalTheory.ScalarAnnih.exists_compact_of_annih <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis : ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w = ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  first | exact @GlobalTheory.TwistCoords.finPart_eq_sum_trace | exact GlobalTheory.TwistCoords.finPart_eq_sum_trace | (intros; apply GlobalTheory.TwistCoords.finPart_eq_sum_trace <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_test_matrix_isolates_entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  atlas_forward_decl GlobalTheory.EntryTest.entry
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanAnnih

theorem finPart_mem_compact : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  intro D V W a b P Q hP hQ ψ hψ U hU
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis D
  have hm : ∀ p : Fin a × Fin b × Fin d, ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) =
        r * Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
    fun p => GlobalTheory.T.exists_rational_test_matrix_isolates_entry D V W a b P Q hP hQ p.1 p.2.1 (c p.2.2)
  choose m hm using hm
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  let φ : (Fin a × Fin b × Fin d) → Af D.host.F → WO V W :=
    fun p t => (pairA D.host.F 0 t) • (m p).map (incA D)
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => (m p).map (incA D)) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hφ0]; exact U.zero_mem))
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar D ψ hψ _ hO
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : ContinuousSMul (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  let g : (Fin a × Fin b × Fin d → Af D.host.F) → Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun z => Matrix.of fun i j => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin a × Fin b × Fin d → Af D.host.F => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin a × Fin b × Fin d → Af D.host.F => z (i, j, l) ⊗ₜ[D.host.F] e l) =
        fun z => z (i, j, l) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin a × Fin b × Fin d => Af D.host.F) (i, j, l))
      (continuous_const (y := ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy =>
    ⟨fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1)),
      fun p _ => hmem _ fun t ht => ?_, ?_⟩⟩
  · have hu : φ p t ∈ U := Set.mem_iInter.1 ht p
    have hinf : (φ p t).map (infPart D) = 0 := by
      ext k l
      simp only [φ, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
      change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] m p k l)) = 0
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (m p k l) = 0
      exact TensorProduct.zero_tmul _ _
    have h1 := hy _ hu hinf
    simp only [φ] at h1
    rw [hm] at h1
    convert h1 using 2
    exact Prod.ext (zero_mul _).symm rfl
  · ext i j
    simp only [g, Matrix.of_apply, Matrix.map_apply]
    rw [hce]

end GlobalTheory.IsoMeanAnnih
end
