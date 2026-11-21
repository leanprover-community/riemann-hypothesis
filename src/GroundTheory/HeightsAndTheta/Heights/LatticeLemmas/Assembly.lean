import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLatticeOfLocalisations
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PChainSum
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Extension
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsFibreMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSpherePhase

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights

noncomputable section

theorem gramDet_sub {K : Type*} [Field K] [NumberField K] (M : HermitianBundle K)
    (F : Submodule (𝓞 K) M.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) :
    gramDet (M.sub F).metric σ s = gramDet M.metric σ (fun i ↦ (s i : M.carrier)) := by
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec (M.sub F).metric σ (s i)) =
      Matrix.gram ℂ fun i ↦ fibreVec M.metric σ (s i : M.carrier) := by
    ext i j
    rfl
  simp only [gramDet]
  rw [hG]

theorem card_quotient_span_sub {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E]
    [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) {ι : Type*} (s : ι → F) :
    Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) * Nat.card (E ⧸ F) := by
  set S := Submodule.span (𝓞 K) (Set.range s)
  set T := Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))
  have hspan : T = S.map F.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hTF : T ≤ F := by
    rw [hspan]; exact Submodule.map_subtype_le F S
  rw [← Submodule.card_quotient_mul_card_quotient F T hTF]
  congr 1
  have hk : LinearMap.ker (T.mkQ ∘ₗ F.subtype) = S := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hspan,
      Submodule.comap_map_eq_of_injective F.injective_subtype]
  have hr : LinearMap.range (T.mkQ ∘ₗ F.subtype) = F.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hk, ← hr]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem Sublattice.proof : Sublattice.Statement := by
  intro K _ _ M F hF
  have : Module.Finite (𝓞 K) F := inferInstanceAs (Module.Finite (𝓞 K) (M.sub F).carrier)
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := F)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ (s i : M.carrier)) :=
    hs.map' F.subtype (LinearMap.ker_eq_bot.mpr F.injective_subtype)
  have hcardF : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) F :=
    Fintype.card_fin _
  have hcardM : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) M.carrier := by
    rw [Fintype.card_fin, hF]
  have hdM : M.arithDegree = degreeWith M.metric (fun i ↦ (s i : M.carrier)) :=
    arithDegree_eq _ ht hcardM
  have hdF : (M.sub F).arithDegree = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ (fun i ↦ (s i : M.carrier))) := by
    have h1 := arithDegree_eq (M.sub F).metric hs hcardF
    rw [HermitianBundle.arithDegree, h1]
    unfold degreeWith
    simp only [gramDet_sub]
    rfl
  have hfin := finite_quotient_span ht hcardM
  have hpos : 0 < Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : M.carrier))) :=
    Nat.card_pos
  have hc := card_quotient_span_sub F s
  rw [hc] at hpos
  have ha : (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have hb : (0 : ℝ) < Nat.card (M.carrier ⧸ F) := by
    exact_mod_cast Nat.pos_of_mul_pos_left hpos
  have hsum : M.arithDegree = (M.sub F).arithDegree + Real.log (Nat.card (M.carrier ⧸ F)) := by
    rw [hdM, hdF, degreeWith, hc, Nat.cast_mul, Real.log_mul ha.ne' hb.ne']
    ring
  have hlog : 0 ≤ Real.log (Nat.card (M.carrier ⧸ F)) := Real.log_natCast_nonneg _
  have hdeg : M.deg = (M.sub F).deg + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K := by
    simp only [HermitianBundle.deg]
    rw [hsum, add_div]
  refine ⟨hdeg, ?_⟩
  rw [hdeg]
  exact le_add_of_nonneg_right (div_nonneg hlog (Nat.cast_nonneg _))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace

universe u v w

noncomputable section

theorem det_gram_re_le_prod_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (det (gram ℂ v)).re ≤ ∏ i, ‖v i‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hgw : gram ℂ v = gram ℂ w := by
    ext i j
    simp only [gram_apply, w, Submodule.coe_inner]
  have hfin : Module.finrank ℂ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let b : OrthonormalBasis (Fin n) ℂ W := gramSchmidtOrthonormalBasis hfin w
  have hb : b.toBasis.det w = ∏ i, inner ℂ (b i) (w i) := gramSchmidtOrthonormalBasis_det hfin w
  set A := b.toBasis.toMatrix w
  have hA : gram ℂ w = Aᴴ * A := by
    ext j k
    rw [gram_apply, mul_apply, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [A, conjTranspose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, RCLike.star_def,
      inner_conj_symm]
  have hdet : (det (gram ℂ w)).re = ‖b.toBasis.det w‖ ^ 2 := by
    rw [hA, det_mul, det_conjTranspose, Module.Basis.det_apply, RCLike.star_def, Complex.conj_mul']
    norm_cast
  rw [hgw, hdet, hb, norm_prod, ← Finset.prod_pow]
  gcongr with i
  calc ‖inner ℂ (b i) (w i)‖ ≤ ‖b i‖ * ‖w i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]; rfl

section Gram

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem log_gramDet_le (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    Real.log (gramDet h σ s) ≤ 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
  let e := Fintype.equivFin ι
  have hs' : LinearIndependent (𝓞 K) (s ∘ e.symm) := hs.comp _ e.symm.injective
  have hne : ∀ i, fibreVec h σ (s i) ≠ 0 := (linearIndependent_fibreVec h σ hs).ne_zero
  have hH := det_gram_re_le_prod_norm_sq (fun i ↦ fibreVec h σ ((s ∘ e.symm) i))
    (linearIndependent_fibreVec h σ hs')
  rw [← gramDet_reindex h σ e.symm s]
  calc Real.log (gramDet h σ (s ∘ e.symm))
      ≤ Real.log (∏ i, ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2) :=
        Real.log_le_log (gramDet_pos h σ hs') hH
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ ((s ∘ e.symm) i)‖ := by
        rw [Real.log_prod (s := Finset.univ) (f := fun i ↦ ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2)
          (fun i _ ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne (e.symm i)))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Real.log_pow]
        push_cast
        ring
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
        congr 1
        exact e.symm.sum_comp (fun i ↦ Real.log ‖fibreVec h σ (s i)‖)

end Gram

theorem Hadamard.intersectionNumber_baseChange : Hadamard.Statement.{u, v, w} := by
  intro K _ _ M ι _ x La hli hcard hnorm
  classical
  set r := Module.finrank (𝓞 K) M.carrier
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : 0 ≤ Real.log (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x))) :=
    Real.log_natCast_nonneg _
  have hσ : ∀ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤ 2 * (r * Real.log La) := by
    intro σ
    refine (log_gramDet_le M.metric σ hli).trans ?_
    have hle : ∑ i, Real.log ‖fibreVec M.metric σ (x i)‖ ≤ ∑ _i : ι, Real.log La :=
      Finset.sum_le_sum fun i _ ↦ Real.log_le_log
        (norm_pos_iff.mpr ((linearIndependent_fibreVec M.metric σ hli).ne_zero i)) (hnorm i σ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hle
    linarith
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      Module.finrank ℚ K * (2 * (r * Real.log La)) := by
    calc _ ≤ ∑ _σ : K →+* ℂ, 2 * (r * Real.log La) := Finset.sum_le_sum fun σ _ ↦ hσ σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hli hcard, degreeWith,
    le_div_iff₀ hd]
  nlinarith

theorem Hadamard.proof (_h1 : Sublattice.Statement.{u, v}) : Hadamard.Statement.{u, v, w} :=
  Hadamard.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

namespace HadamardQuotient

theorem exists_subfamily_card_eq_finrank {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (F : Submodule R M)
    {ι : Type*} (x : ι → M) (hx : finrank R (span R (Set.range x)) = finrank R M) :
    ∃ s : Set ι, LinearIndepOn R (F.mkQ ∘ x) s ∧ Finite s ∧ Nat.card s = finrank R (M ⧸ F) := by
  classical
  set y : ι → M ⧸ F := F.mkQ ∘ x with hy_def
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R y
  have hfin : Finite s := LinearIndependent.finite_of_isNoetherian hs
  set S : Submodule R (M ⧸ F) := span R (y '' s) with hS_def

  have hy : ∀ i, S.mkQ (y i) ∈ torsion R ((M ⧸ F) ⧸ S) := by
    intro i
    by_cases hi : i ∈ s
    · have h0 : S.mkQ (y i) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr (subset_span ⟨i, hi, rfl⟩)
      rw [h0]
      exact zero_mem _
    · obtain ⟨a, ha, h⟩ := hmax i hi
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      change a • S.mkQ (y i) = 0
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
  have hspan : span R (Set.range y) ≤ (torsion R ((M ⧸ F) ⧸ S)).comap S.mkQ :=
    span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)

  set N : Submodule R M := span R (Set.range x) with hN_def
  have hN : finrank R (M ⧸ N) = 0 := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
    norm_cast at h
    omega

  have hQS : finrank R ((M ⧸ F) ⧸ S) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro q
    obtain ⟨q, rfl⟩ := S.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha, ham⟩ := Module.finrank_eq_zero_iff.mp hN (N.mkQ m)
    have h1 : a • m ∈ N := by
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at ham
      exact ham
    have h2 : F.mkQ (a • m) ∈ span R (Set.range y) := by
      have h := Submodule.mem_map_of_mem (f := F.mkQ) h1
      rwa [hN_def, Submodule.map_span, ← Set.range_comp] at h
    obtain ⟨⟨b, hb⟩, hbm⟩ := hspan h2
    refine ⟨b * a, mul_ne_zero (nonZeroDivisors.ne_zero hb) ha, ?_⟩
    change b • S.mkQ (F.mkQ (a • m)) = 0 at hbm
    rw [mul_smul, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    rw [map_smul, map_smul] at hbm
    rw [map_smul, map_smul]
    exact hbm
  have hadd := rank_quotient_add_rank_of_isDomain S
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at hadd
  norm_cast at hadd
  have := Fintype.ofFinite s
  have hSr : finrank R S = Nat.card s := by
    rw [hS_def, Set.image_eq_range, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hs
  exact ⟨s, hs, hfin, by omega⟩

variable {K : Type*} [Field K] [NumberField K]

theorem normAt_mkQ_le (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
    (σ : K →+* ℂ) (x : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ x) ≤ M.normAt σ x := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (F.mkQ x : M.carrier ⧸ F))
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] x, rfl⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ x})

end HadamardQuotient

theorem HadamardQuotient.proof (h1 : Hadamard.Statement.{u, v, w}) :
    HadamardQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x La hx hLa
  obtain ⟨s, hs, hfin, hcard⟩ := exists_subfamily_card_eq_finrank F x hx
  have := Fintype.ofFinite s
  exact h1 K (M.quot F hF) (ι := s) (fun i ↦ F.mkQ (x i)) La hs
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    (fun i σ ↦ (normAt_mkQ_le M F hF σ (x i)).trans (hLa i σ))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField Matrix GroundTheory.Heights₂.Heights

noncomputable section

section GramHadamard

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem norm_sub_starProjection_le {ι : Type*} [Fintype ι] (v : ι → V) (y : V) :
    ‖y - (Submodule.span ℂ (Set.range v)).starProjection y‖ ≤ ‖y‖ := by
  set U := Submodule.span ℂ (Set.range v)
  calc ‖y - U.starProjection y‖ ≤ ‖y - ((0 : U) : V)‖ := by
        rw [Submodule.starProjection_minimal]
        exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (0 : U)
    _ = ‖y‖ := by simp

theorem re_det_gram_le_prod_fin : ∀ (n : ℕ) (c : Fin n → V),
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : c ∘ e = Sum.elim (fun i ↦ c i.castSucc) (fun _ : Unit ↦ c (Fin.last n)) := by
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : det (gram ℂ c) = det (gram ℂ fun i : Fin n ↦ c i.castSucc) *
        ((‖c (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ c i.castSucc)).starProjection
          (c (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      rw [← det_gram_comp_equiv e c, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key, Complex.re_mul_ofReal, Fin.prod_univ_castSucc]
    exact mul_le_mul (ih _)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ _) 2) (sq_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)

theorem re_det_gram_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → V) :
    (det (gram ℂ c)).re ≤ ∏ i, ‖c i‖ ^ 2 := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_le_prod_fin (Fintype.card ι) (c ∘ e)
  rw [det_gram_comp_equiv e c] at h
  refine h.trans_eq ?_
  exact Fintype.prod_equiv e _ _ fun _ ↦ rfl

end GramHadamard

theorem HadamardMean.intersectionNumber_baseChange : HadamardMean.Statement := by
  intro K _ _ M ι _ x hx hcard
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hx hcard, degreeWith]
  refine (div_le_div_iff_of_pos_right hn).mpr ?_
  have hσ : ∀ σ : K →+* ℂ,
      Real.log (gramDet M.metric σ x) ≤ 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
    intro σ
    have hne : ∀ i, fibreVec M.metric σ (x i) ≠ 0 := fun i ↦
      (linearIndependent_fibreVec M.metric σ hx).ne_zero i
    have h1 : gramDet M.metric σ x ≤ ∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2 :=
      re_det_gram_le_prod _
    calc Real.log (gramDet M.metric σ x)
        ≤ Real.log (∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2) :=
          Real.log_le_log (gramDet_pos M.metric σ hx) h1
      _ = ∑ i, Real.log (‖fibreVec M.metric σ (x i)‖ ^ 2) := by
          rw [Real.log_prod]
          intro i _
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne i))
      _ = 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Real.log_pow, HermitianBundle.normAt]
          push_cast
          rfl
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      2 * ∑ i, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x i)) := by
    rw [Finset.sum_comm (f := fun i σ ↦ Real.log (M.normAt σ (x i))), Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ ↦ hσ σ
  have hc := Real.log_natCast_nonneg
    (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x)))
  linarith

theorem HadamardMean.proof (_h1 : Sublattice.Statement) : HadamardMean.Statement :=
  HadamardMean.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct

universe u v w

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

theorem normAt_mkQ_le (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    (hF : M.Saturated F) (σ : K →+* ℂ) (e : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ e) ≤ M.normAt σ e := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e)
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] e, by simp⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ e})

theorem exists_linearIndependent_mkQ (M : HermitianBundle.{v} K) (F : Submodule (𝓞 K) M.carrier)
    {ι : Type w} (x : ι → M.carrier)
    (hx : Module.finrank (𝓞 K) (span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier) :
    ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
      LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) := by
  classical
  let v : ι → M.carrier ⧸ F := fun i ↦ F.mkQ (x i)
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn (𝓞 K) v
  set N := span (𝓞 K) (v '' s)
  have hS : Module.IsTorsion (𝓞 K) (M.carrier ⧸ span (𝓞 K) (Set.range x)) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have := Submodule.finrank_quotient_add_finrank (span (𝓞 K) (Set.range x))
    omega
  have hv : span (𝓞 K) (Set.range x) ≤
      (torsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N)).comap (N.mkQ ∘ₗ F.mkQ) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · have : N.mkQ (v i) = 0 := by
        rw [mkQ_apply, Quotient.mk_eq_zero]
        exact subset_span ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      exact this ▸ zero_mem _
    · obtain ⟨a, ha, hav⟩ := hmax i hi
      simp only [SetLike.mem_coe, mem_comap, LinearMap.coe_comp, Function.comp_apply]
      rw [mem_torsion_iff]
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero]
      exact hav
  have hT : Module.IsTorsion (𝓞 K) ((M.carrier ⧸ F) ⧸ N) := by
    intro q
    obtain ⟨q, rfl⟩ := N.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha⟩ := hS (x := (span (𝓞 K) (Set.range x)).mkQ m)
    rw [Submonoid.smul_def, ← map_smul, mkQ_apply, Quotient.mk_eq_zero] at ha
    obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp (hv ha)
    refine ⟨b * a, ?_⟩
    rw [Submonoid.smul_def] at hb ⊢
    simpa [mul_smul, map_smul] using hb
  have hrank : Module.rank (𝓞 K) (M.carrier ⧸ F) ≤ #(v '' s) := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [Module.rank_eq_zero_iff_isTorsion.mpr hT, zero_add] at h
    exact h ▸ rank_span_le _
  have hle : lift.{w} #(Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F))) ≤ lift.{0} #s := by
    have h1 := (lift_le.{w}).mpr hrank
    have h2 := mk_image_le_lift (f := v) (s := s)
    rw [← Module.finrank_eq_rank, lift_natCast] at h1
    rw [mk_fin, lift_natCast, lift_uzero]
    exact (lift_le.{v}).mp (by simpa using h1.trans h2)
  obtain ⟨e⟩ := lift_mk_le'.mp hle
  exact ⟨fun j ↦ (e j : ι), hs.comp e e.injective⟩

theorem HadamardMeanQuotient.proof (h1 : HadamardMean.Statement.{u, v, 0}) :
    HadamardMeanQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x hx
  obtain ⟨s, hs⟩ := exists_linearIndependent_mkQ M F x hx
  refine ⟨s, hs, le_trans ?_ (h1 K (M.quot F hF) (fun j ↦ F.mkQ (x (s j))) hs
    (by rw [Fintype.card_fin]; rfl))⟩
  gcongr with j _ σ _
  have hne : HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) ≠ 0 := by
    have := (linearIndependent_fibreVec (M.quot F hF).metric σ hs).ne_zero j
    exact norm_ne_zero_iff.mpr this
  have hpos : 0 < HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) :=
    (norm_nonneg _).lt_of_ne' hne
  all_goals first
    | exact hpos
    | exact normAt_mkQ_le M F hF σ _

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GaussNormBasic

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
theorem normAbv_apply (x : L) : normAbv L x = ‖x‖ := rfl

theorem isNonarchimedean_normAbv : IsNonarchimedean (normAbv L) :=
  fun x y ↦ IsUltrametricDist.isNonarchimedean_norm x y

theorem gaussNorm_add_le {ι : Type*} (g g' : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (g + g') ≤
      max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') := by
  refine gaussNormOf_le _ ((gaussNormOf_nonneg _ g).trans (le_max_left _ _)) fun m ↦ ?_
  rw [coeff_add]
  exact (isNonarchimedean_normAbv _ _).trans
    (max_le_max (le_gaussNormOf _ g m) (le_gaussNormOf _ g' m))

theorem gaussNorm_sum_le {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ r) :
    gaussNormOf (normAbv L) (∑ b ∈ s, f b) ≤ r :=
  Finset.sum_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ r)
    (fun _ _ ha hb ↦ (gaussNorm_add_le _ _).trans (max_le ha hb))
    (by rw [gaussNormOf_zero]; exact hr) h

omit [IsUltrametricDist L] in

theorem gaussNorm_monomial_le {ι : Type*} (d : ι →₀ ℕ) (b : L) :
    gaussNormOf (normAbv L) (monomial d b) ≤ ‖b‖ := by
  classical
  refine gaussNormOf_le _ (norm_nonneg b) fun m ↦ ?_
  rw [coeff_monomial, normAbv_apply]
  split_ifs <;> simp

omit [IsUltrametricDist L] in

theorem gaussNorm_one {ι : Type*} : gaussNormOf (normAbv L) (1 : MvPolynomial ι L) = 1 := by
  rw [← C_1, gaussNormOf_C, normAbv_apply, norm_one]

theorem mul_le_one_of_gaussNorm {ι : Type*} {a b : MvPolynomial ι L}
    (ha : gaussNormOf (normAbv L) a ≤ 1) (hb : gaussNormOf (normAbv L) b ≤ 1) :
    gaussNormOf (normAbv L) (a * b) ≤ 1 :=
  (gaussNormOf_mul_le isNonarchimedean_normAbv a b).trans
    (mul_le_one₀ ha (gaussNormOf_nonneg _ b) hb)

theorem gaussNorm_prod_le_one {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L)
    (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ 1) :
    gaussNormOf (normAbv L) (∏ b ∈ s, f b) ≤ 1 :=
  Finset.prod_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ 1)
    (fun _ _ ha hb ↦ mul_le_one_of_gaussNorm ha hb) gaussNorm_one.le h

theorem gaussNorm_pow_le_one {ι : Type*} (f : MvPolynomial ι L)
    (h : gaussNormOf (normAbv L) f ≤ 1) (n : ℕ) : gaussNormOf (normAbv L) (f ^ n) ≤ 1 := by
  induction n with
  | zero => rw [pow_zero]; exact gaussNorm_one.le
  | succ n ih => rw [pow_succ]; exact mul_le_one_of_gaussNorm ih h

theorem gaussNorm_bind₁_le {ι κ : Type*} (f : ι → MvPolynomial κ L)
    (hf : ∀ i, gaussNormOf (normAbv L) (f i) ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (bind₁ f g) ≤ gaussNormOf (normAbv L) g := by
  conv_lhs => rw [g.as_sum, map_sum]
  refine gaussNorm_sum_le _ _ (gaussNormOf_nonneg _ g) fun m _ ↦ ?_
  rw [bind₁_monomial]
  refine (gaussNormOf_mul_le isNonarchimedean_normAbv _ _).trans ?_
  rw [gaussNormOf_C]
  have h1 := gaussNorm_prod_le_one m.support (fun i ↦ f i ^ m i)
    fun i _ ↦ gaussNorm_pow_le_one _ (hf i) _
  calc normAbv L (g.coeff m) * gaussNormOf (normAbv L) (∏ i ∈ m.support, f i ^ m i)
      ≤ normAbv L (g.coeff m) * 1 :=
        mul_le_mul_of_nonneg_left h1 ((normAbv L).nonneg _)
    _ ≤ gaussNormOf (normAbv L) g := by rw [mul_one]; exact le_gaussNormOf _ g m

theorem gaussNorm_linearForm_le {κ : Type*} [Fintype κ] (b : κ → L) (c : L)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    gaussNormOf (normAbv L) (∑ j, C (b j) * X j + C c : MvPolynomial κ L) ≤ 1 := by
  refine (gaussNorm_add_le _ _).trans (max_le ?_ ?_)
  · refine gaussNorm_sum_le _ _ zero_le_one fun j _ ↦ ?_
    rw [C_mul_X_eq_monomial]
    exact (gaussNorm_monomial_le _ _).trans (hb j)
  · rw [gaussNormOf_C, normAbv_apply]; exact hc

theorem gaussNorm_affineSubst_le {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g :=
  gaussNorm_bind₁_le _ (fun i ↦ gaussNorm_linearForm_le _ _ (hB i) (ha i)) g

omit [IsUltrametricDist L] in

theorem affineSubst_affineSubst {ι κ μ : Type*} [Fintype κ] [Fintype μ] (B : Matrix ι κ L)
    (a : ι → L) (B' : Matrix κ μ L) (a' : κ → L) (g : MvPolynomial ι L) :
    affineSubst B' a' (affineSubst B a g) = affineSubst (B * B') (B.mulVec a' + a) g := by
  have h : ∀ i, bind₁ (fun k ↦ ∑ l, C (B' k l) * X l + C (a' k))
      (∑ j, C (B i j) * X j + C (a i) : MvPolynomial κ L) =
      ∑ l, C ((B * B') i l) * X l + C ((B.mulVec a' + a) i) := by
    intro i
    simp only [map_add, map_sum, map_mul, bind₁_C_right, bind₁_X_right, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.add_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := μ))]
    ring
  unfold affineSubst
  rw [bind₁_bind₁]
  simp only [h]

omit [IsUltrametricDist L] in

theorem affineSubst_one_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι L) :
    affineSubst (1 : Matrix ι ι L) 0 g = g := by
  unfold affineSubst
  have : (fun i ↦ ∑ j, C ((1 : Matrix ι ι L) i j) * X j + C ((0 : ι → L) i)) =
      (X : ι → MvPolynomial ι L) := by
    funext i
    simp [Matrix.one_apply]
  rw [this, bind₁_X_left]
  rfl

theorem norm_sum_le_one {β : Type*} (s : Finset β) (f : β → L) (h : ∀ b ∈ s, ‖f b‖ ≤ 1) :
    ‖∑ b ∈ s, f b‖ ≤ 1 :=
  Finset.sum_induction f (fun x ↦ ‖x‖ ≤ 1)
    (fun _ _ ha hb ↦ (IsUltrametricDist.isNonarchimedean_norm _ _).trans (max_le ha hb))
    (by simp) h

end GaussNormBasic

open GaussNormBasic in

theorem GaussNormBasic.proof : GaussNormBasic.Statement := by
  intro L _ _ _
  refine ⟨fun ι g g' ↦ ⟨gaussNorm_add_le g g', gaussNormOf_mul_le isNonarchimedean_normAbv g g'⟩,
    fun ι κ _ B a hB ha g ↦ gaussNorm_affineSubst_le B a hB ha g, ?_, ?_⟩
  · intro ι _ _ B a hB ha hdet hinv g
    refine le_antisymm (gaussNorm_affineSubst_le B a hB ha g) ?_
    set a' : ι → L := -(B⁻¹.mulVec a)
    have ha' : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ by
      simp only [a', Pi.neg_apply, norm_neg, Matrix.mulVec, dotProduct]
      exact norm_sum_le_one _ _ fun j _ ↦ by
        rw [norm_mul]; exact mul_le_one₀ (hinv i j) (norm_nonneg _) (ha j)
    have hcomp : affineSubst B⁻¹ a' (affineSubst B a g) = g := by
      rw [affineSubst_affineSubst, Matrix.mul_nonsing_inv _ hdet]
      have : B.mulVec a' + a = 0 := by
        simp only [a', Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
          Matrix.one_mulVec, neg_add_cancel]
      rw [this, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst B⁻¹ a' (affineSubst B a g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ hinv ha' _
  · intro ι κ _ _ P hP hsurj g
    classical
    refine le_antisymm (gaussNorm_affineSubst_le P 0 hP (fun _ ↦ by simp) g) ?_
    choose x hx hPx using fun i : ι ↦ hsurj (Pi.single i 1) fun j ↦ by
      rw [Pi.single_apply]; split_ifs <;> simp
    let S : Matrix κ ι L := fun k i ↦ x i k
    have hPS : P * S = 1 := by
      ext j i
      have := congrFun (hPx i) j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [S, this, Pi.single_apply]
    have hcomp : affineSubst S 0 (affineSubst P 0 g) = g := by
      rw [affineSubst_affineSubst, hPS, Matrix.mulVec_zero, add_zero, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst S 0 (affineSubst P 0 g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ (fun k i ↦ hx i k) (fun _ ↦ by simp) _

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SchwartzZippelPerVariable.proof : SchwartzZippelPerVariable.Statement := by
  intro R _ _ _ q d S G hG hdeg
  have key := MvPolynomial.schwartz_zippel_sum_degreeOf hG (fun _ : Fin q ↦ S)
  have hsum : ∑ i : Fin q, ((G.degreeOf i : ℚ≥0) / (S.card : ℚ≥0)) ≤
      ∑ _i : Fin q, ((d : ℚ≥0) / (S.card : ℚ≥0)) :=
    Finset.sum_le_sum fun i _ ↦ by gcongr; exact_mod_cast hdeg i
  have key' := key.trans hsum
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    nsmul_eq_mul] at key'
  change ((((Fintype.piFinset fun _ : Fin q ↦ S).filter fun c ↦ eval c G = 0).card : ℕ) : ℚ≥0) /
    (S.card : ℚ≥0) ^ q ≤ (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) at key'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero,
      Nat.cast_eq_zero] at key'
    rw [key']
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos S.card with hs | hs
  · have : S = ∅ := Finset.card_eq_zero.mp hs
    subst this
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    simp [Fintype.piFinset_empty]
  have hs' : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hs
  have hpow : (S.card : ℚ≥0) ^ q = (S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (pow_pos hs' q), hpow] at key'
  have hcalc : (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) *
      ((S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1)) =
      (q : ℚ≥0) * d * (S.card : ℚ≥0) ^ (q - 1) := by
    field_simp
  rw [hcalc] at key'
  exact_mod_cast key'

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ComplexAt TensorProduct

noncomputable section

namespace HeightOfPointAlt

variable {K : Type*} [Field K] [NumberField K]

theorem adicAbv_sum_le (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem finite_adicAbv_ne_one {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  refine (hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  exact hv

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

omit [NumberField F] in

theorem adicAbv_intToField_le_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by
  let b : 𝓞 K := ⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩
  have hb : intToField F K a = algebraMap (𝓞 K) K b := rfl
  rw [hb]
  exact v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b

variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]

def archLinear (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[ℂ] ComplexAt (τ.comp (algebraMap F K)) where
  toFun := archFunctional τ yv
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z e =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply]
      simp only [archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
      exact smul_mul_assoc c z _
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem archDualNorm_pos (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by
  set σ := τ.comp (algebraMap F K)
  let φ : FibreSpace h σ →ₗ[ℂ] ℂ := (ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ
    (FibreSpace.equiv h σ).symm.toLinearMap
  have hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ)) :=
    fun _ => rfl
  let φc := LinearMap.toContinuousLinearMap φ
  have hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} =>
      ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖) := by
    refine ⟨‖φc‖, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    show ‖φ ξ‖ ≤ _
    calc ‖φ ξ‖ = ‖φc ξ‖ := rfl
      _ ≤ ‖φc‖ * ‖(ξ : FibreSpace h σ)‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * 1 := mul_le_mul_of_nonneg_left ξ.2 (norm_nonneg φc)
      _ = ‖φc‖ := mul_one _
  set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)
  have hξ₀ : φ ξ₀ = τ (yv x) := by
    rw [hφ]
    simp only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, one_mul]
    rfl
  have hne : ξ₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ₀
    exact (map_ne_zero τ).mpr hx hξ₀.symm
  set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀
  have hξ₁ : ‖ξ₁‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hne)
  have hφ₁ : φ ξ₁ ≠ 0 := by
    rw [map_smul, hξ₀, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)
    exact_mod_cast (norm_ne_zero_iff.mpr hne)
  calc (0 : ℝ) < ‖φ ξ₁‖ := norm_pos_iff.mpr hφ₁
    _ ≤ archDualNorm h τ yv := by
      rw [hφ]
      exact le_ciSup hbdd ⟨ξ₁, hξ₁⟩

end HeightOfPointAlt

open HeightOfPointAlt

theorem heightOfPoint : HeightOfPoint.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv
  have hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)
  have hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k) := by
    intro c
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef
  have hM0 : ∀ v, 0 ≤ M v := fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _
  have hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v := fun v k =>
    by
    show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))
    exact le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)))
      (Finite.bddAbove_range _) k
  have hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v := by
    intro v x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) :=
          mul_le_mul_of_nonneg_right (adicAbv_intToField_le_one v (c k)) (AbsoluteValue.nonneg _ _)
      _ ≤ M v := by rw [one_mul]; exact hleM v k
  have hdual : ∀ v, dualNormAt v yv = M v := by
    intro v
    have hbdd : BddAbove (Set.range fun x : W =>
        NumberField.HeightOneSpectrum.adicAbv K v (yv x)) := by
      refine ⟨M v, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle v x
    unfold dualNormAt
    refine le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_
    exact Real.iSup_le (fun k => le_ciSup hbdd (w k))
      (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)
  have hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v := by
    intro v
    rw [gaussNorm_eq_gaussNormOf]
    refine le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_
    · rw [coeff_sum]
      refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
      rw [coeff_C_mul, map_mul, coeff_X]
      split_ifs
      · rw [map_one, mul_one]; exact hleM v k
      · rw [map_zero, mul_zero]; exact hM0 v
    · refine Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)
      have hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) =
          yv (w k) := by
        rw [coeff_sum, Finset.sum_eq_single k]
        · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
          intro hjk
          exact hj (Finsupp.single_left_injective one_ne_zero hjk)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [← hc]
      exact le_gaussNormOf _ _ _

  obtain ⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hyv
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    simp [hcon]
  have hMpos : ∀ v, 0 < M v := fun v =>
    lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)
  have hMfin : (Function.support fun v => Real.log (M v)).Finite := by
    refine (Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0})
      fun k hk => finite_adicAbv_ne_one hk).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    have h1 : M v = 1 := by
      refine le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_
      · by_cases hk : yv (w k) = 0
        · rw [hk, map_zero]; exact zero_le_one
        · exact (hnot k hk).le
      · rw [← hnot k₀ hk₀]; exact hleM v k₀
    simp only [h1, Real.log_one]
  refine ⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩
  have hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite := by
    refine (finite_adicAbv_ne_one hx).subset ?_
    intro v hv h1
    apply hv
    simp only [h1, Real.log_one]
  have e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v) := by
    intro v
    rw [hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']
  have e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) =
      Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv) := by
    intro τ
    exact Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx))
      (archDualNorm_pos h τ yv x hx).ne'
  have e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) =
      ∑ᶠ v, Real.log (M v) := finsum_congr fun v => by rw [hdual]
  unfold heightWith
  simp only [e1, e2]
  rw [finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx,
    sum_log_norm_embeddings hx, e3]
  ring

theorem HeightOfPoint.proof (_h1 : GaussNormBasic.Statement) : HeightOfPoint.Statement :=
  heightOfPoint

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

namespace HeightOfCycle

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_iSup {ι : Type*} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {f : MvPolynomial ι K} (hf : f ≠ 0) (S : Finset (ι →₀ ℕ)) (hS : f.support ⊆ S) :
    gaussNorm v f = ⨆ m : S, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) := by
  have e : ∀ m, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) =
      NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m) := fun m ↦ by
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  simp_rw [e]
  obtain ⟨m, hm, hmax⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
  have : Nonempty S := ⟨⟨m, hS hm⟩⟩
  apply le_antisymm
  · rw [gaussNorm_eq_gaussNormOf, hmax]
    exact le_ciSup (f := fun m : S ↦ NumberField.HeightOneSpectrum.adicAbv K v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hS hm⟩
  · exact ciSup_le fun m ↦ le_gaussNormOf _ f m

theorem finsum_log_gaussNorm_map {E : Type*} [Field E] [NumberField E] [Algebra E K] {ι : Type*}
    {P : MvPolynomial ι E} (hP : P ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (P.map (algebraMap E K))) =
      Module.finrank E K *
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) := by
  have hPK : P.map (algebraMap E K) ≠ 0 :=
    fun h0 ↦ hP (MvPolynomial.map_injective _ (algebraMap E K).injective (by rw [h0, _root_.map_zero]))
  obtain ⟨m0, hm0⟩ := support_nonempty.mpr hP
  have hy : (fun m : P.support ↦ P.coeff m) ≠ 0 :=
    Function.ne_iff.mpr ⟨⟨m0, hm0⟩, mem_support_iff.mp hm0⟩
  have eK : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      gaussNorm v (P.map (algebraMap E K)) =
        ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (algebraMap E K (P.coeff m)) :=
    fun v ↦ by
      rw [gaussNorm_eq_iSup v hPK P.support (support_map_subset _ _)]
      simp_rw [coeff_map]
  have eE : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      gaussNorm v P = ⨆ m : P.support, FinitePlace.equivHeightOneSpectrum.symm v (P.coeff m) :=
    fun v ↦ gaussNorm_eq_iSup v hP P.support subset_rfl
  simp_rw [eK, eE]
  rw [finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace K ↦ Real.log (⨆ m : P.support, w (algebraMap E K (P.coeff m)))),
    finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace E ↦ Real.log (⨆ m : P.support, w (P.coeff m)))]
  exact finsum_log_iSup_algebraMap hy

theorem finsum_log_gaussNorm_prod {ι α : Type*} (s : Finset α) (L : α → MvPolynomial ι K)
    (hL : ∀ q, L q ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (∏ q ∈ s, L q)) =
      ∑ q ∈ s, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (L q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1]
    simp_rw [gaussNorm_C, map_one, Real.log_one, finsum_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, finsum_log_gaussNorm_mul (hL a)
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q), ih, Finset.sum_insert ha]

end HeightOfCycle

open HeightOfCycle in

theorem HeightOfCycle.proof (h1 : HeightOfPoint.Statement) (h2 : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement := by
  intro F _ _ W _ _ _ _ h n w hw E _ _ _ K _ _ _ _ _ m yv hyv c hc P hP

  have hL : ∀ q, (∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 := by
    intro q h0
    apply hyv q
    have hle : Submodule.span (𝓞 F) (Set.range w) ≤ LinearMap.ker (yv q) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrArg (coeff (Finsupp.single k 1)) h0
      simp only [coeff_sum, coeff_C_mul, coeff_X, coeff_zero] at this
      rw [Finset.sum_eq_single k (fun j _ hj ↦ by
        rw [if_neg (fun e ↦ hj (Finsupp.single_left_injective one_ne_zero e)), mul_zero])
        (by simp)] at this
      simpa using this
    rw [hw, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle
  have hprod : (∏ q, ∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc) hprod hP.symm
  have hr : (Module.finrank E K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

  have hpt : ∀ q, pointHeight h (yv q) = (Module.finrank ℚ K : ℝ)⁻¹ *
      ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) +
        ∑ τ : K →+* ℂ, Real.log (archDualNorm h τ (yv q))) := by
    intro q
    obtain ⟨hloc, hht⟩ := h1 F W h n w hw K (yv q) (hyv q)
    have hex : ∃ x, yv q x ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hyv q (LinearMap.ext hne)
    rw [pointHeight, hht _ (Classical.epsilon_spec hex)]
    congr 2
    exact finsum_congr fun v ↦ by rw [(hloc v).2]

  have hfin : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) =
      (Module.finrank E K : ℝ)⁻¹ *
        ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (NumberField.HeightOneSpectrum.adicAbv K v c)) +
          ∑ q, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← finsum_log_gaussNorm_map hPne, hP,
      finsum_log_gaussNorm_mul (C_ne_zero.mpr hc) hprod,
      finsum_log_gaussNorm_prod Finset.univ (fun q ↦ ∑ k, C (yv q (w k)) * X k) hL]
    simp_rw [gaussNorm_C]

  have harch : ∑ σ : E →+* ℂ, (fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2) =
      (Module.finrank E K : ℝ)⁻¹ * ∑ τ : K →+* ℂ,
        (Real.log ‖τ c‖ + ∑ q, Real.log (archDualNorm h τ (yv q))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← sum_embeddings_restrict (K := E) (L := K)
      (fun σ : E →+* ℂ ↦ fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    have e1 : (τ.comp (algebraMap E K)).comp (algebraMap F E) = τ.comp (algebraMap F K) := by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have e2 : P.map (τ.comp (algebraMap E K)) =
        C (τ c) * ∏ q, ∑ k, C (τ (yv q (w k))) * X k := by
      rw [← MvPolynomial.map_map, hP]
      simp only [map_mul, map_prod, map_sum, map_C, map_X]
    rw [e1, e2, h2 F W h n w hw K τ m yv hyv (τ c) ((map_ne_zero τ).mpr hc)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hfin, harch, Finset.sum_add_distrib, finsum_log_adicAbv hc, sum_log_norm_embeddings hc,
    Finset.sum_comm (f := fun τ q ↦ Real.log (archDualNorm h τ (yv q)))]
  simp_rw [hpt]
  rw [← Module.finrank_mul_finrank ℚ E K, ← Finset.mul_sum, Finset.sum_add_distrib]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawUnitary

def rowMap {N : ℕ} (k : ℕ) (U : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :
    (Fin k × Fin N → ℂ) →ₗ[ℝ] (Fin k × Fin N → ℂ) where
  toFun u ij := U (fun j ↦ u (ij.1, j)) ij.2
  map_add' u v := by
    funext ij
    have : (fun j ↦ (u + v) (ij.1, j)) = (fun j ↦ u (ij.1, j)) + fun j ↦ v (ij.1, j) := rfl
    change U (fun j ↦ (u + v) (ij.1, j)) ij.2 =
      U (fun j ↦ u (ij.1, j)) ij.2 + U (fun j ↦ v (ij.1, j)) ij.2
    rw [this, map_add]
    rfl
  map_smul' r u := by
    funext ij
    have : (fun j ↦ (r • u) (ij.1, j)) = (r : ℂ) • fun j ↦ u (ij.1, j) := by
      funext j; simp [Complex.real_smul]
    change U (fun j ↦ (r • u) (ij.1, j)) ij.2 = r • U (fun j ↦ u (ij.1, j)) ij.2
    rw [this, map_smul]
    simp [Complex.real_smul]

theorem proof : SphereLawUnitary.Statement := by
  intro N U hU
  set B := sphereBall (HermNorm.std N) 1 with hBdef
  set g : (Fin 1 × Fin N → ℂ) → (Fin N → ℂ) :=
    fun u j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j) with hgdef
  set V := rowMap 1 U with hVdef
  have hrow : ∀ u i, (fun j ↦ V u (i, j)) = U (fun j ↦ u (i, j)) := fun _ _ ↦ rfl
  have hnorm : ∀ v, (HermNorm.std N).norm (U v) = (HermNorm.std N).norm v := by
    intro v; simp only [HermNorm.std_norm_eq, hU]
  have hBm : MeasurableSet B := (isOpen_sphereBall_std N).measurableSet
  have hVm : Measurable V := V.continuous_of_finiteDimensional.measurable
  have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
  have hgm : Measurable g := by
    simp only [hgdef, sphereNormalize, HermNorm.std_norm_eq]
    fun_prop
  have hpre : V ⁻¹' B = B := by
    ext u
    simp only [Set.mem_preimage, hBdef, sphereBall, Set.mem_ofPred_eq, hrow, hnorm]
  have hcomm : U ∘ g = g ∘ V := by
    funext u
    have hg : ∀ w, g w = (((HermNorm.std N).norm fun j ↦ w (0, j) : ℝ) : ℂ)⁻¹ •
        fun j ↦ w (0, j) := fun w ↦ by
      funext j; simp [hgdef, sphereNormalize]
    simp only [Function.comp_apply, hg, map_smul, hrow, hnorm]
  have hinj : Function.Injective V := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext ij
    have h1 : U (fun j ↦ u (ij.1, j)) = 0 := by rw [← hrow, hu]; rfl
    have h2 := hU (fun j ↦ u (ij.1, j))
    rw [h1] at h2
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h2
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)).mp h2.symm ij.2
      (Finset.mem_univ _)
    simpa using this
  have hdet : LinearMap.det V ≠ 0 := by
    have h := (LinearEquiv.ofInjectiveEndo V hinj).isUnit_det'
    have e : ((LinearEquiv.ofInjectiveEndo V hinj : _ ≃ₗ[ℝ] _) : _ →ₗ[ℝ] _) = V :=
      LinearMap.ext fun x ↦ by simp [LinearEquiv.coe_ofInjectiveEndo]
    rw [e] at h
    exact h.ne_zero
  have h0 : volume B ≠ 0 := by
    refine ((isOpen_sphereBall_std N).measure_pos volume ⟨0, ?_⟩).ne'
    simp [sphereBall, HermNorm.std_norm_eq]
  have htop : volume B ≠ ⊤ :=
    ((measure_mono (sphereBall_std_subset N)).trans_lt
      (isCompact_closedBall 0 1).measure_lt_top).ne
  have hvol : Measure.map V volume = (volume : Measure (Fin 1 × Fin N → ℂ)) := by
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin 1 × Fin N → ℂ)) hdet
    have hc : ENNReal.ofReal |(LinearMap.det V)⁻¹| = 1 := by
      have hB := congrArg (fun μ : Measure (Fin 1 × Fin N → ℂ) ↦ μ B) hmap
      simp only [Measure.map_apply hVm hBm, hpre, Measure.smul_apply, smul_eq_mul] at hB
      have : 1 * volume B = ENNReal.ofReal |(LinearMap.det V)⁻¹| * volume B := by
        rw [one_mul]; exact hB
      exact ((ENNReal.mul_left_inj h0 htop).mp this).symm
    rw [hmap, hc, one_smul]
  have hcond : Measure.map V (volume[|B]) = volume[|B] := by
    rw [ProbabilityTheory.cond, Measure.map_smul, ← hpre, ← Measure.restrict_map hVm hBm,
      hvol, hpre]
  show Measure.map U (Measure.map g (volume[|B])) = Measure.map g (volume[|B])
  rw [Measure.map_map hUm hgm, hcomm, ← Measure.map_map hgm hVm, hcond]

end SphereLawUnitary

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereProjectionLaw

variable {n : ℕ}

theorem ofReal_norm_sq (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ofReal_sum_norm_sq (v : Fin n → ℂ) :
    ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = ∑ j, v j * star (v j) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ ↦ ofReal_norm_sq (v j)

theorem coordAlong_smul (p w : Fin n → ℂ) (c : ℂ) :
    coordAlong p (c • w) = c * coordAlong p w := by
  simp [coordAlong, Finset.mul_sum, mul_assoc]

theorem coordAlong_sub (p z w : Fin n → ℂ) :
    coordAlong p (z - w) = coordAlong p z - coordAlong p w := by
  simp [coordAlong, sub_mul, Finset.sum_sub_distrib]

theorem coordAlong_self {p : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) : coordAlong p p = 1 := by
  rw [coordAlong, ← ofReal_sum_norm_sq, hp, Complex.ofReal_one]

theorem std_norm (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem sum_norm_sq_smul (c : ℂ) (w : Fin n → ℂ) :
    ∑ j, ‖(c • w) j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

theorem sum_norm_sq_sub {p z : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ∑ j, ‖(z - coordAlong p z • p) j‖ ^ 2 = 1 - ‖coordAlong p z‖ ^ 2 := by
  apply Complex.ofReal_injective
  set a := coordAlong p z with ha
  have hzp : ∑ j, p j * star (z j) = star a := by
    simp [ha, coordAlong, star_sum, mul_comm]
  have hpp : ∑ j, p j * star (p j) = 1 := by rw [← ofReal_sum_norm_sq, hp, Complex.ofReal_one]
  have hzz : ∑ j, z j * star (z j) = 1 := by rw [← ofReal_sum_norm_sq, hz, Complex.ofReal_one]
  have key : ∀ j, (z - a • p) j * star ((z - a • p) j) =
      z j * star (z j) - star a * (z j * star (p j)) - a * (p j * star (z j)) +
        a * star a * (p j * star (p j)) := by
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
    ring
  rw [ofReal_sum_norm_sq, Finset.sum_congr rfl fun j _ ↦ key j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hzp, hpp, hzz, ← coordAlong, ← ha, Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_norm_sq]
  ring

theorem exists_unitary_first {m : ℕ} (p : Fin (m + 1) → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    ∃ U : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) ∧ ∀ v, U v 0 = coordAlong p v := by
  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (Set.mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  have hUapp : ∀ v, Ulin v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v ↦ rfl
  refine ⟨Ulin.toLinearMap, fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
    simpa [hUapp] using h2
  · rw [LinearEquiv.coe_coe, hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply, coordAlong]

theorem span_singleton_ne_top {N : ℕ} (hN : 2 ≤ N) (p : Fin N → ℂ) :
    Submodule.span ℂ {p} ≠ ⊤ := by
  intro h
  have h1 := finrank_span_le_card (R := ℂ) ({p} : Set (Fin N → ℂ))
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega

end SphereProjectionLaw

open SphereProjectionLaw in

theorem SphereProjectionLaw.proof (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement)
    (h3 : SphereLawFirstCoord.Statement) (h4 : SpherePhase.Statement) :
    SphereProjectionLaw.Statement := by
  intro N p hp
  refine ⟨fun hN ↦ ?_, fun hN ↦ ⟨?_, h4 N p hp hN, ?_⟩⟩
  ·
    subst hN
    filter_upwards [(h1 1 le_rfl).2.1] with z hz
    simp only [Fin.sum_univ_one] at hz hp
    have hz1 : ‖z 0‖ = 1 := by nlinarith [norm_nonneg (z 0)]
    have hp1 : ‖p 0‖ = 1 := by nlinarith [norm_nonneg (p 0)]
    simp [coordAlong, hz1, hp1]
  ·
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      ((h1 N (by omega)).2.2 _ (span_singleton_ne_top hN p))
    filter_upwards [(h1 N (by omega)).2.1, hnull] with z hz hzS
    set a := coordAlong p z with ha
    set w := z - a • p with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply hzS
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, (sub_eq_zero.mp h).symm⟩
    have hsq : ∑ j, ‖w j‖ ^ 2 = 1 - ‖a‖ ^ 2 := sum_norm_sq_sub hp hz
    have hpos : 0 < ∑ j, ‖w j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
      calc (0 : ℝ) < ‖w j‖ ^ 2 := by positivity
        _ ≤ ∑ j, ‖w j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j ↦ ‖w j‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    set s := √(1 - ‖a‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (hsq ▸ hpos)
    have hss : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (hsq ▸ hpos.le)
    have hdir : orthoDir p z = ((s : ℂ))⁻¹ • w := by
      rw [orthoDir, std_norm, ← ha, ← hw, hsq]
    have hwp : coordAlong p w = 0 := by
      rw [hw, coordAlong_sub, coordAlong_smul, coordAlong_self hp, mul_one, sub_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdir, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs0.ne'), one_smul, hw,
        add_sub_cancel]
    · rw [hdir, coordAlong_smul, hwp, mul_zero]
    · rw [hdir, std_norm, sum_norm_sq_smul, hsq, ← hss, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs0.le, inv_pow, inv_mul_cancel₀ (pow_pos hs0 2).ne', Real.sqrt_one]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    obtain ⟨U, hU, hU0⟩ := exists_unitary_first p hp
    have hf : (fun z ↦ ‖coordAlong p z‖ ^ 2) =
        (fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2) ∘ U := by
      funext z
      simp [hU0]
    have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
    have hgm : Measurable fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2 :=
      ((continuous_apply _).norm.pow 2).measurable
    rw [hf, ← Measure.map_map hgm hUm, h2 _ U hU, h3 _ hN]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

namespace LatticeLemmas

theorem BaseChange.full : BaseChange.Statement := BaseChange.proof

theorem Sublattice.full : Sublattice.Statement := Sublattice.proof

theorem LatticeOfLocalisations.full : LatticeOfLocalisations.Statement :=
  LatticeOfLocalisations.proof

theorem LocalChange.full_of_localIndex (h : LocalIndex.Statement.{u, v}) :
    LocalChange.Statement.{u, v} :=
  LocalChange.proof Sublattice.full h

theorem NormComparison.full : NormComparison.Statement := NormComparison.proof

theorem DiagonalChange.full : DiagonalChange.Statement := DiagonalChange.proof

theorem ExactSequence.full : ExactSequence.Statement := ExactSequence.proof

theorem ChainSum.full : ChainSum.Statement.{u, v} := ChainSum.proof ExactSequence.full

theorem Hadamard.full : Hadamard.Statement.{u, v, w} := Hadamard.proof Sublattice.full

theorem HadamardQuotient.full : HadamardQuotient.Statement.{u, v, w} :=
  HadamardQuotient.proof Hadamard.full

theorem HadamardMean.full : HadamardMean.Statement.{u, v, w} := HadamardMean.intersectionNumber_baseChange

theorem HadamardMeanQuotient.full : HadamardMeanQuotient.Statement.{u, v, w} :=
  HadamardMeanQuotient.proof HadamardMean.full

end LatticeLemmas

theorem GaussNormBasic.full : GaussNormBasic.Statement := GaussNormBasic.proof

theorem SchwartzZippelPerVariable.full : SchwartzZippelPerVariable.Statement :=
  SchwartzZippelPerVariable.proof

theorem RootsOfUnityValuation.full : RootsOfUnityValuation.Statement :=
  RootsOfUnityValuation.proof

theorem HeightOfPoint.full : HeightOfPoint.Statement := HeightOfPoint.proof GaussNormBasic.full

theorem HeightOfCycle.full_of_fibreMahlerForms (h : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement :=
  HeightOfCycle.proof HeightOfPoint.full h

theorem SphereLawUnitary.full : SphereLawUnitary.Statement := SphereLawUnitary.proof

theorem SpherePhase.full_of_sphereLawBasic (hb : SphereLawBasic.Statement) :
    SpherePhase.Statement :=
  SpherePhase.proof hb SphereLawUnitary.full

theorem SphereProjectionLaw.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.proof hb SphereLawUnitary.full hc (SpherePhase.full_of_sphereLawBasic hb)

theorem PointwiseLelong.full_of (hb : SphereLawBasic.Statement)
    (hc : SphereLawFirstCoord.Statement) : PointwiseLelong.Statement :=
  PointwiseLelong.proof (SphereProjectionLaw.full_of hb hc)

end GroundTheory.Heights₂.Heights
end
