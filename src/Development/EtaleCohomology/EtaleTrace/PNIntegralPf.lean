import Development.EtaleCohomology.EtaleTrace.LCoverCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem pn_sep (k : Type) [Field k] (d : ℕ) : IsSeparated (PNto k d) := by
  unfold PNto; infer_instance

theorem algebraMap_field_homogeneousDegreeZero_surjective (k : Type) [Field k] (d : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨MvPolynomial.coeff 0 x, ?_⟩
  apply Subtype.ext
  have h0 := (MvPolynomial.mem_homogeneousSubmodule 0 x).1 hx
  have h : x = C (coeff 0 x) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 h0)
  show (algebraMap k (MvPolynomial (Fin (d + 1)) k)) (coeff 0 x) = x
  conv_rhs => rw [h]
  rfl

instance ft0 (k : Type) [Field k] (d : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
    exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k _ _

theorem pn_lft (k : Type) [Field k] (d : ℕ) : LocallyOfFiniteType (PNto k d) := by
  unfold PNto
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (algebraMap_field_homogeneousDegreeZero_surjective k d)
  infer_instance

def PNIntegral : Prop := ∀ (k : Type) [Field k] (d : ℕ), IsIntegral (PN k d)

theorem PNBasic_of (h : PNIntegral) : PNBasic := fun k _ d => ⟨h k d, pn_sep k d, pn_lft k d⟩

end LateralTheory.EtaleTrace.Cov
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
end
end
