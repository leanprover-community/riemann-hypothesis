import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthMapEqLogOrdFracDet

section
universe u_1 u_2

namespace GlobalTheory.LengthDualFunctional

open Module

theorem exists_dual_ne_zero_comp_eq_zero {R : Type u_1} [CommRing R] [IsDomain R]
    {M : Type u_2} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : LinearMap.det f = 0) :
    ∃ φ : Module.Dual R M, φ ≠ 0 ∧ φ ∘ₗ f = 0 := by
  have hd : LinearMap.det f.dualMap = 0 := by
    rw [LinearMap.det_dualMap]; exact h
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.bot_lt_ker_of_det_eq_zero hd).ne'
  exact ⟨φ, hφ0, by simpa [LinearMap.dualMap_apply'] using hφ⟩

theorem length_self_eq_top (R : Type u_1) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Module.length R R = ⊤ := by
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨_, hA⟩ := hne
  haveI : IsArtinianRing R := hA
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem main : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [Module.Free R M] [Module.Finite R M] {f : M →ₗ[R] M}, (LinearMap.det : (M →ₗ[R] M) → R) f = (0 : R) → Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  intro R _ _ _ M _ _ _ _ f h
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_ne_zero_comp_eq_zero h
  obtain ⟨m, hm⟩ : ∃ m, φ m ≠ 0 := by
    by_contra hc; push_neg at hc; exact hφ0 (LinearMap.ext hc)
  have hle : LinearMap.range f ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    simpa using congrArg (fun g => g x) hφ
  let ψ := (LinearMap.range f).liftQ φ hle
  let g : R →ₗ[R] M ⧸ LinearMap.range f := LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk m)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have := congrArg ψ hr
    simp [g, ψ] at this
    tauto
  have := Module.length_le_of_injective g hg
  rw [length_self_eq_top] at this
  exact top_le_iff.mp this

end GlobalTheory.LengthDualFunctional
end

section
universe u_1 u_2

namespace GlobalTheory.LengthQuotientValuationDet

open Module IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

theorem length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

theorem length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end GlobalTheory.LengthQuotientValuationDet
end

section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.LengthQuotientSpanValuation

open Module

section

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma length_quot_span (x : R) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x :=
  Ring.ord_eq_addVal x

lemma length_self_eq_top : Module.length R R = ⊤ := by
  rw [← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

end

theorem main {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by
  set A := LinearMap.toMatrix b' b f with hA
  by_cases hf : Function.Injective f
  · set N := LinearMap.range f with hN
    let e₀ : M' ≃ₗ[R] N := LinearEquiv.ofInjective f hf
    have h : Module.finrank R N = Module.finrank R M := by
      rw [← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
    let a := Submodule.smithNormalFormCoeffs b h
    let bT := Submodule.smithNormalFormTopBasis b h
    let bB := Submodule.smithNormalFormBotBasis b h
    have ab_eq := Submodule.smithNormalFormBotBasis_def b h

    have hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i) := by
      rw [(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype,
        addVal_prod]
      exact Finset.sum_congr rfl fun i _ => length_quot_span _
    rw [hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]

    let φ : M' ≃ₗ[R] M := b'.equiv b (Equiv.refl ι)
    have hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N)) := by
      rw [← LinearMap.det_toMatrix b]
      congr 1
      ext i j
      simp [hA, LinearMap.toMatrix_apply, φ, e₀]
      rfl
    let e' : M ≃ₗ[R] N := bT.equiv bB (Equiv.refl ι)
    have hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i := by
      intro i
      simp [e', Basis.equiv_apply, bB, bT, a, ab_eq]
    have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hdetA, ← hdiag]
    exact LinearMap.associated_det_comp_equiv _ _ _
  · have hdet : A.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
        simpa [Function.Injective] using hf
      refine ⟨b'.repr (x - y), ?_, ?_⟩
      · intro h
        apply hne
        rw [← sub_eq_zero]
        apply b'.repr.injective
        rw [map_zero]
        exact Finsupp.ext fun i => by simpa using congrFun h i
      · rw [hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
        rfl
    rw [hdet, IsDiscreteValuationRing.addVal_zero]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    let φ : M →ₗ[R] R := ∑ i, w i • b.coord i
    have hφ : ∀ x, φ x = ∑ i, w i * b.repr x i := by
      intro x
      simp [φ]
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rw [LinearMap.range_le_ker_iff]
      refine b'.ext fun j => ?_
      have := congrFun hw j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    let ψ := (LinearMap.range f).liftQ φ hle
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    have hmem : (R ∙ w i) ≤ LinearMap.range ψ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨Submodule.Quotient.mk (b i), ?_⟩
      simp [ψ, hφ, Finsupp.single_apply]
    have h1 : Module.length R (R ∙ w i) = ⊤ := by
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]
    have h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ) :=
      Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)
    have h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f) :=
      Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
    rw [← top_le_iff, ← h1]
    exact h2.trans h3

end GlobalTheory.LengthQuotientSpanValuation
end

section
universe u_1 u_2 u_3

namespace GlobalTheory.LatticeLinearEquivBasis

open Module

theorem span_range_basis_coe {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by
  have h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_linearEquiv_map_lattice_eq : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] (K : Type u_2) [inst_3 : Field K] [inst_4 : Algebra R K] [IsFractionRing R K] {V : Type u_3} [inst_6 : AddCommGroup V] [inst_7 : Module K V] [inst_8 : Module R V] [inst_9 : IsScalarTower R K V] (A B : Submodule R V) [Submodule.IsLattice K A] [Submodule.IsLattice K B], Exists fun (g : LinearEquiv (RingHom.id K) V V) ↦ Eq (Submodule.map (LinearMap.restrictScalars R (LinearEquiv.toLinearMap g)) A) B := by
  intro R _ _ _ K _ _ _ V _ _ _ _ A B _ _
  let bA := Free.chooseBasis R A
  let bB := Free.chooseBasis R B
  let eA := bA.extendOfIsLattice K
  let eB := bB.extendOfIsLattice K
  let e := eA.indexEquiv eB
  refine ⟨eA.equiv eB e, ?_⟩
  have hA := span_range_basis_coe A bA
  have hB := span_range_basis_coe B bB
  suffices h : Submodule.map ((eA.equiv eB e : V ≃ₗ[K] V).toLinearMap.restrictScalars R)
      (Submodule.span R (Set.range fun i => (bA i : V))) =
      Submodule.span R (Set.range fun j => (bB j : V)) by
    rw [hA, hB] at h; exact h
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨e i, ?_⟩
    have h1 : (bA i : V) = eA i := (bA.extendOfIsLattice_apply K i).symm
    have h2 : (bB (e i) : V) = eB (e i) := (bB.extendOfIsLattice_apply K (e i)).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply]
  · rintro ⟨j, rfl⟩
    refine ⟨(bA (e.symm j) : V), ⟨e.symm j, rfl⟩, ?_⟩
    have h1 : (bA (e.symm j) : V) = eA (e.symm j) := (bA.extendOfIsLattice_apply K _).symm
    have h2 : (bB j : V) = eB j := (bB.extendOfIsLattice_apply K j).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply, Equiv.apply_symm_apply]

end GlobalTheory.LatticeLinearEquivBasis
end

section
universe u_1 u_2

namespace GlobalTheory.RelativeLengthAdditivity

open GlobalTheory

section
variable {S : Type u_1} {V : Type u_2} [Ring S] [AddCommGroup V] [Module S V]

theorem relLength_bot_add {A D : Submodule S V} (h : D ≤ A) :
    relLength A ⊥ = relLength A D + relLength D ⊥ := by
  let N : Submodule S A := D.submoduleOf A
  have hex := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length S N = relLength D ⊥ := by
    have := relLength_submoduleOf h (⊥ : Submodule S V)
    have hb : (⊥ : Submodule S V).submoduleOf A = ⊥ := by
      ext x; simp [Submodule.submoduleOf]
    rw [hb, relLength_bot_right] at this
    exact this
  rw [relLength_bot_right, hex, hN, add_comm]
  rfl

theorem relLength_add {A C D : Submodule S V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hb : C.map C.mkQ = ⊥ := Submodule.mkQ_map_self C
  rw [← relLength_map_mkQ le_rfl A, ← relLength_map_mkQ hCD A, ← relLength_map_mkQ le_rfl D, hb]
  exact relLength_bot_add (Submodule.map_mono hDA)

theorem signedLength_of_common_lower : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V]
    [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ},
    GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) →
    GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := by
  intro S V _ _ _ A B C hCA hCB m n hm hn
  have hCD : C ≤ A ⊓ B := le_inf hCA hCB
  have h1 := relLength_add hCD (inf_le_left : A ⊓ B ≤ A)
  have h2 := relLength_add hCD (inf_le_right : A ⊓ B ≤ B)
  rw [relLength_inf_right] at h1
  rw [relLength_inf_right'] at h2
  rw [hm] at h1
  rw [hn] at h2
  have ha : relLength A B ≠ ⊤ := fun h => by simp [h] at h1
  have hb : relLength B A ≠ ⊤ := fun h => by simp [h] at h2
  have hk : relLength (A ⊓ B) C ≠ ⊤ := fun h => by simp [h] at h1
  refine ⟨⟨ha, hb⟩, ?_⟩
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.mp hb
  obtain ⟨k, hk'⟩ := ENat.ne_top_iff_exists.mp hk
  rw [← ha', ← hk'] at h1
  rw [← hb', ← hk'] at h2
  have e1 : m = a + k := by exact_mod_cast h1
  have e2 : n = b + k := by exact_mod_cast h2
  rw [signedLength_eq_of_relLength_eq ha'.symm hb'.symm, e1, e2]
  push_cast
  ring
end

end GlobalTheory.RelativeLengthAdditivity

example : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V] [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ}, GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) → GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := @GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower
end

section
namespace GlobalTheory.RelativeLengthSpanDet

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

theorem addVal_prod (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  have : IsArtinianRing R := h.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem length_coker_of_det_eq_zero (P : Matrix ι ι R) (h : P.det = 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = ⊤ := by
  obtain ⟨w, hw, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  have hk' : w k ≠ 0 := hk
  let g : R →ₗ[R] (ι → R) ⧸ LinearMap.range P.mulVecLin :=
    (LinearMap.range P.mulVecLin).mkQ ∘ₗ LinearMap.single R (fun _ : ι => R) k
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have hr' : (Pi.single k r : ι → R) ∈ LinearMap.range P.mulVecLin :=
      (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨x, hx⟩ := hr'
    have h1 : w ⬝ᵥ P.mulVec x = 0 := by
      rw [Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, dotProduct_single] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  exact top_le_iff.mp (length_self_eq_top (R := R) ▸ Module.length_le_of_injective g hg)

theorem length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]

theorem length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']

theorem relLength_span_eq_addVal_det {V : Type*} [AddCommGroup V] [Module R V] {a v : ι → V}
    (ha : LinearIndependent R a) (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by
  have hinj : Function.Injective (Fintype.linearCombination R a) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by rwa [Fintype.linearCombination_apply] at hx) i
  have hA : Submodule.span R (Set.range a) =
      (⊤ : Submodule R (ι → R)).map (Fintype.linearCombination R a) := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hcomp : Fintype.linearCombination R a ∘ₗ P.mulVecLin = Fintype.linearCombination R v := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simp [Fintype.linearCombination_apply, hv, Pi.single_apply]
  have hB : Submodule.span R (Set.range v) =
      (LinearMap.range P.mulVecLin).map (Fintype.linearCombination R a) := by
    rw [← LinearMap.range_comp, hcomp, Fintype.range_linearCombination]
  rw [hA, hB, relLength_map_of_injective _ hinj, relLength_top_left, length_coker]

universe u_1 u_2 u_3 in

theorem relLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {V : Type u_2} [AddCommGroup V] [Module R V] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {a v : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R)
    (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      (addVal R : R → ℕ∞) P.det :=
  relLength_span_eq_addVal_det ha P hv

end GlobalTheory.RelativeLengthSpanDet
end

section
universe u_1 u_2

namespace GlobalTheory.LengthCokernelInjective

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h : Ring.ord R (0 : R) = ⊤ := by rw [Ring.ord_eq_addVal]; simp
  have h2 : Ring.ord R (0 : R) ≤ Module.length R R :=
    Module.length_le_of_surjective (Ideal.span {(0 : R)}).mkQ (Submodule.mkQ_surjective _)
  rw [h] at h2
  exact top_le_iff.mp h2

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem length_coker_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  let a := Submodule.smithNormalFormCoeffs b h
  let t := Submodule.smithNormalFormTopBasis b h
  let s := Submodule.smithNormalFormBotBasis b h
  have hs : ∀ i, (s i : M) = a i • t i := Submodule.smithNormalFormBotBasis_def b h
  have h1 : Associated
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap))
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap)) :=
    LinearMap.associated_det_comp_equiv _ _ _
  have h2 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  have h3 : (LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap =
      Matrix.toLin t t (Matrix.diagonal a) := by
    refine t.ext fun i => ?_
    simp [hs, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [h2, h3, LinearMap.det_toLin, Matrix.det_diagonal] at h1
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr h1, addVal_finset_prod,
    (Submodule.quotientEquivPiSpan (LinearMap.range f) b h).length_eq,
    Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)

theorem length_coker_of_not_injective (f : M →ₗ[R] M) (hf : LinearMap.ker f ≠ ⊥) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 : Module.finrank R (LinearMap.ker f) ≠ 0 := by
    rwa [ne_eq, Submodule.finrank_eq_zero]
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [f.quotKerEquivRange.finrank_eq] at h2
  have h4 : Module.finrank R (M ⧸ LinearMap.range f) ≠ 0 := by omega
  rw [ne_eq, Module.finrank_eq_zero_iff] at h4
  push Not at h4
  obtain ⟨x, hx⟩ := h4
  have h5 : Function.Injective (LinearMap.toSpanSingleton R _ x) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    exact hx r h0 hr
  have h6 := Module.length_le_of_injective _ h5
  rw [length_self_eq_top] at h6
  exact top_le_iff.mp h6

theorem length_coker (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.ker f = ⊥
  · exact length_coker_of_injective f (LinearMap.ker_eq_bot.mp hf)
  · rw [length_coker_of_not_injective f hf, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf]
    simp


end GlobalTheory.LengthCokernelInjective
end

section
namespace GlobalTheory.SignedLengthOrdFracDet

open Module Submodule

theorem ord_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι) (c : ι → R)
    (hc : ∀ i, c i ≠ 0) : Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]

theorem length_coker {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e₀ : Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  have : Module.Finite R M := Module.Finite.of_basis e₀
  have : Module.Free R M := Module.Free.of_basis e₀
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := smithNormalFormCoeffs e₀ h
  let t := smithNormalFormTopBasis e₀ h
  let u := smithNormalFormBotBasis e₀ h
  let e' : M ≃ₗ[R] N := t.equiv u (Equiv.refl _)
  have h1 : Associated (LinearMap.det f) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have h2 : LinearMap.toMatrix t t (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal c := by
    ext i j
    have hj : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e', Basis.equiv_apply,
        Equiv.refl_apply]
      exact smithNormalFormBotBasis_def e₀ h j
    rw [LinearMap.toMatrix_apply, hj, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [Ring.ord_eq_of_associated h1, ← LinearMap.det_toMatrix t, h2, Matrix.det_diagonal,
    ord_prod _ _ (smithNormalFormCoeffs_ne_zero e₀ h),
    (quotientEquivPiSpan N e₀ h).length_eq, Module.length_pi_of_fintype]
  rfl

theorem relLength_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hD : D ≤ A) (hC : C ≤ D) :
    relLength A C = relLength A D + relLength D C := by
  rw [relLength_eq_length_map_mkQ A C, relLength_eq_length_map_mkQ D C,
    ← relLength_map_mkQ hC A, add_comm]
  have hle : D.map C.mkQ ≤ A.map C.mkQ := Submodule.map_mono hD
  rw [relLength_def, ← (Submodule.submoduleOfEquivOfLe hle).length_eq]
  exact Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.mkQ _)
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

theorem signedLength_of_common {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ} (hm : relLength A C = m)
    (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  have h1 := relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB)
  have h2 := relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB)
  rw [relLength_inf_right, hm] at h1
  rw [relLength_inf_right', hn] at h2
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = z at *
  cases x with
  | top => simp at h1
  | coe x =>
  cases y with
  | top => simp at h2
  | coe y =>
  cases z with
  | top => simp at h2
  | coe z =>
  norm_cast at h1 h2
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  simp only [ENat.toNat_natCast]
  omega



end GlobalTheory.SignedLengthOrdFracDet
end

section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthTower

theorem relLength_tower {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength B C + relLength A B := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  rw [← relLength_submoduleOf hBA C, relLength_eq_length_map_mkQ (B.submoduleOf A),
    relLength_def, relLength_def]
  refine Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.factor hle)
    (Submodule.injective_subtype _) (Submodule.factor_surjective _) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  constructor
  · intro h
    have hx : x ∈ B.submoduleOf A := by
      simpa [Submodule.factor_mk] using h
    exact ⟨⟨_, x, hx, rfl⟩, rfl⟩
  · rintro ⟨⟨_, z, hz, rfl⟩, h⟩
    have h' : (C.submoduleOf A).mkQ z = (C.submoduleOf A).mkQ x := h
    rw [← h']
    simpa [Submodule.factor_mk] using hz

theorem ord_prod {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]

theorem length_coker {R ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype ι] (f : (ι → R) →ₗ[R] (ι → R)) (hf : Function.Injective f) :
    Module.length R ((ι → R) ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hf
  set e := Pi.basisFun R ι
  set d := Submodule.smithNormalFormCoeffs e h with hd
  set top := Submodule.smithNormalFormTopBasis e h with htop
  set bot := Submodule.smithNormalFormBotBasis e h with hbot
  have hass := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (top.equiv bot (Equiv.refl ι))
  have h1 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext1 i
    ext1
    rfl
  have h2 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (top.equiv bot (Equiv.refl ι)).toLinearMap) = ∏ i, d i := by
    rw [← LinearMap.det_toMatrix top, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have := Submodule.smithNormalFormBotBasis_def e h j
    rw [← hd, ← htop, ← hbot] at this
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Finsupp.single_apply, Ne.symm hij]
  rw [h1, h2] at hass
  obtain ⟨v, hv⟩ := hass.symm
  rw [(Submodule.quotientEquivPiSpan _ e h).length_eq, Module.length_pi_of_fintype, ← hv,
    Ring.ord_mul R (v.isUnit.mem_nonZeroDivisors), Ring.ord_of_isUnit v.isUnit, add_zero,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero e h)]
  rfl

theorem relLength_span_matrix {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by
  let φ := Fintype.linearCombination R a
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i
  have hf : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)
  have hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hC : Submodule.span R (Set.range c) =
      Submodule.map φ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, Fintype.linearCombination_apply, hc]
  rw [hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf,
    LinearMap.det_toLin']

theorem signedLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ)
    (u : Rˣ) (n : ℤ) (hdet : g.det = algebraMap R K (u : R) * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hg : g.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr u.ne_zero) (zpow_ne_zero _ hϖK)
  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro x hx
    have h0 : g.mulVec x = 0 := by
      funext i
      refine ha (g.mulVec x) ?_ i
      rw [← hx]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0)
  have hres : ∀ {v : ι → V}, LinearIndependent K v → LinearIndependent R v := fun hv =>
    hv.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using hinj)
  obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose m hm using hint
  let M : Matrix ι ι R := Matrix.of fun i j => m (i, j)
  have hM : (algebraMap R K).mapMatrix M = algebraMap R K t • g := by
    ext i j
    simp [M, hm, Algebra.smul_def]
  let D : Matrix ι ι R := Matrix.diagonal fun _ => t
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.ne_zero ht
  have hMD : algebraMap R K M.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, hM, Matrix.det_smul, Matrix.det_diagonal]
    simp
  have hM0 : M.det ≠ 0 := by
    rw [← map_ne_zero_iff _ hinj, hMD]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hD) hg
  let c : ι → V := fun j => t • b j
  have hca : ∀ j, c j = ∑ i, M i j • a i := by
    intro j
    simp only [c, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hm (i, j), algebraMap_smul]
    rfl
  have hcb : ∀ j, c j = ∑ i, D i j • b i := by
    intro j
    simp [c, D, Matrix.diagonal_apply, ite_smul]
  have hle : ∀ {v : ι → V} {N : Matrix ι ι R}, (∀ j, c j = ∑ i, N i j • v i) →
      Submodule.span R (Set.range c) ≤ Submodule.span R (Set.range v) := by
    intro v N hN
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hN]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := relLength_span_matrix (hres ha) M hM0 hca
  have h2 := relLength_span_matrix (hres hbK) D hD hcb
  have hC := le_inf (hle hca) (hle hcb)
  rw [relLength_tower inf_le_left hC, relLength_inf_right] at h1
  rw [relLength_tower inf_le_right hC, relLength_inf_right'] at h2
  have hord : Ring.ord R ϖ = 1 := by
    have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have h := relLength_top_of_isMaximal (Ideal.span {ϖ})
    rw [relLength_top_left] at h
    exact h
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℕ, n = (p : ℤ) - q := ⟨n.toNat, (-n).toNat, by omega⟩
  have hR : M.det * ϖ ^ q = D.det * (u * ϖ ^ p) := by
    apply hinj
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hMD, hdet, zpow_sub₀ hϖK, zpow_natCast,
      zpow_natCast]
    field_simp
  have hϖ0 : ϖ ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have hlen := congrArg (Ring.ord R) hR
  rw [Ring.ord_mul R (pow_mem hϖ0 q), Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero hD),
    Ring.ord_mul R (pow_mem hϖ0 p), Ring.ord_of_isUnit u.isUnit, Ring.ord_pow hϖ0,
    Ring.ord_pow hϖ0, hord, ← h1, ← h2] at hlen
  have f1 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM0)
  have f2 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hD)
  rw [← h1] at f1
  rw [← h2] at f2
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).1
  obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).2
  obtain ⟨z, hz⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f2).2
  rw [signedLength_eq_of_relLength_eq hy.symm hz.symm]
  rw [← hx, ← hy, ← hz, nsmul_one, nsmul_one, zero_add] at hlen
  have : x + y + q = x + z + p := by exact_mod_cast hlen
  omega

end GlobalTheory.SignedLengthTower
end

section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthLogDet

open Module

theorem ord_finprod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι)
    (c : ι → R) (hc : ∀ i, c i ≠ 0) :
    Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]

theorem length_coker {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (b : Basis ι R M)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range φ) = Ring.ord R (LinearMap.det φ) := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have hrk : finrank R N = finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b hrk
  let t := Submodule.smithNormalFormTopBasis b hrk
  let s := Submodule.smithNormalFormBotBasis b hrk
  have hs : ∀ i, (s i : M) = c i • t i := Submodule.smithNormalFormBotBasis_def b hrk
  have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrk
  let e' : M ≃ₗ[R] N := t.equiv s (Equiv.refl _)
  have h1 : Associated (LinearMap.det φ) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    conv_lhs => rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix t, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp [e', hs]
    rw [LinearMap.toMatrix_apply, this, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  rw [Ring.ord_eq_of_associated h1, h2, ord_finprod _ _ hc,
    (Submodule.quotientEquivPiSpan N b hrk).length_eq, Module.length_pi_of_fintype]
  rfl

theorem relLength_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hle : C.submoduleOf A ≤ D.submoduleOf A := Submodule.comap_mono hCD
  have hf : C.submoduleOf D ≤ (C.submoduleOf A).comap (Submodule.inclusion hDA) :=
    fun x hx => hx
  have := Module.length_eq_add_of_exact
    (Submodule.mapQ (C.submoduleOf D) (C.submoduleOf A) (Submodule.inclusion hDA) hf)
    (Submodule.factor hle) ?_ (Submodule.factor_surjective hle) ?_
  · rw [relLength_def, this, add_comm]; rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (Submodule.Quotient.mk y : A ⧸ D.submoduleOf A) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      exact ⟨Submodule.Quotient.mk ⟨y, hy'⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      change (Submodule.Quotient.mk (Submodule.inclusion hDA x) : A ⧸ D.submoduleOf A) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.2


theorem ordFrac_algebraMap_eq_exp {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R} (hx : x ≠ 0) {n : ℕ}
    (hn : Ring.ord R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R hx,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hx) hn]
  rfl


end GlobalTheory.SignedLengthLogDet
end

section
open Module IsDiscreteValuationRing

namespace GlobalTheory

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Cokernel

variable {M : Type*} [AddCommGroup M] [Module R M]


theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  first
  | (rename_i h_1 h_2 h_3; revert R h_1 h_2 h_3 ι s a; exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod)
  | exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | (apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod ..)

theorem length_quotient_range_eq_top_of_det_eq_zero [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (hf : LinearMap.det f = 0) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 f hf; exact @_root_.GlobalTheory.LengthDualFunctional.main)
  | exact @_root_.GlobalTheory.LengthDualFunctional.main
  | exact _root_.GlobalTheory.LengthDualFunctional.main
  | (apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthDualFunctional.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthDualFunctional.main ..)

theorem length_quotient_eq_addVal_det_equiv [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) = addVal R (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 N e; exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det ..)

theorem length_quotient_range_eq_addVal_det [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.det f = 0
  · rw [length_quotient_range_eq_top_of_det_eq_zero hf, hf, addVal_zero]
  · have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      by_contra h
      exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    exact length_quotient_eq_addVal_det_equiv _ (LinearEquiv.ofInjective f hinj)


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem length_quotient_range_toLin'_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (Matrix.toLin' P)) = addVal R P.det := by
  rw [length_quotient_range_eq_addVal_det, LinearMap.det_toLin']

theorem length_quotient_range_mulVecLin_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det :=
  length_quotient_range_toLin'_eq_addVal_det P



theorem length_quotient_range_eq_addVal_det_toMatrix {M' : Type*} [AddCommGroup M'] [Module R M']
    (b' : Basis ι R M') (b : Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.toMatrix b' b f).det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9 h_11 h_12; revert R h_1 h_2 h_3 M h_5 h_6 ι h_8 h_9 M' h_11 h_12 b' b f; exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main)
  | exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main
  | exact _root_.GlobalTheory.LengthQuotientSpanValuation.main
  | (apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientSpanValuation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientSpanValuation.main ..)

theorem length_quotient_span_eq_addVal_det (b : Basis ι R M) (v : ι → M) :
    Module.length R (M ⧸ Submodule.span R (Set.range v)) = addVal R (b.det v) := by
  rw [← b.constr_range R, length_quotient_range_eq_addVal_det_toMatrix b b, Basis.det_apply,
    Basis.toMatrix_eq_toMatrix_constr]
  rfl




end Cokernel

section Relative

variable {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem relLength_span_eq_addVal_det {A : Submodule R V} (b : Basis ι R A) (v : ι → A) :
    relLength A (Submodule.span R (Set.range fun i => (v i : V))) = addVal R (b.det v) := by
  have : Submodule.span R (Set.range fun i => (v i : V)) =
      (Submodule.span R (Set.range v)).map A.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← length_quotient_span_eq_addVal_det, ← relLength_top_left, ← relLength_map_subtype,
    Submodule.map_subtype_top, this]



end Relative

section Lattice



variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem ordFrac_algebraMap_eq_exp {x : R} {n : ℕ} (h : addVal R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_of_ne_zero hx) ((Ring.ord_eq_addVal x).trans h)]
  rfl

theorem ordFrac_unit_mul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    Ring.ordFrac R (algebraMap R K u * algebraMap R K ϖ ^ n) = WithZero.exp n := by
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible hϖ, one_mul,
    ← WithZero.exp_zsmul, smul_eq_mul, mul_one]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]






theorem signedLength_span_eq_of_det_eq_unit_mul_zpow {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ)
    (n : ℤ) (hg : g.det = algebraMap R K u * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 a b ha g hb ϖ hϖ u n hg; exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq)
  | exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | (apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq ..)




omit [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_coe_basis {A : Submodule R V} (a : Basis ι R A) :
    Submodule.span R (Set.range fun i => (a i : V)) = A := by
  conv_rhs => rw [← Submodule.map_subtype_top A, ← a.span_eq, Submodule.map_span,
    ← Set.range_comp]
  rfl

omit [IsDiscreteValuationRing R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_extendOfIsLattice {A : Submodule R V} [A.IsLattice K]
    (a : Basis ι R A) : Submodule.span R (Set.range (a.extendOfIsLattice K)) = A := by
  refine Eq.trans ?_ (span_range_coe_basis a)
  congr 2
  funext i
  exact a.extendOfIsLattice_apply K i


theorem signedLength_map_eq_log_ordFrac_det (A : Submodule R V) [A.IsLattice K] (g : V →ₗ[K] V)
    (hg : LinearMap.det g ≠ 0) :
    LengthCommensurable A (A.map (g.restrictScalars R)) ∧
      signedLength A (A.map (g.restrictScalars R)) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g)) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 A h_14 g hg; exact @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det ..)

theorem signedLength_eq_log_ordFrac_det_of_map_eq {A B : Submodule R V} [A.IsLattice K]
    (g : V ≃ₗ[K] V) (h : A.map ((g : V →ₗ[K] V).restrictScalars R) = B) :
    LengthCommensurable A B ∧
      signedLength A B = WithZero.log (Ring.ordFrac R (LinearMap.det (g : V →ₗ[K] V))) :=
  h ▸ signedLength_map_eq_log_ordFrac_det A _ g.isUnit_det'.ne_zero

variable (K) in

theorem exists_linearEquiv_map_eq_of_isLattice (A B : Submodule R V) [A.IsLattice K]
    [B.IsLattice K] : ∃ g : V ≃ₗ[K] V, A.map ((g : V →ₗ[K] V).restrictScalars R) = B := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_15 h_16; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 A B h_15 h_16; exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq)
  | exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | (apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq ..)

variable (K) in

theorem lengthCommensurable_of_isLattice (A B : Submodule R V) [A.IsLattice K] [B.IsLattice K] :
    LengthCommensurable A B :=
  have ⟨g, h⟩ := exists_linearEquiv_map_eq_of_isLattice K A B
  (signedLength_eq_log_ordFrac_det_of_map_eq g h).1


example {ϖ : R} (hϖ : Irreducible ϖ) :
    signedLength (Submodule.span R (Set.range fun _ : Unit => (1 : K)))
      (Submodule.span R (Set.range fun _ : Unit => (algebraMap R K ϖ)⁻¹)) = -1 :=
  signedLength_span_eq_of_det_eq_unit_mul_zpow (K := K) (by simp)
    (Matrix.of fun _ _ => (algebraMap R K ϖ)⁻¹) (by simp) hϖ 1 (-1) (by simp)

end Lattice

end GlobalTheory
end
