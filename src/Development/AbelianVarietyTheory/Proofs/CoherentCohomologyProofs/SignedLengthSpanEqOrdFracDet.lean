import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

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
