import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

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
