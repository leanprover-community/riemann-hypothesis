import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertySemiAbelianFlatBaseChangeDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_vert_of_mem (S : Type) [CommRing S] [IsDomain S] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] (f : S) (hf : f ≠ 0) (hx : ∃ x : X, f ∈ (p x).asIdeal) : ∃ z : X, Vert p f z := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal := by
    intro q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal := by
    intro y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩
  have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
    (X.presheaf.stalk (z : X))
  rw [this, hP]
  change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
  rw [hQ1]; rfl

end GlobalTheory.Desc
end

section
open IsLocalRing

namespace GlobalTheory.VandermondeEmbeddingVanishing

theorem eq_zero_of_embeddings {K L Ω : Type} [Field K] [Field L] [Field Ω] [IsAlgClosed Ω] [Algebra K L] [Algebra K Ω]
    [Module.Finite K L] [Algebra.IsSeparable K L] {ι : Type} [Fintype ι] (b : Module.Basis ι K L) (c : ι → Ω)
    (h : ∀ s : L →ₐ[K] Ω, ∑ t, s (b t) * c t = 0) : c = 0 := by
  classical
  have hcard : Fintype.card ι = Fintype.card (L →ₐ[K] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e : ι ≃ (L →ₐ[K] Ω) := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex K Ω b e).det ≠ 0 := by
    intro h0
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two (K := K) (E := Ω) (b := ⇑b) e
    rw [h0, zero_pow two_ne_zero, map_eq_zero_iff _ (algebraMap K Ω).injective] at hd
    exact Algebra.discr_not_zero_of_basis K b hd
  have hmul : Matrix.mulVec (Algebra.embeddingsMatrixReindex K Ω b e).transpose c = 0 := by
    ext j
    simpa [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix_apply] using h (e j)
  exact Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hmul

theorem exists_functional {T M Ω : Type} [CommRing T] [IsLocalRing T] [AddCommGroup M] [Module T M] [Field Ω]
    [Algebra (ResidueField T) Ω] [Algebra T Ω] [IsScalarTower T (ResidueField T) Ω] (ϖ : T)
    (hϖ : maximalIdeal T = Ideal.span {ϖ}) (z : M) (hz : ¬ ∃ y : M, z = ϖ • y) : ∃ lam : M →ₗ[T] Ω, lam z ≠ 0 := by
  classical
  let N : Submodule T M := maximalIdeal T • ⊤
  let _ : Module (ResidueField T) (M ⧸ N) := Module.instQuotientIdealSubmoduleHSMulTop M (maximalIdeal T)
  have hq : (Submodule.Quotient.mk z : M ⧸ N) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    show z ∉ maximalIdeal T • (⊤ : Submodule T M)
    rw [hϖ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    rintro ⟨y, -, hy⟩
    exact hz ⟨y, hy.symm⟩
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ResidueField T) (M ⧸ N), f (Submodule.Quotient.mk z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff (ResidueField T) _).mp hcon)
  refine ⟨LinearMap.mk (AddHom.mk (fun m => algebraMap (ResidueField T) Ω (f (Submodule.Quotient.mk m)))
    (fun a b => by simp only [Submodule.Quotient.mk_add, map_add])) (fun a m => ?_), ?_⟩
  · have hs : (Submodule.Quotient.mk (a • m) : M ⧸ N) = residue T a • Submodule.Quotient.mk m := rfl
    simp only [RingHom.id_apply]
    rw [hs, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply T (ResidueField T) Ω a]
    rfl
  · exact (map_ne_zero (algebraMap (ResidueField T) Ω)).mpr hf

theorem mem_spanBy_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] (S : Set F) (x : F) :
    x ∈ GlobalTheory.Desc.spanBy (algebraMap R F) S ↔ x ∈ Submodule.span R S := by
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Submodule.sum_mem _ fun i _ => by
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (ht i))
  · intro hx
    obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hx
    exact ⟨n, f, fun i => g i, fun i => (g i).2, by rw [← hfg]; simp only [Algebra.smul_def]⟩

section Main

variable {O T F F₁ Ω : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field F] [Field F₁] [Algebra O T] [IsLocalHom (algebraMap O T)] [Algebra T F₁] [Field Ω] [IsAlgClosed Ω]
  [Algebra (ResidueField O) Ω] [Algebra (ResidueField T) Ω] [Algebra T Ω] [IsScalarTower T (ResidueField T) Ω]
  [Module.Finite (ResidueField O) (ResidueField T)] [Algebra.IsSeparable (ResidueField O) (ResidueField T)]

def Van (Ω : Type) [Field Ω] [Algebra (ResidueField O) Ω] [Algebra T Ω] (θ : F →+* F₁) (π : O) (W : Subalgebra T F₁) : Prop :=
  ∀ (s : ResidueField T →ₐ[ResidueField O] Ω) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω) (n : ℕ) (r : Fin n → T)
    (w : Fin n → F) (hw : ∀ (i : Fin n), θ (w i) ∈ Subalgebra.toSubmodule W), ∀ y ∈ W,
    ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
      ∑ i : Fin n, s (residue T (r i)) * lam ⟨θ (w i), hw i⟩ = 0

theorem compat {c₀ : O →+* F} {θ : F →+* F₁} (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    {W : Subalgebra T F₁} (hV : Van Ω θ π W) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω)
    (h1 : lam ⟨1, W.one_mem⟩ ≠ 0) (o : O) :
    algebraMap (ResidueField O) Ω (residue O o) = algebraMap T Ω (algebraMap O T o) := by
  classical
  let s : ResidueField T →ₐ[ResidueField O] Ω := IsAlgClosed.lift
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have hmem : ∀ x, θ (c₀ x) ∈ Subalgebra.toSubmodule W := fun x => by
    rw [Subalgebra.mem_toSubmodule, hco]
    exact W.algebraMap_mem _
  have hl : ∀ x, lam ⟨θ (c₀ x), hmem x⟩ = algebraMap T Ω (algebraMap O T x) * lam ⟨1, W.one_mem⟩ := by
    intro x
    rw [← Algebra.smul_def, ← map_smul]
    congr 1
    ext
    simp only [hco, Submodule.coe_smul, Algebra.algebraMap_eq_smul_one]
  have key := hV s lam 2 ![1, -algebraMap O T o] ![c₀ o, c₀ 1] (fun i => by fin_cases i <;> exact hmem _) 0 W.zero_mem
    (by simp [Fin.sum_univ_two, hco])
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  rw [hl, hl, map_one, map_one, map_one, map_one, one_mul, map_neg, map_neg, ← IsLocalRing.ResidueField.algebraMap_residue,
    AlgHom.commutes] at key
  have hsub : (algebraMap T Ω (algebraMap O T o) - algebraMap (ResidueField O) Ω (residue O o)) * lam ⟨1, W.one_mem⟩ = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp hsub with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h h1

theorem comp_div {c₀ : O →+* F} {θ : F →+* F₁} (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    (hπ : Irreducible (algebraMap O T π)) {W : Subalgebra T F₁} (hV : Van Ω θ π W)
    {ι : Type} [Fintype ι] (b : Module.Basis ι (ResidueField O) (ResidueField T))
    {n : ℕ} (r : Fin n → T) (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W) (y : F₁) (hy : y ∈ W)
    (hr : ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y)
    (o : ι → Fin n → O) (ho : ∀ t i, residue O (o t i) = b.repr (residue T (r i)) t) (t : ι) :
    ∃ y' ∈ W, ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y' := by
  classical
  have hmax : maximalIdeal T = Ideal.span {algebraMap O T π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
  have hsum : ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i) ∈ W :=
    W.sum_mem fun i _ => W.mul_mem (W.algebraMap_mem _) (hw i)
  by_cases hone : ∃ y₁ ∈ W, (1 : F₁) = algebraMap T F₁ (algebraMap O T π) * y₁
  · obtain ⟨y₁, hy₁, e₁⟩ := hone
    exact ⟨y₁ * ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i), W.mul_mem hy₁ hsum,
      by rw [← mul_assoc, ← e₁, one_mul]⟩
  obtain ⟨lam₀, hl₀⟩ := exists_functional (Ω := Ω) (M := Subalgebra.toSubmodule W) _ hmax ⟨1, W.one_mem⟩ (by
    rintro ⟨y, hy⟩
    exact hone ⟨y, y.2, by simpa [Algebra.smul_def] using congrArg Subtype.val hy⟩)
  have hcompat := compat hc hV lam₀ hl₀
  by_contra hno
  obtain ⟨lam, hlam⟩ := exists_functional (Ω := Ω) (M := Subalgebra.toSubmodule W) _ hmax ⟨_, hsum⟩ (by
    rintro ⟨y, hy⟩
    exact hno ⟨y, y.2, by simpa [Algebra.smul_def] using congrArg Subtype.val hy⟩)
  apply hlam
  let cc : ι → Ω := fun t => ∑ i, algebraMap (ResidueField O) Ω (residue O (o t i)) * lam ⟨θ (w i), hw i⟩
  have hcc : cc = 0 := by
    refine eq_zero_of_embeddings b cc fun s => ?_
    have hs := hV s lam n r w hw y hy hr
    rw [← hs]
    simp only [cc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← b.sum_repr (residue T (r i)), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [map_smul, ← ho, Algebra.smul_def]
    ring
  have he : (⟨_, hsum⟩ : Subalgebra.toSubmodule W) = ∑ i, algebraMap O T (o t i) • ⟨θ (w i), hw i⟩ := by
    ext
    simp [Algebra.smul_def]
  rw [he, map_sum]
  have hct : cc t = 0 := by rw [hcc]; rfl
  rw [← hct]
  simp only [cc, map_smul, Algebra.smul_def, hcompat]

theorem div_span (hinj : Function.Injective (algebraMap T F₁)) {c₀ : O →+* F} {θ : F →+* F₁}
    (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    (hπ : Irreducible (algebraMap O T π)) {W : Subalgebra T F₁} (hV : Van Ω θ π W)
    {n : ℕ} (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W) (S : Finset (Fin n)) :
    ∀ (r : Fin n → T), (∀ i ∉ S, r i = 0) → ∀ y ∈ W,
      ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
      y ∈ Submodule.span T (θ '' (θ ⁻¹' (W : Set F₁))) := by
  classical
  intro r _ y hy hr
  have hmax : maximalIdeal T = Ideal.span {algebraMap O T π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have hϖ : algebraMap T F₁ (algebraMap O T π) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hπ.ne_zero
  let b := Module.finBasis (ResidueField O) (ResidueField T)
  choose o ho using fun t (i : Fin n) => IsLocalRing.residue_surjective (b.repr (residue T (r i)) t)
  choose β hβ using fun t => IsLocalRing.residue_surjective (b t)
  have hdiff : ∀ i, ∃ r' : T, r i = ∑ t, algebraMap O T (o t i) * β t + algebraMap O T π * r' := by
    intro i
    have hm : r i - ∑ t, algebraMap O T (o t i) * β t ∈ maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sum]
      simp only [map_mul, ← IsLocalRing.ResidueField.algebraMap_residue, ho, hβ]
      conv_lhs => enter [1]; rw [← b.sum_repr (residue T (r i))]
      simp [Algebra.smul_def]
    rw [hmax, Ideal.mem_span_singleton'] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, by rw [mul_comm _ a, ha]; ring⟩
  choose r' hr' using hdiff
  choose y' hy' hyeq using fun t => comp_div hc hπ hV b r w (fun i => hw i) y hy hr o (fun t i => ho t i) t
  have hmem' : ∀ t, y' t ∈ θ '' (θ ⁻¹' (W : Set F₁)) := by
    intro t
    have hne : θ (c₀ π) ≠ 0 := by rw [hco]; exact hϖ
    have hval : θ ((∑ i, c₀ (o t i) * w i) * (c₀ π)⁻¹) = y' t := by
      rw [map_mul, map_inv₀, map_sum]
      simp only [map_mul, hco]
      rw [hyeq t, mul_comm, ← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    exact ⟨_, by rw [Set.mem_preimage, hval]; exact hy' t, hval⟩
  have hyeq' : y = ∑ t, algebraMap T F₁ (β t) * y' t + ∑ i, algebraMap T F₁ (r' i) * θ (w i) := by
    apply mul_left_cancel₀ hϖ
    rw [← hr]
    simp only [hr', map_add, map_sum, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_add, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mul_left_comm, ← hyeq t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [hyeq']
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
  · rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem' t))
  · rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w i, hw i, rfl⟩)

theorem gaussAt (hinj : Function.Injective (algebraMap T F₁)) (c₀ : O →+* F) (θ : F →+* F₁)
    (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) (π : O)
    (hπ : Irreducible (algebraMap O T π)) (W : Subalgebra T F₁)
    (hW : ∀ x : F₁, ∃ n : ℕ, algebraMap T F₁ (algebraMap O T π) ^ n * x ∈ W)
    (hV : ∀ (s : ResidueField T →ₐ[ResidueField O] Ω) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω) (n : ℕ)
      (r : Fin n → T) (w : Fin n → F) (hw : ∀ (i : Fin n), θ (w i) ∈ Subalgebra.toSubmodule W), ∀ y ∈ W,
      ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
        ∑ i : Fin n, s (residue T (r i)) * lam ⟨θ (w i), hw i⟩ = 0) :
    GlobalTheory.Desc.GaussAt (algebraMap T F₁) (maximalIdeal T) θ (θ ⁻¹' (W : Set F₁)) (W : Set F₁) := by
  classical
  have hϖ0 : algebraMap O T π ≠ 0 := hπ.ne_zero
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have claim : ∀ (K : ℕ) (v : F₁), v ∈ W → ∀ (m : ℕ) (r : Fin m → T) (u : Fin m → F), (∀ i, θ (u i) ∈ W) →
      algebraMap T F₁ (algebraMap O T π) ^ K * v = ∑ i, algebraMap T F₁ (r i) * θ (u i) →
      v ∈ Submodule.span T (θ '' (θ ⁻¹' (W : Set F₁))) := by
    intro K
    induction K with
    | zero =>
      intro v _ m r u hu he
      rw [pow_zero, one_mul] at he
      rw [he]
      exact Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u i, hu i, rfl⟩)
    | succ k ih =>
      intro v hv m r u hu he
      have hvk : algebraMap T F₁ (algebraMap O T π) ^ k * v ∈ W :=
        W.mul_mem (W.pow_mem (W.algebraMap_mem _) _) hv
      have hsp := div_span (Ω := Ω) hinj hc hπ hV u hu Finset.univ r (by simp) _ hvk (by rw [← he, pow_succ]; ring)
      obtain ⟨m', f, g, hfg⟩ := Submodule.mem_span_set'.mp hsp
      choose u' hu' hgu using fun j => (g j).2
      exact ih v hv m' f u' hu' (by rw [← hfg]; simp only [Algebra.smul_def, hgu])
  rintro v ⟨d, hd0, hdv⟩
  constructor
  · intro hv
    refine ⟨1, (maximalIdeal.isMaximal T).ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), ?_⟩
    rw [map_one, one_mul, mem_spanBy_iff]
    obtain ⟨n, r, t, ht, hdv'⟩ := hdv
    choose u hu using ht
    choose N hN using fun i => hW (θ (u i))
    obtain ⟨K, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mul_ne_zero (pow_ne_zero (∑ i, N i) hϖ0) hd0) hπ
    refine claim K v hv n (fun i => ↑e⁻¹ * r i) (fun i => c₀ π ^ (∑ j, N j) * u i) (fun i => ?_) ?_
    · rw [map_mul, map_pow, hco, ← Nat.sub_add_cancel (Finset.single_le_sum (fun j _ => Nat.zero_le (N j))
        (Finset.mem_univ i)), pow_add, mul_assoc]
      exact W.mul_mem (W.pow_mem (W.algebraMap_mem _) _) (hN i)
    · have h2 : algebraMap T F₁ (↑e * algebraMap O T π ^ K) * v =
          algebraMap T F₁ (algebraMap O T π ^ (∑ j, N j)) * ∑ i, algebraMap T F₁ (r i) * t i := by
        rw [← he, map_mul, mul_assoc, hdv']
      have hu' : ∀ i, t i = θ (u i) := fun i => (hu i).symm
      simp only [hu'] at h2
      calc algebraMap T F₁ (algebraMap O T π) ^ K * v
          = algebraMap T F₁ ↑e⁻¹ * (algebraMap T F₁ (↑e * algebraMap O T π ^ K) * v) := by
            rw [map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
        _ = ∑ i, algebraMap T F₁ (↑e⁻¹ * r i) * θ (c₀ π ^ (∑ j, N j) * u i) := by
            rw [h2, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [map_mul, map_pow, hco]
            ring
  · rintro ⟨s, hs, hsv⟩
    rw [mem_spanBy_iff] at hsv
    have hsW : algebraMap T F₁ s * v ∈ Subalgebra.toSubmodule W :=
      Submodule.span_le.mpr (by rintro x ⟨a, ha, rfl⟩; exact ha) hsv
    obtain ⟨u, rfl⟩ : IsUnit s := by
      by_contra hnu
      exact hs ((IsLocalRing.mem_maximalIdeal s).mpr hnu)
    have hv : v = algebraMap T F₁ ↑u⁻¹ * (algebraMap T F₁ ↑u * v) := by
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    show v ∈ W
    rw [hv]
    exact W.mul_mem (W.algebraMap_mem _) hsW

end Main

end GlobalTheory.VandermondeEmbeddingVanishing
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GaussDvr

theorem rel_transfer {T E F₁ FH Ω : Type} [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [CommRing E] [Field F₁]
    [CommRing FH] [CommRing Ω] [Algebra T F₁] [Algebra T Ω] (hc : Function.Injective (algebraMap T F₁))
    (b : T →+* E) (cE : E →+* FH) (θb : F₁ →+* FH) (hcomm : θb.comp (algebraMap T F₁) = cE.comp b)
    (hld : LinDisj (algebraMap T F₁) cE θb) (v : E →+* Ω) (hv : v.comp b = algebraMap T Ω)
    (W : Submodule T F₁) (lam : W →ₗ[T] Ω) {J : Type} [Fintype J] (r : J → E) (x : J → W)
    (h : ∑ i, cE (r i) * θb (x i) = 0) : ∑ i, v (r i) * lam (x i) = 0 := by
  classical
  haveI : FaithfulSMul T F₁ := (faithfulSMul_iff_algebraMap_injective T F₁).2 hc
  let M : Submodule T W := Submodule.span T (Set.range x)
  haveI : Module.Finite T M := Module.Finite.span_of_finite T (Set.finite_range x)
  haveI : Module.Free T M := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis T M
  let x' : J → M := fun i => ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hx : ∀ i, x i = ∑ t, B.repr (x' i) t • (B t : W) := fun i => by
    have := congrArg (fun m : M => (m : W)) (B.sum_repr (x' i))
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using this.symm
  have hb : ∀ t, θb (algebraMap T F₁ t) = cE (b t) := fun t => RingHom.congr_fun hcomm t
  have hvb : ∀ t, v (b t) = algebraMap T Ω t := fun t => RingHom.congr_fun hv t
  have h0 := hld _ (fun t => ((B t : W) : F₁)) (fun s hs => by
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent s (by
      apply Subtype.ext; apply Subtype.ext
      simpa [Algebra.smul_def] using hs)
    exact funext hli) (fun t => ∑ i, r i * b (B.repr (x' i) t)) (by
      rw [← h]
      simp only [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [hx i]
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def, map_sum, map_mul, hb,
        Finset.mul_sum, _root_.mul_assoc])
  have h1 : ∑ i, v (r i) * lam (x i) = ∑ t, v (∑ i, r i * b (B.repr (x' i) t)) * lam (B t) := by
    simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hx i]
    simp only [map_sum, map_smul, Algebra.smul_def, hvb, Finset.mul_sum, _root_.mul_assoc]
  rw [h1]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [show (∑ i, r i * b (B.repr (x' i) t)) = 0 from congrFun h0 t, map_zero, zero_mul]

theorem key_of_gauss {T E F F₁ FH Ω : Type} [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [CommRing E] [IsLocalRing E]
    [Field F] [Field F₁] [CommRing FH] [Field Ω] [Algebra T F₁] [Algebra T Ω]
    (hc : Function.Injective (algebraMap T F₁)) (θ : F →+* F₁)
    (a b : T →+* E) (cE : E →+* FH) (θa θb : F₁ →+* FH) (ha : θa.comp (algebraMap T F₁) = cE.comp a)
    (hb : θb.comp (algebraMap T F₁) = cE.comp b) (hθ : θa.comp θ = θb.comp θ)
    (hld : LinDisj (algebraMap T F₁) cE θb) (v : E →+* Ω) (hv : v.comp b = algebraMap T Ω)
    (hk : RingHom.ker v = maximalIdeal E) (W : Submodule T F₁) (WH : Set FH) (hW : ∀ y ∈ W, θa y ∈ WH)
    (hG : GaussAt cE (maximalIdeal E) θb W WH) (π : T) (hπ : a π ≠ 0) (hπ' : v (a π) = 0)
    (lam : W →ₗ[T] Ω) (n : ℕ) (r : Fin n → T) (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W) (y : F₁) (hy : y ∈ W)
    (h : ∑ i, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ π * y) :
    ∑ i, v (a (r i)) * lam ⟨_, hw i⟩ = 0 := by
  have ha' : ∀ t, θa (algebraMap T F₁ t) = cE (a t) := fun t => RingHom.congr_fun ha t
  have hθ' : ∀ t, θa (θ t) = θb (θ t) := fun t => RingHom.congr_fun hθ t
  have h1 : cE (a π) * θa y = ∑ i, cE (a (r i)) * θb (θ (w i)) := by
    have := congrArg θa h
    simp only [map_sum, map_mul, ha', hθ'] at this
    exact this.symm
  obtain ⟨s, hs, m, r', t, ht, e⟩ :=
    (hG (θa y) ⟨a π, hπ, n, fun i => a (r i), fun i => θb (θ (w i)), fun i => ⟨_, rfl⟩, h1⟩).1 (hW y hy)
  choose t' ht' ht'' using ht
  have h2 := rel_transfer hc b cE θb hb hld v hv W lam (J := Fin n ⊕ Fin m)
    (Sum.elim (fun i => s * a (r i)) (fun l => -(a π * r' l))) (Sum.elim (fun i => ⟨_, hw i⟩) (fun l => ⟨_, ht' l⟩)) (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_mul, map_neg, ht'', _root_.mul_assoc, neg_mul,
        Finset.sum_neg_distrib, ← Finset.mul_sum]
      rw [← h1, ← e]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_mul, map_neg, hπ', zero_mul, neg_zero,
    Finset.sum_const_zero, add_zero, _root_.mul_assoc, ← Finset.mul_sum] at h2
  refine (mul_eq_zero.1 h2).resolve_left fun h0 => hs ?_
  rw [← hk]; exact h0

theorem gauss_of_key {O T F F₁ Ω : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field F] [Field F₁] [Algebra O T] [IsLocalHom (algebraMap O T)] [Algebra T F₁]
    [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField O) Ω] [Algebra (ResidueField T) Ω] [Algebra T Ω]
    [IsScalarTower T (ResidueField T) Ω]
    [Module.Finite (ResidueField O) (ResidueField T)] [Algebra.IsSeparable (ResidueField O) (ResidueField T)]
    (hc : Function.Injective (algebraMap T F₁)) (c₀ : O →+* F) (θ : F →+* F₁)
    (hcomm : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) (π : O) (hπ : Irreducible (algebraMap O T π))
    (W : Subalgebra T F₁) (htors : ∀ x : F₁, ∃ n : ℕ, algebraMap T F₁ (algebraMap O T π) ^ n * x ∈ W)
    (key : ∀ (s : ResidueField T →ₐ[ResidueField O] Ω) (lam : W.toSubmodule →ₗ[T] Ω) (n : ℕ) (r : Fin n → T)
      (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W.toSubmodule) (y : F₁), y ∈ W →
      ∑ i, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
      ∑ i, s (residue T (r i)) * lam ⟨_, hw i⟩ = 0) :
    GaussAt (algebraMap T F₁) (maximalIdeal T) θ (θ ⁻¹' W) W := by
  first
  | (rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_15 h_16 h_17 h_18 h_19 h_20 h_21 h_22; revert O T F F₁ Ω h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_15 h_16 h_17 h_18 h_19 h_20 h_21 h_22 hc c₀ θ hcomm π hπ W htors key; exact @_root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt)
  | exact @_root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt
  | exact _root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt
  | (apply _root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt <;> assumption)
  | (intros; apply _root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.VandermondeEmbeddingVanishing.gaussAt ..)

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem flat_ne_zero {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S] (a : R →+* S) (ha : a.Flat)
    {r : R} (hr : r ≠ 0) : a r ≠ 0 := by
  intro h
  letI := a.toAlgebra
  haveI : Module.Flat R S := ha
  have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) (mem_nonZeroDivisors_of_ne_zero hr)
  have h1 : r • (1 : S) = r • (0 : S) := by
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact h
  exact one_ne_zero (this h1)

theorem dvr_of_span {T : Type} [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsLocalRing T] {t : T} (ht : t ≠ 0)
    (h : maximalIdeal T = Ideal.span {t}) : IsDiscreteValuationRing T := by
  have hf : ¬ IsField T := by
    rw [isField_iff_maximalIdeal_eq, h, Ideal.span_singleton_eq_bot]; exact ht
  have h2 : Submodule.IsPrincipal (maximalIdeal T) := ⟨t, h⟩
  exact ((IsDiscreteValuationRing.TFAE T hf).out 0 4).2 h2

theorem exists_dvd_pow {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : ringKrullDim A = 1) {b t : A}
    (hb : b ≠ 0) (ht : t ∈ maximalIdeal A) : ∃ n : ℕ, b ∣ t ^ n := by
  have h1 : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hA]; rfl)
  have : t ∈ (Ideal.span {b}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hP, hP'⟩
    have hne : P ≠ ⊥ := fun h => hb (by simpa [h] using hP)
    rw [eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 h1 P hne hP')]
    exact ht
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstAt (p : X ⟶ Sp R) (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem fromSpecStalk_comp (p : X ⟶ Sp R) (x : X) : X.fromSpecStalk x ≫ p = spMap (cstAt p x) := by
  have h : p = X.toSpecΓ ≫ Spec.map p.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [h]
  rw [Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem mem_asIdeal_iff (p : X ⟶ Sp R) (x : X) (r : R) :
    r ∈ (p x).asIdeal ↔ cstAt p x r ∈ maximalIdeal (X.presheaf.stalk x) := by
  have h : p x = (X.fromSpecStalk x ≫ p) (closedPoint (X.presheaf.stalk x)) :=
    (congrArg p (Scheme.fromSpecStalk_closedPoint (x := x))).symm
  rw [h, fromSpecStalk_comp]
  rfl

variable [IsIntegral X]

theorem algebraMap_cstAt (p : X ⟶ Sp R) (x : X) (r : R) :
    algebraMap _ X.functionField (cstAt p x r) = GlobalTheory.Desc.cst p r := algebraMap_germ (U := ⊤) trivial _

theorem regAt_cst (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) := ⟨_, algebraMap_cstAt p x r⟩

theorem gp_comp (p : X ⟶ Sp R) : gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := fromSpecStalk_comp p _

theorem cst_comm {R₁ : Type} [CommRing R₁] {Y V : Scheme.{0}} [IsIntegral Y] {i : V ⟶ Y} {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ) (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (ρ : R →+* R₁)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h1, h2⟩ := h
  apply sp_inj
  rw [← sp_comp, ← sp_comp, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, ← h1, Category.assoc, w]
  simp only [Category.assoc]

theorem cst_injective [IsDomain R] (p : X ⟶ Sp R) [Surjective p] : Function.Injective (GlobalTheory.Desc.cst p) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨y, hy⟩ := p.surjective ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : cstAt p y r = 0 :=
    IsFractionRing.injective (X.presheaf.stalk y) X.functionField (by rw [algebraMap_cstAt, hr, map_zero])
  have h2 := (mem_asIdeal_iff p y r).2 (h1 ▸ zero_mem _)
  rw [hy] at h2
  exact h2

theorem exists_pow_mul_regAt (p : X ⟶ Sp R) (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 1) {r : R}
    (hr : r ∈ (p x).asIdeal) (u : X.functionField) : ∃ n : ℕ, RegAt x (GlobalTheory.Desc.cst p r ^ n * u) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) u
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, t, ht⟩ := exists_dvd_pow hx hb0 ((mem_asIdeal_iff p x r).1 hr)
  refine ⟨n, t * a, ?_⟩
  have hb1 : algebraMap _ X.functionField b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (X.presheaf.stalk x) X.functionField (h.trans (map_zero _).symm))
  rw [← algebraMap_cstAt p x, ← map_pow, ht, map_mul, map_mul]
  field_simp

def regAlg (p : X ⟶ Sp R) (x : X) : letI := (GlobalTheory.Desc.cst p).toAlgebra; Subalgebra R X.functionField :=
  letI := (GlobalTheory.Desc.cst p).toAlgebra
  { carrier := regSet x
    mul_mem' := RegAt.mul
    add_mem' := RegAt.add
    algebraMap_mem' := regAt_cst p x }

end Geo

theorem surjective_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] : Surjective G.hom := by
  have h : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w _
  haveI : Surjective ((η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom) := by rw [h]; exact ⟨Function.surjective_id⟩
  exact Surjective.of_comp (η[G] : 𝟙_ (Over S) ⟶ G).left _

theorem eq_closedPoint {T : Type} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (q : Sp T) {t : T} (ht : t ≠ 0)
    (hq : t ∈ q.asIdeal) : q = closedPoint T := by
  have hne : q.asIdeal ≠ ⊥ := fun h => ht (by simpa [h] using hq)
  exact PrimeSpectrum.ext (eq_maximalIdeal (Ideal.IsPrime.isMaximal q.isPrime hne))

theorem exists_closed_codim_one {E : Type} [CommRing E] [IsDomain E] [IsDiscreteValuationRing E] (H : Over (Sp E))
    [GrpObj H] [IsIntegral H.left] (hH : IsSemiAbelian H) :
    ∃ y : H.left, H.hom y = closedPoint E ∧ ringKrullDim (H.left.presheaf.stalk y) = 1 := by
  haveI := hH.smooth
  haveI := surjective_hom H
  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E
  obtain ⟨x, hx⟩ := H.hom.surjective (closedPoint E)
  obtain ⟨y, h1, h2⟩ := exists_vert_of_mem E H.left H.hom t ht.ne_zero ⟨x, by rw [hx]; exact ht.not_isUnit⟩
  exact ⟨y, eq_closedPoint _ ht.ne_zero h2, h1⟩

theorem exists_unram {R T : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing T]
    [IsLocalRing T] (ρ : R →+* T) (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1)
    (cen : spMap ρ (closedPoint T) = p) (etc : IsEtaleCompletion (Scheme.stalkClosedPointTo (spMap ρ)).hom)
    (unr : ((residue T).comp (Scheme.stalkClosedPointTo (spMap ρ)).hom).FormallyUnramified) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsLocalRing O) (_ : Algebra R O) (_ : IsLocalization.AtPrime O p.asIdeal)
      (φ : O →+* T) (π : O), IsLocalHom φ ∧ φ.comp (algebraMap R O) = ρ ∧ maximalIdeal T = Ideal.span {φ π} ∧
      ((residue T).comp φ).Finite ∧ ((residue T).comp φ).FormallyUnramified := by
  subst cen
  let y : PrimeSpectrum R := spMap ρ (closedPoint T)
  let A := (Spec (CommRingCat.of R)).presheaf.stalk y
  letI : Algebra R A := StructureSheaf.stalkAlgebra R y
  haveI hA : IsLocalization.AtPrime A y.asIdeal := StructureSheaf.IsLocalization.to_stalk R y
  have e : StructureSheaf.toStalk R y ≫ Scheme.stalkClosedPointTo (spMap ρ) = CommRingCat.ofHom ρ := by
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom ρ)
    rw [← Iso.inv_comp_eq] at h
    exact h
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing y.asIdeal.primeCompl A inferInstance
  haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A y.asIdeal.primeCompl_le_nonZeroDivisors
  have hic : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A _ y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal A]
    exact le_of_eq (congrArg (fun t : ℕ∞ => (t : WithBot ℕ∞)) hp)
  have h3 : IsIntegrallyClosed A ∧ ∀ P : Ideal A, P ≠ ⊥ → P.IsPrime → P = maximalIdeal A :=
    ⟨hic, fun P h h' => eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hd P h h')⟩
  have h4 : Submodule.IsPrincipal (maximalIdeal A) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 3 4).1 h3
  obtain ⟨π, hπ⟩ := h4
  refine ⟨A, inferInstance, inferInstance, inferInstance, hA, (Scheme.stalkClosedPointTo (spMap ρ)).hom, π,
    inferInstance, congrArg (·.hom) e, ?_, etc.2.2, unr⟩
  have h5 : (maximalIdeal A).map (Scheme.stalkClosedPointTo (spMap ρ)).hom = maximalIdeal T := etc.2.1
  have h6 : maximalIdeal A = Ideal.span {π} := hπ
  rw [← h5, h6, Ideal.map_span, Set.image_singleton]

theorem finite_separable {O T : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] [Algebra O T]
    [IsLocalHom (algebraMap O T)] (h : ((residue T).comp (algebraMap O T)).Finite)
    (h' : ((residue T).comp (algebraMap O T)).FormallyUnramified) :
    Module.Finite (ResidueField O) (ResidueField T) ∧ Algebra.IsSeparable (ResidueField O) (ResidueField T) := by
  haveI : Module.Finite O (ResidueField T) := RingHom.finite_algebraMap.1 h
  haveI : Algebra.FormallyUnramified O (ResidueField T) := RingHom.formallyUnramified_algebraMap.1 h'
  haveI : Module.Finite (ResidueField O) (ResidueField T) := Module.Finite.of_restrictScalars_finite O _ _
  haveI := Algebra.FormallyUnramified.of_restrictScalars O (ResidueField O) (ResidueField T)
  exact ⟨inferInstance, Algebra.FormallyUnramified.isSeparable _ _⟩

theorem pff_refl (X : Scheme.{0}) [IsIntegral X] : PFF (𝟙 X) (𝟙 X) (RingHom.id _) :=
  ⟨gp X, Category.comp_id _, by
    rw [show spMap (RingHom.id X.functionField) = 𝟙 _ from Spec.map_id _, Category.comp_id, Category.id_comp]⟩

end GaussDvr

open GaussDvr in

theorem gaussAt_chart_of_height_one : ∀ (σ : Setup) (p : Sp σ.R) (z : (σ.C p).G.left), p.asIdeal.height = 1 → Vert (σ.C p).G.hom (σ.ρ p σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C p).G.hom) (maximalIdeal (σ.C p).R) (σ.θ p) (σ.W p) (regSet z) := by
  intro σ p z hp hz
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have etc := (σ.C p).etc
  have unr := (σ.C p).unr
  have cen := (σ.C p).centre
  rw [σ.hρ p] at etc unr cen
  obtain ⟨O, _, _, _, _, φ, π, hloc, hφ, hm, hfin, hunr⟩ := exists_unram (σ.ρ p) p hp cen etc unr
  have hf : σ.ρ p σ.f ≠ 0 := flat_ne_zero _ (σ.flat p) σ.hf
  have hπ0 : φ π ≠ 0 := by
    intro h
    have := le_maximalIdeal ((σ.C p).G.hom z).isPrime.ne_top hz.2
    rw [hm, h, Ideal.span_singleton_zero] at this
    exact hf this
  haveI : IsDiscreteValuationRing (σ.C p).R := dvr_of_span hπ0 hm
  have hirr : Irreducible (φ π) := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπ0 hm
  have hcl : ∀ z', Vert (σ.C p).G.hom (σ.ρ p σ.f) z' → (σ.C p).G.hom z' = closedPoint _ :=
    fun z' h => eq_closedPoint _ hf h.2
  have hW : σ.W p = σ.θ p ⁻¹' regSet z := by
    have hreg : ∀ z', Vert (σ.C p).G.hom (σ.ρ p σ.f) z' → regSet z' = regSet z := fun z' h =>
      (GlobalTheory.T.gaussProperty_semiAbelian_flat_baseChange_dvr _ _ (RingHom.id _) (RingHom.Flat.id _) (Ideal.map_id _) (σ.C p).G (σ.C p).G (𝟙 _) (RingHom.id _)
        (σ.C p).semi (by
          rw [show spMap (RingHom.id (σ.C p).R) = 𝟙 _ from Spec.map_id _]
          exact IsPullback.id_horiz _) (pff_refl _) z z' (hcl z hz) (hcl z' h) hz.1 h.1).2.1
    ext u
    exact ⟨fun h => h z hz, fun h z' h' => show σ.θ p u ∈ regSet z' from (hreg z' h').symm ▸ h⟩
  rw [hW]
  haveI := surjective_hom (σ.C p).G
  have hc := cst_injective (σ.C p).G.hom
  have hcomm : (σ.θ p).comp σ.c₀ = (GlobalTheory.Desc.cst (σ.C p).G.hom).comp (σ.ρ p) :=
    cst_comm (σ.hθ p) _ _ _ (σ.cart p).w
  have hφ' : ∀ r, φ (algebraMap _ O r) = σ.ρ p r := fun r => RingHom.congr_fun hφ r
  have hunit : ∀ s : (PrimeSpectrum.asIdeal p).primeCompl, IsUnit (σ.c₀ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => ?_
    have h1 : GlobalTheory.Desc.cst (σ.C p).G.hom (σ.ρ p s) = 0 := by
      rw [← RingHom.comp_apply, ← hcomm, RingHom.comp_apply, h, map_zero]
    rw [← hφ'] at h1
    exact (((IsLocalization.map_units O s).map φ).map _).ne_zero h1
  letI : Algebra O (σ.C p).R := φ.toAlgebra
  haveI : IsLocalHom (algebraMap O (σ.C p).R) := hloc
  letI := (GlobalTheory.Desc.cst (σ.C p).G.hom).toAlgebra
  obtain ⟨_, _⟩ := finite_separable (O := O) (T := (σ.C p).R) hfin hunr
  refine gauss_of_key (O := O) (Ω := AlgebraicClosure (ResidueField (σ.C p).R)) hc (IsLocalization.lift hunit) (σ.θ p)
    ?_ π hirr (regAlg (σ.C p).G.hom z) (fun x => exists_pow_mul_regAt _ z hz.1 ?_ x) ?_
  · refine IsLocalization.ringHom_ext (PrimeSpectrum.asIdeal p).primeCompl ?_
    rw [RingHom.comp_assoc, IsLocalization.lift_comp, hcomm, RingHom.comp_assoc]
    exact congrArg _ hφ.symm
  · rw [hcl z hz]; exact hirr.not_isUnit
  intro s lam n r w hw y hy hrel
  have hker : ∀ g : ResidueField (σ.C p).R →+* AlgebraicClosure (ResidueField (σ.C p).R),
      RingHom.ker (g.comp (residue _)) = maximalIdeal _ := fun g => by
    rw [RingHom.ker_comp_of_injective _ g.injective, ker_residue]
  obtain ⟨E, _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, ha, hb, hab, hv, hva, hvb, hma, hH, ⟨pa, -⟩, ⟨pb, -⟩, fa, fb, hθ⟩ :=
    GlobalTheory.T.abelianSchemeDescentData_charts_common σ p p _ (s.toRingHom.comp (residue _)) ((algebraMap (ResidueField (σ.C p).R) _).comp (residue _))
      (hker _) (by
        ext t
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← hφ']
        exact s.commutes (residue O (algebraMap _ O t)))
  rw [hker] at hma
  have hab' : a.comp φ = b.comp φ := IsLocalization.ringHom_ext (PrimeSpectrum.asIdeal p).primeCompl (by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hφ, hab])
  have hπab : a (φ π) = b (φ π) := RingHom.congr_fun hab' π
  have hE : maximalIdeal E = Ideal.span {a (φ π)} := by rw [← hma, hm, Ideal.map_span, Set.image_singleton]
  have hmb : (maximalIdeal _).map b = maximalIdeal E := by rw [hE, hm, Ideal.map_span, Set.image_singleton, hπab]
  have ha0 : a (φ π) ≠ 0 := flat_ne_zero a ha hπ0
  haveI : IsDiscreteValuationRing E := dvr_of_span ha0 hE
  obtain ⟨y', hy', hd⟩ := exists_closed_codim_one H hH
  obtain ⟨-, hra, -⟩ := GlobalTheory.T.gaussProperty_semiAbelian_flat_baseChange_dvr _ _ a ha hma _ H πa θa (σ.C p).semi pa fa z y' (hcl z hz) hy' hz.1 hd
  obtain ⟨hG, -, hld⟩ := GlobalTheory.T.gaussProperty_semiAbelian_flat_baseChange_dvr _ _ b hb hmb _ H πb θb (σ.C p).semi pb fb z y' (hcl z hz) hy' hz.1 hd
  have := key_of_gauss hc (σ.θ p) a b (GlobalTheory.Desc.cst H.hom) θa θb
    (cst_comm fa _ _ _ (by rw [Category.id_comp]; exact pa.w)) (cst_comm fb _ _ _ (by rw [Category.id_comp]; exact pb.w))
    hθ hld v hvb hv (regAlg (σ.C p).G.hom z).toSubmodule (regSet y')
    (fun t ht => show t ∈ θa ⁻¹' regSet y' from hra.symm ▸ ht) hG (φ π) ha0
    (by rw [← RingHom.mem_ker, hv, hE]; exact Ideal.mem_span_singleton_self _) lam n r w hw y hy hrel
  have hva' : ∀ t, v (a t) = s (residue _ t) := fun t => RingHom.congr_fun hva t
  simpa only [hva'] using this

end GlobalTheory.Desc
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_at_height_one_vertical_point : ∀ (σ : Setup) (p : Sp σ.R) (z : (σ.C p).G.left), p.asIdeal.height = 1 → Vert (σ.C p).G.hom (σ.ρ p σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C p).G.hom) (maximalIdeal (σ.C p).R) (σ.θ p) (σ.W p) (regSet z) := by
  atlas_forward_decl GlobalTheory.Desc.gaussAt_chart_of_height_one
end
