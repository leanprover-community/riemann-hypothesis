import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
import Mathlib

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

open MvPolynomial

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} [Fintype ι]
  {K : Type*} [CommSemiring K] (σ : K →+* ℂ)

theorem hasFDerivAt_mv (q : MvPolynomial ι K) {h : V → ι → ℂ} {z0 : V} {Dh : ι → V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) :
    HasFDerivAt (fun z => eval₂ σ (h z) q) (∑ i, eval₂ σ (h z0) (pderiv i q) • Dh i) z0 := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (σ a) z0
  | add p q hp hq =>
    simp only [eval₂_add, map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    refine (hp.mul (hh i)).congr_fderiv ?_
    simp only [Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, eval₂_X, add_smul,
      Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [pderiv_X_self]
    · intro b _ hb
      classical
      rw [pderiv_X]
      simp [hb.symm]
    · simp

def xTerm {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P : Polynomial (MvPolynomial ι K)) : R :=
  P.sum fun n c => ψ (pderiv i c) * s ^ n

theorem xTerm_add {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P Q : Polynomial (MvPolynomial ι K)) : xTerm ψ s i (P + Q) = xTerm ψ s i P + xTerm ψ s i Q := by
  unfold xTerm
  exact Polynomial.sum_add_index _ _ _ (by simp) (by intros; simp [add_mul])

theorem xTerm_monomial {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (n : ℕ) (c : MvPolynomial ι K) : xTerm ψ s i (Polynomial.monomial n c) = ψ (pderiv i c) * s ^ n := by
  unfold xTerm
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem map_xTerm {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : MvPolynomial ι K →+* R)
    (f : R →+* S) (s : R) (i : ι) (P : Polynomial (MvPolynomial ι K)) :
    f (xTerm ψ s i P) = xTerm (f.comp ψ) (f s) i P := by
  unfold xTerm Polynomial.sum
  simp [map_sum]

theorem hasFDerivAt_eval₂ (P : Polynomial (MvPolynomial ι K)) {h : V → ι → ℂ} {g : V → ℂ} {z0 : V}
    {Dh : ι → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) (hg : HasFDerivAt g Dg z0) :
    HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z))
      ((Polynomial.derivative P).eval₂ (eval₂Hom σ (h z0)) (g z0) • Dg +
        ∑ i, xTerm (eval₂Hom σ (h z0)) (g z0) i P • Dh i) z0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add]
    refine (hp.add hq).congr_fderiv ?_
    simp only [map_add, Polynomial.eval₂_add, xTerm_add, add_smul, Finset.sum_add_distrib]
    abel
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial]
    refine ((hasFDerivAt_mv σ c hh).mul (hg.pow n)).congr_fderiv ?_
    simp only [Polynomial.derivative_monomial, xTerm_monomial, Polynomial.eval₂_monomial, coe_eval₂Hom,
      Finset.smul_sum, smul_smul, map_mul, map_natCast, nsmul_eq_mul]
    congr 1
    · congr 1; ring
    · exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

omit [Fintype ι] in

theorem exists_rel {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {y : ι → Ω}
    (hy : AlgebraicIndependent K y) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    ∃ P : Polynomial (MvPolynomial ι K), P.eval₂ (aeval y).toRingHom a = 0 ∧
      (Polynomial.derivative P).eval₂ (aeval y).toRingHom a ≠ 0 := by
  classical
  obtain ⟨q, hq0, hqa⟩ := ha
  let f : Algebra.adjoin K (Set.range y) →+* MvPolynomial ι K := hy.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f := hy.aevalEquiv.symm.injective
  have hcomp : (aeval y).toRingHom.comp f = algebraMap (Algebra.adjoin K (Set.range y)) Ω := by
    ext s
    have := hy.algebraMap_aevalEquiv (hy.aevalEquiv.symm s)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hex : ∃ n, ∃ P : Polynomial (MvPolynomial ι K), P ≠ 0 ∧
      P.eval₂ (aeval y).toRingHom a = 0 ∧ P.natDegree = n := by
    refine ⟨_, q.map f, (Polynomial.map_ne_zero_iff hf).mpr hq0, ?_, rfl⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hqa
  obtain ⟨P, hP0, hPa, hPn⟩ := Nat.find_spec hex
  refine ⟨P, hPa, fun hd => ?_⟩
  by_cases hD : Polynomial.derivative P = 0
  · have h0 : P.natDegree = 0 := Polynomial.derivative_eq_zero.mp hD
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.eval₂_C] at hPa
    have hc : P.coeff 0 = 0 := hy (by simpa using hPa)
    apply hP0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
  · have hne : P.natDegree ≠ 0 := fun h0 => hD (Polynomial.derivative_eq_zero.mpr h0)
    have hlt := Polynomial.natDegree_derivative_lt hne
    rw [hPn] at hlt
    exact Nat.find_min hex hlt ⟨_, hD, hd, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {ιB : Type} [Fintype ιB]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eval₂Hom_comp (φ : Ω →+* ℂ) (y : ιB → Ω) :
    eval₂Hom (φ.comp (algebraMap K Ω)) (φ ∘ y) = φ.comp (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp
  · intro b; simp

def coef (y : ιB → Ω) (a : Ω) (P : Polynomial (MvPolynomial ιB K)) (b : ιB) : Ω :=
  -(xTerm (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a b P) /
    (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a

theorem deriv_rel (φ : Ω →+* ℂ) {y : ιB → Ω} {a : Ω} (P : Polynomial (MvPolynomial ιB K))
    (hP' : (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a ≠ 0)
    {h : V → ιB → ℂ} {g : V → ℂ} {Dh : ιB → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ b, HasFDerivAt (fun z => h z b) (Dh b) 0) (hg : HasFDerivAt g Dg 0)
    (h0 : h 0 = φ ∘ y) (g0 : g 0 = φ a)
    (hrel : ∀ᶠ z in 𝓝 (0 : V), P.eval₂ (eval₂Hom (φ.comp (algebraMap K Ω)) (h z)) (g z) = 0) :
    Dg = ∑ b, φ (coef y a P b) • Dh b := by
  set σ := φ.comp (algebraMap K Ω)
  have hd := hasFDerivAt_eval₂ σ P hh hg
  have hz : HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z)) (0 : V →L[ℂ] ℂ) 0 :=
    (hasFDerivAt_const (0 : ℂ) (0 : V)).congr_of_eventuallyEq (hrel.mono fun z hz => hz)
  have heq := hd.unique hz
  rw [h0, g0, eval₂Hom_comp] at heq
  simp only [← Polynomial.hom_eval₂, ← map_xTerm] at heq
  set E := (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a
  have hE : φ E ≠ 0 := (map_ne_zero φ).mpr hP'
  apply smul_right_injective (V →L[ℂ] ℂ) hE
  simp only
  rw [eq_neg_of_add_eq_zero_left heq, Finset.smul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, coef, map_div₀, map_neg, mul_div_cancel₀ _ hE, neg_smul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoD

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC

noncomputable section

variable {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
  {Fr : Type*} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem zero_of_dense {U G : Set Fr} (hU : IsOpen U) (hUG : U ⊆ closure G) {F : Fr → ℂ}
    (hF : ContinuousOn F U) (h0 : ∀ y ∈ G ∩ U, F y = 0) : ∀ y ∈ U, F y = 0 := by
  have hsub : U ⊆ closure (G ∩ U) := by
    intro y hy
    have := hU.inter_closure ⟨hy, hUG hy⟩
    rwa [Set.inter_comm] at this
  exact Set.EqOn.of_subset_closure (f := F) (g := fun _ => 0) (fun y hy => h0 y hy) hF
    continuousOn_const Set.inter_subset_right hsub

theorem rel_deriv {ιB : Type} [Fintype ιB] (sg : K →+* ℂ) {U Gen : Set Fr} (hU : IsOpen U)
    (hUG : U ⊆ closure Gen) (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (vb : ιB → Fr → ℂ) (vj : Fr → ℂ) (hvb : ∀ b, ∀ y ∈ U, DifferentiableAt ℂ (vb b) y)
    (hvj : ∀ y ∈ U, DifferentiableAt ℂ vj y) (yB : ιB → Ω) (a : Ω)
    (hGb : ∀ y ∈ Gen ∩ U, ∀ b, vb b y = pt y (yB b)) (hGa : ∀ y ∈ Gen ∩ U, vj y = pt y a)
    (hy : AlgebraicIndependent K yB) (ha : IsAlgebraic (Algebra.adjoin K (Set.range yB)) a)
    (c : V → Fr) (hc : Differentiable ℂ c) (x : Fr) (hc0 : c 0 = x) (hx : x ∈ Gen ∩ U) :
    ∃ co : ιB → Ω, fderiv ℂ (fun z => vj (c z)) 0 =
      ∑ b, pt x (co b) • fderiv ℂ (fun z => vb b (c z)) 0 := by
  obtain ⟨P, hP, hP'⟩ := exists_rel hy ha
  refine ⟨coef yB a P, ?_⟩
  set F : Fr → ℂ := fun y => P.eval₂ (eval₂Hom sg (fun b => vb b y)) (vj y) with hFdef
  have hFcont : ContinuousOn F U := fun y hyU =>
    (hasFDerivAt_eval₂ sg P (h := fun y b => vb b y) (fun b => (hvb b y hyU).hasFDerivAt)
      (hvj y hyU).hasFDerivAt).continuousAt.continuousWithinAt
  have hF0 : ∀ y ∈ Gen ∩ U, F y = 0 := by
    intro y hyGU
    have hb : (fun b => vb b y) = pt y ∘ yB := funext (hGb y hyGU)
    show P.eval₂ (eval₂Hom sg (fun b => vb b y)) (vj y) = 0
    rw [hb, hGa y hyGU, ← hpt y hyGU.1, eval₂Hom_comp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hFU := zero_of_dense hU hUG hFcont hF0
  have hev : ∀ᶠ z in 𝓝 (0 : V), c z ∈ U :=
    hc.continuous.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU.mem_nhds hx.2)
  have hxU : c 0 ∈ U := by rw [hc0]; exact hx.2
  refine deriv_rel (pt x) P hP' (h := fun z b => vb b (c z)) (g := fun z => vj (c z))
    (fun b => ((hvb b (c 0) hxU).comp 0 (hc 0)).hasFDerivAt)
    ((hvj (c 0) hxU).comp 0 (hc 0)).hasFDerivAt ?_ ?_ ?_
  · funext b; show vb b (c 0) = pt x (yB b); rw [hc0]; exact hGb x hx b
  · show vj (c 0) = pt x a; rw [hc0]; exact hGa x hx
  · rw [hpt x hx.1]
    exact hev.mono fun z hz => hFU (c z) hz

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoD
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoB

open MvPolynomial

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem isAlgebraic_map {ιB : Type} {y : ιB → Ω} (hy : AlgebraicIndependent K y) [Algebra K ℂ]
    (φK : Ω →ₐ[K] ℂ) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    IsAlgebraic (Algebra.adjoin K (Set.range (φK ∘ y))) (φK a) := by
  have hY : AlgebraicIndependent K (φK ∘ y) := hy.map' φK.toRingHom.injective
  by_contra hc
  have h1 : AlgebraicIndependent K (fun o : Option ιB => o.elim (φK a) (φK ∘ y)) :=
    AlgebraicIndependent.option_iff.mpr ⟨hY, hc⟩
  have h2 : AlgebraicIndependent K (fun o : Option ιB => o.elim a y) := by
    refine AlgebraicIndependent.of_comp φK ?_
    convert h1 using 1
    funext o; cases o <;> rfl
  exact ((AlgebraicIndependent.option_iff.mp h2).2) ha

set_option maxHeartbeats 1000000 in

theorem gen_indep {ιB R : Type} [Fintype ιB] [Fintype R] {N : ℕ} (σ : K →+* ℂ) (φ : Ω →+* ℂ)
    (hφ : φ.comp (algebraMap K Ω) = σ) {y : ιB → Ω} (hy : IsTranscendenceBasis K y)
    (j0 : Fin (N + 1)) (u : Fin (N + 1) → Ω) (hu0 : u j0 = 1) (t : R → Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (R × Fin (N + 1)) K, Q ≠ 0 → eval₂ σ (fun p => t p.1 p.2) Q ≠ 0)
    (hrel : ∀ i, ∑ j, t i j * φ (u j) = 0) (hcard : Fintype.card ιB ≤ Fintype.card R) :
    ∀ p : MvPolynomial (R × {j // j ≠ j0}) Ω, p ≠ 0 → eval₂ φ (fun q => t q.1 q.2) p ≠ 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hcomm : ∀ k, φ (algebraMap K Ω k) = algebraMap K ℂ k := fun k => by
    rw [RingHom.algebraMap_toAlgebra, ← hφ]; rfl
  let φK : Ω →ₐ[K] ℂ := { toRingHom := φ, commutes' := hcomm }
  have hφK : ∀ a, φK a = φ a := fun _ => rfl
  let T : R × Fin (N + 1) → ℂ := fun p => t p.1 p.2
  have hT : AlgebraicIndependent K T := by
    rw [AlgebraicIndependent, injective_iff_map_eq_zero]
    intro Q hQ
    by_contra h
    exact ht Q h (by simpa [aeval_def, RingHom.algebraMap_toAlgebra] using hQ)
  let Y : ιB → ℂ := φK ∘ y
  let S : R × {j // j ≠ j0} → ℂ := fun q => t q.1 q.2
  let Z : ιB ⊕ (R × {j // j ≠ j0}) → ℂ := Sum.elim Y S
  have hYZ : Algebra.adjoin K (Set.range Y) ≤ Algebra.adjoin K (Set.range Z) :=
    Algebra.adjoin_mono (by rintro _ ⟨b, rfl⟩; exact ⟨Sum.inl b, rfl⟩)
  let M := AlgebraicIndependent.matroid K ℂ

  have hsub : Set.range T ⊆ M.closure (Set.range Z) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    let A' := Subalgebra.algebraicClosure (Algebra.adjoin K (Set.range Z)) ℂ
    have hin : ∀ q, S q ∈ A' := fun q => by
      rw [Subalgebra.mem_algebraicClosure]
      have hm : S q ∈ Algebra.adjoin K (Set.range Z) := Algebra.subset_adjoin ⟨Sum.inr q, rfl⟩
      exact isAlgebraic_algebraMap (⟨S q, hm⟩ : Algebra.adjoin K (Set.range Z))
    have hu : ∀ j, φ (u j) ∈ A' := fun j => by
      rw [Subalgebra.mem_algebraicClosure]
      have h1 := isAlgebraic_map hy.1 φK (hy.isAlgebraic.isAlgebraic (u j))
      exact h1.tower_top_of_subalgebra_le hYZ
    rintro _ ⟨⟨i, j⟩, rfl⟩
    show t i j ∈ A'
    by_cases hj : j = j0
    · subst hj
      have h2 := hrel i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu0, map_one, mul_one] at h2
      have h3 : t i j = -∑ k ∈ Finset.univ.erase j, t i k * φ (u k) := eq_neg_of_add_eq_zero_left h2
      rw [h3]
      refine A'.neg_mem (A'.sum_mem fun k hk => A'.mul_mem ?_ (hu k))
      exact hin (i, ⟨k, Finset.ne_of_mem_erase hk⟩)
    · exact hin (i, ⟨j, hj⟩)
  have hI : M.Indep (Set.range T) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hT.to_subtype_range
  have h0 := hI.encard_le_eRk_of_subset hsub
  rw [Matroid.eRk_closure_eq] at h0
  have h1 := hT.injective.encard_range.trans h0
  have h2 := M.eRk_le_encard (Set.range Z)
  let rng := Finset.univ.image Z
  have hrng : Set.range Z = ↑rng := by simp [rng]
  have h3 : (Set.range Z).encard = rng.card := by rw [hrng, Set.encard_coe_eq_coe_finsetCard]
  have h4 : rng.card ≤ Fintype.card (ιB ⊕ R × {j // j ≠ j0}) :=
    Finset.card_image_le.trans (by simp)
  have hcardT : ENat.card (R × Fin (N + 1)) = ((Fintype.card R * (N + 1) : ℕ) : ℕ∞) := by
    simp [ENat.card_eq_coe_fintype_card]
  have hcardZ : Fintype.card (ιB ⊕ R × {j // j ≠ j0}) = Fintype.card ιB + Fintype.card R * N := by
    simp [Fintype.card_sum, Fintype.card_prod]
  have hRN : Fintype.card R * (N + 1) = Fintype.card R * N + Fintype.card R := by ring
  have hle : Fintype.card R * (N + 1) ≤ rng.card := by
    have := h1.trans (h2.trans h3.le)
    rw [hcardT] at this
    exact_mod_cast this
  have heq : rng.card = Fintype.card (ιB ⊕ R × {j // j ≠ j0}) :=
    le_antisymm h4 (by rw [hcardZ]; omega)
  have hinj : Function.Injective Z := by
    have := Finset.card_image_iff.mp (heq.trans Finset.card_univ.symm)
    exact fun a b hab => this (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  have hindZ : M.Indep (Set.range Z) := by
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.finite_range Z)]
    refine le_antisymm h2 ?_
    rw [h3]
    calc (rng.card : ℕ∞) ≤ ((Fintype.card R * (N + 1) : ℕ) : ℕ∞) := by
          exact_mod_cast (show rng.card ≤ Fintype.card R * (N + 1) by rw [heq, hcardZ]; omega)
      _ = ENat.card (R × Fin (N + 1)) := hcardT.symm
      _ ≤ _ := h1
  have hZ : AlgebraicIndependent K Z :=
    (algebraicIndependent_subtype_range hinj).mp (AlgebraicIndependent.matroid_indep_iff.mp hindZ)
  have hZ' : AlgebraicIndependent K (Sum.elim S Y) := by
    have := hZ.comp (Equiv.sumComm _ _) (Equiv.injective _)
    convert this using 1
    funext a; cases a <;> rfl
  have hS : AlgebraicIndependent (Algebra.adjoin K (Set.range Y)) S :=
    (AlgebraicIndependent.sumElim_iff.mp hZ').2
  let R0 := Algebra.adjoin K (Set.range y)
  have hmap : ∀ s : R0, (φK.comp R0.val) s ∈ Algebra.adjoin K (Set.range Y) := by
    intro s
    have h : φK (s : Ω) ∈ R0.map φK := Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩
    rw [AlgHom.map_adjoin, ← Set.range_comp] at h
    exact h
  let ρ : R0 →ₐ[K] Algebra.adjoin K (Set.range Y) := (φK.comp R0.val).codRestrict _ hmap
  letI : Algebra Ω ℂ := φ.toAlgebra
  letI : Algebra R0 ℂ := (φ.comp (algebraMap R0 Ω)).toAlgebra
  have hS0 : AlgebraicIndependent R0 S := by
    refine AlgebraicIndependent.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range Y)) (B := ℂ)
      ρ.toRingHom (RingHom.id ℂ) ?_ ?_ ?_
    · simpa using hS
    · intro a b h
      apply Subtype.ext
      apply φ.injective
      exact congrArg Subtype.val h
    · ext s; rfl
  have hSΩ : AlgebraicIndependent Ω S := by
    have htow : IsScalarTower R0 Ω ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have halg := hy.isAlgebraic
    exact @AlgebraicIndependent.extendScalars _ R0 ℂ S Ω _ _ _ _ _ _ htow _ hS0 halg
  intro p hp hev
  apply hp
  apply hSΩ
  simpa [aeval_def, RingHom.algebraMap_toAlgebra] using hev

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoB
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE

open MvPolynomial

noncomputable section

def pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) : MvPolynomial (Fin n × {j // j ≠ j0}) Ω :=
  (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))).det

theorem pdet_ne {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1) : pdet e a ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)) h0
  rw [map_zero, pdet, RingHom.map_det] at h1
  have h2 : (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)).mapMatrix
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))) = 1 := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      eval_X, eval_C, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ha,
      Matrix.one_apply]
    rw [Pi.single_apply]
    simp [e.apply_eq_iff_eq, eq_comm]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem eval_pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (φ : Ω →+* ℂ) (t : Fin (n + 1) × Fin (N + 1) → ℂ) :
    eval₂ φ (fun q : Fin n × {j // j ≠ j0} => t (q.1.succ, q.2.1)) (pdet e a) =
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det := by
  classical
  rw [pdet, ← coe_eval₂Hom, RingHom.map_det]
  congr 1
  ext i k
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem det_ne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n N : ℕ} (sg : K →+* ℂ)
    (φ : Ω →+* ℂ) (hφ : φ.comp (algebraMap K Ω) = sg) (j0 : Fin (N + 1)) (u : Fin (N + 1) → Ω)
    (hu0 : u j0 = 1) (B : Set {j // j ≠ j0}) [Fintype B]
    (hy : IsTranscendenceBasis K (fun b : B => u b.1.1)) (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1)
    (t : Fin (n + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (n + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hrel : ∀ i : Fin n, ∑ j, t (i.succ, j) * φ (u j) = 0) :
    (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det ≠ 0 := by
  classical
  have hcard : Fintype.card B ≤ Fintype.card (Fin n) := (Fintype.card_congr e).symm.le
  let f : Fin n × Fin (N + 1) → Fin (n + 1) × Fin (N + 1) := fun p => (p.1.succ, p.2)
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, Prod.mk.injEq, Fin.succ_inj] at h
    rw [h.1, h.2]
  have ht' : ∀ Q : MvPolynomial (Fin n × Fin (N + 1)) K, Q ≠ 0 →
      eval₂ sg (fun p => (fun i j => t (i.succ, j)) p.1 p.2) Q ≠ 0 := by
    intro Q hQ
    have h1 := ht (rename f Q) (by simpa using (rename_injective f hf).ne hQ)
    rwa [eval₂_rename] at h1
  have hgen : ∀ p : MvPolynomial (Fin n × {j // j ≠ j0}) Ω, p ≠ 0 →
      eval₂ φ (fun q => t (q.1.succ, q.2.1)) p ≠ 0 :=
    SCoB.gen_indep (ιB := B) (R := Fin n) sg φ hφ hy j0 u hu0 (fun i j => t (i.succ, j)) ht' hrel hcard
  rw [← eval_pdet e a φ t]
  exact hgen _ (pdet_ne e a ha)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoG

noncomputable section

theorem finale {n N : ℕ} (Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ))
    (t : Fin (n + 1) × Fin (N + 1) → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)) (hM : M.det ≠ 0)
    (key : ∀ ξ, (∀ k, w k ξ = 0) → ξ = 0)
    (hrow : ∀ i, ∑ j, t (i.succ, j) • Dv j = ∑ k, M i k • w k) (den : ℂ) (hden : den ≠ 0) :
    (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i => den⁻¹ • ∑ j, t (i.succ, j) • Dv j)).det ≠ 0 := by
  classical
  set L := (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i => den⁻¹ • ∑ j, t (i.succ, j) • Dv j)) with hL
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    apply key
    have hmv : M.mulVec (fun k => w k ξ) = 0 := by
      funext i
      have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) hξ
      simp only [hL, ContinuousLinearMap.comp_apply] at h1
      have h2 : den⁻¹ * (∑ j, t (i.succ, j) • Dv j) ξ = 0 := by simpa using h1
      have h3 := (mul_eq_zero.mp h2).resolve_left (inv_ne_zero hden)
      rw [hrow i] at h3
      simpa [Matrix.mulVec, dotProduct] using h3
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hmv)
  have hU : IsUnit (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
    exact hinj
  exact (LinearMap.isUnit_det _ hU).ne_zero

open Filter Topology in

theorem target {Fr : Type*} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N : ℕ}
    (W : Fin (N + 1) → Fr → ℂ) (c : EuclideanSpace ℂ (Fin n) → Fr) (j0 : Fin (N + 1))
    (hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), W j0 (c z) ≠ 0)
    (Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ))
    (hDv : ∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0)
    (t : Fin (n + 1) × Fin (N + 1) → ℂ) (hx0 : W j0 (c 0) ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t (i.succ, j) * W j (c 0) = 0) (hw : ∑ j, t (0, j) * W j (c 0) ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun i =>
      (∑ j, t (i.succ, j) * W j (c z)) / (∑ j, t (0, j) * W j (c z)) : EuclideanSpace ℂ (Fin n)))
      (((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
        (ContinuousLinearMap.pi fun i =>
          ((∑ j, t (0, j) * W j (c 0)) / W j0 (c 0))⁻¹ • ∑ j, t (i.succ, j) • Dv j)) 0 := by
  set Num : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun i z => ∑ j, t (i.succ, j) * (W j (c z) / W j0 (c z))
    with hNumd
  set Den : EuclideanSpace ℂ (Fin n) → ℂ := fun z => ∑ j, t (0, j) * (W j (c z) / W j0 (c z)) with hDend
  have hNum : ∀ i, HasFDerivAt (Num i) (∑ j, t (i.succ, j) • Dv j) 0 := fun i =>
    HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _
  have hDen : HasFDerivAt Den (∑ j, t (0, j) • Dv j) 0 :=
    HasFDerivAt.fun_sum fun j _ => (hDv j).const_mul _
  have hNum0 : ∀ i, Num i 0 = 0 := by
    intro i
    simp only [hNumd, mul_div_assoc']
    rw [← Finset.sum_div, hs i, zero_div]
  have hDen0' : Den 0 = (∑ j, t (0, j) * W j (c 0)) / W j0 (c 0) := by
    simp only [hDend, mul_div_assoc']
    rw [← Finset.sum_div]
  have hDen0 : Den 0 ≠ 0 := by rw [hDen0']; exact div_ne_zero hw hx0
  have hQ : ∀ i, HasFDerivAt (fun z => Num i z * (Den z)⁻¹) ((Den 0)⁻¹ • ∑ j, t (i.succ, j) • Dv j) 0 := by
    intro i
    have hinv := (hDen.differentiableAt.inv hDen0).hasFDerivAt
    have h := (hNum i).mul hinv
    rw [hNum0 i, zero_smul, zero_add] at h
    exact h
  rw [← hDen0']
  have h1 := ((EuclideanSpace.equiv (Fin n) ℂ).symm.hasFDerivAt).comp (0 : EuclideanSpace ℂ (Fin n))
    (hasFDerivAt_pi.2 hQ)
  refine h1.congr_of_eventuallyEq (hev.mono fun z hz => ?_)
  show (WithLp.toLp 2 fun i => _ : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => _
  congr 1
  funext i
  simp only [hNumd, hDend, mul_div_assoc']
  rw [← Finset.sum_div, ← Finset.sum_div, inv_div, div_mul_div_cancel₀ hz]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoG
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoF

open MvPolynomial Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
theorem part1 {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    {Fr : Type} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N D : ℕ} (hD : n = D) (sg : K →+* ℂ)
    {dom Gen : Set Fr} (hdom : IsOpen dom) (hGs : Gen ⊆ dom) (hGd : dom ⊆ closure Gen)
    (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (htr : Algebra.trdeg K Ω = D)
    (W : Fin (N + 1) → Fr → ℂ) (hW : ∀ j, DifferentiableOn ℂ (W j) dom)
    (u : Fin (N + 1) → Ω) (j0 : Fin (N + 1)) (hWu : ∀ y ∈ Gen, ∀ j, W j y = pt y (u j) * W j0 y)
    (c : EuclideanSpace ℂ (Fin n) → Fr) (hc : Differentiable ℂ c) {x : Fr} (hc0 : c 0 = x)
    (hx : x ∈ Gen) (hx0 : W j0 x ≠ 0) (jj : Fin n → Fin (N + 1))
    (hJ : (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) 0).det ≠ 0)
    (t : Fin (D + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) * W j x = 0) :
    ∃ Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ),
      (∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0) ∧
      ∃ (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)), M.det ≠ 0 ∧
      (∀ ξ, (∀ k, w k ξ = 0) → ξ = 0) ∧ ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) • Dv j =
        ∑ k, M i k • w k := by
  subst hD
  simp only [Fin.cast_eq_self] at hs ⊢
  set U : Set Fr := dom ∩ W j0 ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := (hW j0).continuousOn.isOpen_inter_preimage hdom isOpen_compl_singleton
  have hUG : U ⊆ closure Gen := fun y hy => hGd hy.1
  have hxU : x ∈ Gen ∩ U := ⟨hx, hGs hx, hx0⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (N + 1) → Fr → ℂ, v = fun j y => W j y / W j0 y := ⟨_, rfl⟩
  have hvd : ∀ j, ∀ y ∈ U, DifferentiableAt ℂ (v j) y := fun j y hy => by
    have h : DifferentiableAt ℂ (fun y => W j y * (W j0 y)⁻¹) y :=
      ((hW j).differentiableAt (hdom.mem_nhds hy.1)).mul
        (((hW j0).differentiableAt (hdom.mem_nhds hy.1)).inv hy.2)
    have hv' : v j = fun y => W j y * (W j0 y)⁻¹ := by rw [hv]; exact funext fun y => div_eq_mul_inv _ _
    rw [hv']; exact h
  have hvG : ∀ y ∈ Gen ∩ U, ∀ j, v j y = pt y (u j) := fun y hy j => by
    rw [hv]; show W j y / W j0 y = _
    rw [hWu y hy.1 j, mul_div_cancel_right₀ _ hy.2.2]
  have hu0 : u j0 = 1 := by
    have h := hvG x hxU j0
    rw [hv] at h
    change W j0 x / W j0 x = _ at h
    rw [div_self hx0] at h
    exact (pt x).injective (by rw [map_one]; exact h.symm)

  let u' : {j : Fin (N + 1) // j ≠ j0} → Ω := fun j => u j.1
  obtain ⟨B, hB⟩ := ((AlgebraicIndependent.matroid K Ω).comap u').exists_isBasis Set.univ
    (by rw [Matroid.comap_ground_eq, AlgebraicIndependent.matroid_e, Set.preimage_univ])
  rw [Matroid.comap_isBasis_iff] at hB
  obtain ⟨hB1, hBinj, -⟩ := hB
  haveI : Fintype B := Fintype.ofFinite B
  let yB : B → Ω := fun b => u b.1.1
  have hyB : AlgebraicIndependent K yB := by
    have h1 := AlgebraicIndependent.matroid_indep_iff.mp hB1.indep
    have h2 := h1.comp (Equiv.Set.imageOfInjOn u' B hBinj) (Equiv.injective _)
    convert h2 using 1
    funext b; rfl
  have hrange : Set.range yB = u' '' B := by
    ext w; simp [yB, u']
  have halg : ∀ j : {j : Fin (N + 1) // j ≠ j0}, IsAlgebraic (Algebra.adjoin K (Set.range yB)) (u j.1) := by
    intro j
    have h1 := hB1.subset_closure (Set.mem_image_of_mem u' (Set.mem_univ j))
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure] at h1
    rwa [hrange]

  have hrel : ∀ j : {j : Fin (N + 1) // j ≠ j0}, ∃ co : B → Ω, fderiv ℂ (fun z => v j.1 (c z)) 0 =
      ∑ b, pt x (co b) • fderiv ℂ (fun z => v b.1.1 (c z)) 0 := fun j =>
    SCoD.rel_deriv sg hU hUG pt hpt (fun b => v b.1.1) (v j.1) (fun b => hvd b.1.1) (hvd j.1) yB (u j.1)
      (fun y hy b => hvG y hy b.1.1) (fun y hy => hvG y hy j.1) hyB (halg j) c hc x hc0 hxU
  choose co hco using hrel
  let a : {j : Fin (N + 1) // j ≠ j0} → B → Ω := fun j => by
    classical exact if hj : j ∈ B then Pi.single ⟨j, hj⟩ 1 else co j
  have ha : ∀ b : B, a b.1 = Pi.single b 1 := fun b => by simp [a, b.2]
  let Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) := fun j => fderiv ℂ (fun z => v j (c z)) 0
  have hDa : ∀ j : {j : Fin (N + 1) // j ≠ j0}, Dv j.1 = ∑ b, pt x (a j b) • Dv b.1.1 := by
    intro j
    by_cases hj : j ∈ B
    · simp only [a, dif_pos hj]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    · simp only [a, dif_neg hj]; exact hco j
  have hxU' : c 0 ∈ U := by rw [hc0]; exact hxU.2
  have hDv : ∀ j, HasFDerivAt (fun z => v j (c z)) (Dv j) 0 := fun j =>
    ((hvd j (c 0) hxU').comp 0 (hc 0)).hasFDerivAt
  have hevU : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), c z ∈ U :=
    hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU')
  have hD0 : Dv j0 = 0 := by
    have h1 : HasFDerivAt (fun z => v j0 (c z)) (0 : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) 0 :=
      (hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq
        (hevU.mono fun z hz => by rw [hv]; exact div_self hz.2)
    exact (hDv j0).unique h1
  have hall : ∀ ξ, (∀ b : B, Dv b.1.1 ξ = 0) → ∀ j, Dv j ξ = 0 := by
    intro ξ hξ j
    by_cases hj : j = j0
    · rw [hj, hD0]; rfl
    · rw [hDa ⟨j, hj⟩, ContinuousLinearMap.sum_apply]
      exact Finset.sum_eq_zero fun b _ => by rw [ContinuousLinearMap.smul_apply, hξ b, smul_zero]

  let eqv := (EuclideanSpace.equiv (Fin n) ℂ).symm
  let Lc : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (eqv : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp (ContinuousLinearMap.pi fun k => Dv (jj k))
  have hLc : HasFDerivAt (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) Lc 0 := by
    have h1 : HasFDerivAt (fun z => fun k => v (jj k) (c z)) (ContinuousLinearMap.pi fun k => Dv (jj k)) 0 :=
      hasFDerivAt_pi.2 fun k => hDv (jj k)
    have hfun : (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
        W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) = eqv ∘ fun z => fun k => v (jj k) (c z) := by
      rw [hv]; rfl
    rw [hfun]
    exact eqv.hasFDerivAt.comp 0 h1
  rw [hLc.fderiv] at hJ
  have hLc_inj : Function.Injective Lc := by
    have h1 : IsUnit (Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJ)
    exact ((Module.End.isUnit_iff _).mp h1).injective
  have key : ∀ ξ, (∀ b : B, Dv b.1.1 ξ = 0) → ξ = 0 := by
    intro ξ hξ
    apply hLc_inj
    rw [map_zero]
    have h2 : (fun k => Dv (jj k) ξ) = 0 := funext fun k => hall ξ hξ (jj k)
    show eqv (fun k => Dv (jj k) ξ) = 0
    rw [h2, map_zero]

  have hcard1 : Fintype.card B ≤ n := by
    have h := hyB.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fintype] at h
    exact_mod_cast h
  have hcard2 : n ≤ Fintype.card B := by
    let Φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (B → ℂ) :=
      (ContinuousLinearMap.pi fun b : B => Dv b.1.1 : EuclideanSpace ℂ (Fin n) →L[ℂ] (B → ℂ)).toLinearMap
    have hinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro ξ hξ
      exact key ξ fun b => congrFun hξ b
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using h
  have hcardB : Fintype.card B = n := le_antisymm hcard1 hcard2
  have hyT : IsTranscendenceBasis K yB :=
    hyB.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fintype, hcardB])
  let e : Fin n ≃ B := (Fintype.equivFinOfCardEq hcardB).symm
  have hrelx : ∀ i : Fin n, ∑ j, t (i.succ, j) * pt x (u j) = 0 := by
    intro i
    have h := hs i
    have h2 : ∑ j, t (i.succ, j) * W j x = (∑ j, t (i.succ, j) * pt x (u j)) * W j0 x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hWu x hx j]; ring
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_right hx0
  have hdet := SCoE.det_ne sg (pt x) (hpt x hx) j0 u hu0 B hyT e a ha t ht hrelx
  have hDv' : ∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0 := by
    intro j; have h := hDv j; rw [hv] at h; exact h
  clear_value e a Dv
  refine ⟨Dv, hDv', ?_⟩
  refine ⟨_, fun k => Dv (e k).1.1, hdet, ?_, ?_⟩
  · intro ξ hξ
    apply key
    intro b
    have h1 : Dv (e (e.symm b)).1.1 ξ = 0 := hξ (e.symm b)
    rwa [Equiv.apply_symm_apply] at h1
  · intro i
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j0, hD0, smul_zero, zero_add]
    have hj : ∀ j : {j : Fin (N + 1) // j ≠ j0}, t (i.succ, j.1) • Dv j.1 =
        ∑ b, (t (i.succ, j.1) * pt x (a j b)) • Dv b.1.1 := fun j => by
      rw [hDa j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_smul]
    exact (e.sum_comp (fun b => ∑ j : {j : Fin (N + 1) // j ≠ j0}, (t (i.succ, j.1) * pt x (a j b)) • Dv b.1.1)).symm

theorem core {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    {Fr : Type} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N D : ℕ} (hD : n = D) (sg : K →+* ℂ)
    {dom Gen : Set Fr} (hdom : IsOpen dom) (hGs : Gen ⊆ dom) (hGd : dom ⊆ closure Gen)
    (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (htr : Algebra.trdeg K Ω = D)
    (W : Fin (N + 1) → Fr → ℂ) (hW : ∀ j, DifferentiableOn ℂ (W j) dom)
    (u : Fin (N + 1) → Ω) (j0 : Fin (N + 1)) (hWu : ∀ y ∈ Gen, ∀ j, W j y = pt y (u j) * W j0 y)
    (c : EuclideanSpace ℂ (Fin n) → Fr) (hc : Differentiable ℂ c) {x : Fr} (hc0 : c 0 = x)
    (hx : x ∈ Gen) (hx0 : W j0 x ≠ 0) (jj : Fin n → Fin (N + 1))
    (hJ : (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) 0).det ≠ 0)
    (t : Fin (D + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) * W j x = 0)
    (hw : ∑ j, t (0, j) * W j x ≠ 0) :
    (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun i =>
      (∑ j, t ((Fin.cast hD i).succ, j) * W j (c z)) / (∑ j, t (0, j) * W j (c z)) :
        EuclideanSpace ℂ (Fin n))) 0).det ≠ 0 := by
  subst hD
  obtain ⟨Dv, hDv, M, w, hM, key, hrow⟩ :=
    part1 rfl sg hdom hGs hGd pt hpt htr W hW u j0 hWu c hc hc0 hx hx0 jj hJ t ht hs
  simp only [Fin.cast_eq_self] at hrow hs ⊢
  have hxd : c 0 ∈ dom := by rw [hc0]; exact hGs hx
  have hcx : ContinuousAt (fun z => W j0 (c z)) 0 :=
    ((hW j0).differentiableAt (hdom.mem_nhds hxd)).continuousAt.comp (hc 0).continuousAt
  have hx0' : W j0 (c 0) ≠ 0 := by rw [hc0]; exact hx0
  have hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), W j0 (c z) ≠ 0 := hcx.eventually_ne hx0'
  have hw' : ∑ j, t (0, j) * W j (c 0) ≠ 0 := by rw [hc0]; exact hw
  have hT := SCoG.target W c j0 hev Dv hDv t hx0' (by rw [hc0]; exact hs) hw'
  rw [hT.fderiv]
  exact SCoG.finale Dv t M w hM key hrow _ (div_ne_zero hw' hx0')

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoF
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

namespace SchubertCoordinates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem diff_coord {n : ℕ} (i : Fin n) : Differentiable ℂ fun v : V n => v i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable

theorem diff_nmat (X : FD.Data E r) (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  split_ifs
  · exact diff_coord _
  · exact differentiable_const _
  · exact differentiable_const _

theorem diff_cpt (X : FD.Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  unfold cpt rmul
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [mat, Matrix.mul_apply, Matrix.of_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (diff_nmat X τ k b)

theorem nmat_zero (X : FD.Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : b < a
  · have h2 : a ≠ b := fun h => by subst h; exact lt_irrefl _ h1
    simp [h1, h2]
    rfl
  · simp [h1]

theorem cpt_zero (X : FD.Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  funext τ
  show (mat x τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [nmat_zero, Matrix.mul_one]
  rfl

theorem cont_gram (X : FD.Data E r) (τ : X.Ψ) :
    Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

theorem isOpen_dom (X : FD.Data E r) : IsOpen X.dom := by
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
    intro τ i
    refine Complex.continuous_re.comp ?_
    unfold dmin lminor
    exact Continuous.matrix_det ((cont_gram X τ).matrix_submatrix _ _)
  have hset : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [FD.Data.dom, GG, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter (isOpen_ne_fun (hdet τ) continuous_const)
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))

end SchubertCoordinates

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]


end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
