import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

section Devissage

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem sup_span_inf_eq' {I : Ideal (MRingOver F ι)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) {g : MRingOver F ι}
    {δ : K → ℕ} (hg : g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ) {d : K → ℕ} (hd : δ ≤ d) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ (I ⊔ Ideal.span {g}).restrictScalars F =
      (weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ I.restrictScalars F) ⊔
        (weightedHomogeneousSubmodule F (mw (ι := ι)) (d - δ)).map (LinearMap.mulLeft F g) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨hxd, hx⟩ := Submodule.mem_inf.mp hx
    rw [Submodule.restrictScalars_mem, Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hdd : d - δ + δ = d := tsub_add_cancel_of_le hd
    have key := DirectSum.coe_decompose_mul_add_of_right_mem
      (𝒜 := weightedHomogeneousSubmodule F (mw (ι := ι))) (a := c) (i := d - δ) hg
    rw [hdd] at key
    have hx' := DirectSum.decompose_of_mem_same (ℳ := weightedHomogeneousSubmodule F (mw (ι := ι))) hxd
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, key] at hx'
    rw [← hx']
    refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨SetLike.coe_mem _, ?_⟩)
      (Submodule.mem_map.mpr ⟨_, SetLike.coe_mem
        ((DirectSum.decompose (weightedHomogeneousSubmodule F (mw (ι := ι))) c) (d - δ)), ?_⟩)
    · rw [Submodule.restrictScalars_mem]
      exact hI d ha
    · rw [LinearMap.mulLeft_apply, mul_comm]
  · refine sup_le (inf_le_inf_left _ ?_) ?_
    · intro x hx
      rw [Submodule.restrictScalars_mem] at hx ⊢
      exact Ideal.mem_sup_left hx
    · rintro y ⟨z, hz, rfl⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [LinearMap.mulLeft_apply]
        have := SetLike.GradedMul.mul_mem hg hz
        rwa [add_tsub_cancel_of_le hd] at this
      · rw [Submodule.restrictScalars_mem, LinearMap.mulLeft_apply]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))



theorem colon_isHomogeneous {I : Ideal (MRingOver F ι)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) {g : MRingOver F ι}
    {δ : K → ℕ} (hg : g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ) :
    (I.colon {g}).IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
  intro i x hx
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
  have := hI (i + δ) hx
  rwa [DirectSum.coe_decompose_mul_add_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (mw (ι := ι))) hg] at this

end Devissage

section Lex

def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun a := toLex fun i => a ((Fintype.equivFin K).symm i)
  map_zero' := rfl
  map_add' _ _ := rfl

instance lexDecEq : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq

theorem lexDeg_injective : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  have h' : (fun i => a ((Fintype.equivFin K).symm i)) = fun i => b ((Fintype.equivFin K).symm i) :=
    toLex.injective h
  funext k
  simpa using congrFun h' (Fintype.equivFin K k)

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem weight_lex (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun p => lexDeg (mw (ι := ι) p)) m = lexDeg (Finsupp.weight (mw (ι := ι)) m) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]

theorem mem_lex_of_mem {x : MRingOver F ι} {d : K → ℕ}
    (hx : x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) d) :
    x ∈ weightedHomogeneousSubmodule F (fun p => lexDeg (mw (ι := ι) p)) (lexDeg d) := by
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro m hm
  rw [weight_lex, hx hm]

theorem homog_of_lex {x : MRingOver F ι} {l : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : x ∈ weightedHomogeneousSubmodule F (fun p => lexDeg (mw (ι := ι) p)) l) :
    ∃ d, x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) d := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  by_cases h : ∃ m, coeff m x ≠ 0
  · obtain ⟨m₀, hm₀⟩ := h
    refine ⟨Finsupp.weight (mw (ι := ι)) m₀, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    intro m hm
    exact lexDeg_injective (by rw [← weight_lex, ← weight_lex, hx hm, hx hm₀])
  · push_neg at h
    refine ⟨0, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    intro m hm
    exact absurd (h m) hm

theorem span_forms_eq {P : Ideal (MRingOver F ι)}
    (hP : P.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) :
    P = Ideal.span {x | x ∈ P ∧ ∃ d, x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) d} := by
  classical
  apply le_antisymm
  · intro r hr
    rw [← DirectSum.sum_support_decompose (weightedHomogeneousSubmodule F (mw (ι := ι))) r]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨hP i hr, i, SetLike.coe_mem _⟩
  · rw [Ideal.span_le]
    rintro x ⟨hx, -⟩
    exact hx

theorem isHomogeneous_lex {P : Ideal (MRingOver F ι)}
    (hP : P.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) :
    P.IsHomogeneous (weightedHomogeneousSubmodule F (fun p => lexDeg (mw (ι := ι) p))) := by
  rw [span_forms_eq hP]
  apply Ideal.homogeneous_span
  rintro x ⟨-, d, hd⟩
  exact ⟨lexDeg d, mem_lex_of_mem hd⟩

theorem isPrime_of_forms {P : Ideal (MRingOver F ι)}
    (hP : P.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) (hne : P ≠ ⊤)
    (h : ∀ (x y : MRingOver F ι) (a b : K → ℕ), x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) a →
      y ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) b → x * y ∈ P → x ∈ P ∨ y ∈ P) :
    P.IsPrime := by
  refine (isHomogeneous_lex hP).isPrime_of_homogeneous_mem_or_mem hne ?_
  intro x y hx hy hxy
  obtain ⟨l, hl⟩ := hx
  obtain ⟨l', hl'⟩ := hy
  obtain ⟨a, ha⟩ := homog_of_lex hl
  obtain ⟨b, hb⟩ := homog_of_lex hl'
  exact h x y a b ha hb hxy

theorem exists_prime_colon {I : Ideal (MRingOver F ι)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) (hIt : I ≠ ⊤) :
    ∃ (g : MRingOver F ι) (δ : K → ℕ), g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ ∧ g ∉ I ∧
      (I.colon {g}).IsPrime := by
  classical
  have hone : (1 : MRingOver F ι) ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) 0 := by
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one _ _
  have h1I : (1 : MRingOver F ι) ∉ I := (Ideal.ne_top_iff_one I).mp hIt
  let S : Set (Ideal (MRingOver F ι)) :=
    {J | ∃ (g : MRingOver F ι) (δ : K → ℕ),
      g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ ∧ g ∉ I ∧ J = I.colon {g}}
  have hS : S.Nonempty := ⟨I.colon {1}, 1, 0, hone, h1I, rfl⟩
  obtain ⟨J, ⟨g, δ, hg, hgI, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherianRing (MRingOver F ι)) S hS
  refine ⟨g, δ, hg, hgI, ?_⟩
  refine isPrime_of_forms (colon_isHomogeneous hI hg) ?_ ?_
  · intro htop
    apply hgI
    have h1 : (1 : MRingOver F ι) ∈ I.colon {g} := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_colon_singleton, smul_eq_mul, one_mul] at h1
    exact h1
  · intro x y a b hx hy hxy
    by_cases hxJ : x ∈ I.colon {g}
    · exact Or.inl hxJ
    · right
      have hxg : x * g ∉ I := by
        rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxJ
      have hle : I.colon {g} ≤ I.colon {x * g} := by
        intro z hz
        rw [Submodule.mem_colon_singleton, smul_eq_mul] at hz ⊢
        have hz' : z * (x * g) = x * (z * g) := by ring
        rw [hz']
        exact I.mul_mem_left x hz
      have hmem : x * g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (a + δ) := by
        rw [mem_weightedHomogeneousSubmodule] at hx hg ⊢
        exact hx.mul hg
      have heq : I.colon {g} = I.colon {x * g} := by
        by_contra hne
        exact hmax _ ⟨x * g, a + δ, hmem, hxg, rfl⟩ (lt_of_le_of_ne hle hne)
      rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
      have hyx : y * (x * g) = x * y * g := by ring
      rw [hyx]
      exact hxy

theorem weighted_le_of_irrel {P : Ideal (MRingOver F ι)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MRingOver F ι) ∈ P) {e : K → ℕ} (he : 1 ≤ e k) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) e ≤ P.restrictScalars F := by
  intro x hx
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [Submodule.restrictScalars_mem, x.as_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hw := hx (mem_support_iff.mp hm)
  obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : Finsupp.weight (mw (ι := ι)) m k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      rcases p with ⟨k', j⟩
      simp only [mw, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k' = k
      · subst hk
        simp [hcon j]
      · simp [Pi.single_apply, Ne.symm hk]
    rw [hw] at h0
    omega
  have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    omega
  have hmono : monomial m (coeff m x) =
      monomial (m - Finsupp.single ⟨k, i⟩ 1) (coeff m x) * X ⟨k, i⟩ := by
    rw [X, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  rw [hmono]
  exact Ideal.mul_mem_left _ _ (hk i)

end Lex

section Len

variable {R : Type*} [CommRing R]

def colonMul (I : Ideal R) (g : R) : (R ⧸ I.colon {g}) →ₗ[R] (R ⧸ I) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R g) fun x hx => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    show g * x ∈ I
    rw [mul_comm]
    exact hx





theorem locLen_quot_self (P : Ideal R) [hP : P.IsPrime] : locLen (R ⧸ P) ⟨P, hP⟩ = 1 := by
  unfold locLen
  rw [Module.length_eq_one_iff]
  change IsSimpleModule (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ P))
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  constructor
  · refine ⟨⟨LocalizedModule.mk (Submodule.Quotient.mk 1) 1, 0, ?_⟩⟩
    rw [← LocalizedModule.zero_mk 1, Ne, LocalizedModule.mk_eq]
    rintro ⟨v, hv⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one] at hv
    exact v.2 hv
  · intro x
    refine LocalizedModule.induction_on (fun m t => ?_) x
    intro hx y
    refine LocalizedModule.induction_on (fun n u => ?_) y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    have ha : a ∉ P := by
      intro haP
      apply hx
      rw [(Submodule.Quotient.mk_eq_zero P).mpr haP, LocalizedModule.zero_mk]
    have hau : a * (u : R) ∈ P.primeCompl := fun h => (hP.mem_or_mem h).elim ha u.2
    refine ⟨Localization.mk (b * t) ⟨a * u, hau⟩, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    simp only [smul_eq_mul, Submonoid.coe_mul]
    ring

end Len

end ReciprocityTheory.ChartRestriction.G.AI.I1
