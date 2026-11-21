import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {Y : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in

theorem specMap_comp_appLE {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by
  have e0 : (Spec.map χ ≫ q).appLE U ⊤ h = q.app U ≫ (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h := by
    first
    | exact Scheme.Hom.comp_appLE _ _ _ _ _
    | (simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]; rfl)
    | (simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]; rfl)
    | (unfold Scheme.Hom.appLE; simp [Category.assoc])
  rw [e0]
  have e1 : (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h =
      (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).app ⊤ := by
    rw [Scheme.Hom.naturality]
    rfl
  rw [e1]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact Scheme.ΓSpecIso_naturality χ

section Tan

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]

theorem aeval_tan (ℓ : ι) (q : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber K) else 0) q =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff q) +
        TrivSqZeroExt.inr (MvPolynomial.coeff (Finsupp.single ℓ 1) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    have hs : (0 : ι →₀ ℕ) ≠ Finsupp.single ℓ 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    ext <;> simp [MvPolynomial.coeff_C, hs, TrivSqZeroExt.algebraMap_eq_inl]
  next p q hp hq =>
    simp only [map_add, hp, hq, MvPolynomial.coeff_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  next p i hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X]
    by_cases h : i = ℓ
    · subst h
      have hc : MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X i) =
          MvPolynomial.constantCoeff p := by
        have := MvPolynomial.coeff_mul_X (0 : ι →₀ ℕ) i p
        rw [zero_add] at this
        exact this
      rw [hc]
      ext <;> simp
    · have h' : ℓ ≠ i := Ne.symm h
      have hc : MvPolynomial.coeff (Finsupp.single ℓ 1) (p * MvPolynomial.X i) = 0 := by
        rw [MvPolynomial.coeff_mul_X']
        simp [Finsupp.single_apply, h', h]
      rw [hc]
      ext <;> simp [h]

end Tan

variable {g : ℕ}

private theorem coeff_psTrunc_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) (hn : n ∈ degLE (ι := ι) m) :
    MvPolynomial.coeff n (psTrunc m f) = MvPowerSeries.coeff n f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, hn]

private theorem mem_degLE_lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (n : ι →₀ ℕ)
    (hb : ∀ i, n i ≤ m) (hs : (n.sum fun _ k => k) ≤ m) : n ∈ degLE (ι := ι) m := by
  unfold degLE
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨n i, Nat.lt_succ_of_le (hb i)⟩,
    Finset.mem_univ _, ?_⟩, hs⟩
  ext i
  simp

theorem jetTan_jetOf (ℓ : Fin 1 × Fin g) (θ : (Fin g → ℂ) → ℂ) :
    (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      TrivSqZeroExt.inl (θ 0) + TrivSqZeroExt.inr (fderiv ℂ θ 0 (Pi.single ℓ.2 1)) := by
  have h1 : (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
        (psTrunc (0 + 1) (tay θ 0)) := rfl
  have hc : ∀ n, MvPowerSeries.coeff n (tay θ 0) = mD θ 0 (dirs n + 0) / fct n := fun n => rfl
  have hb0 : ∀ i, (0 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by simp
  have hs0 : ((0 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by simp
  have h0 : MvPolynomial.constantCoeff (psTrunc (0 + 1) (tay θ 0)) = θ 0 := by
    have hd0 : dirs (0 : Fin 1 × Fin g →₀ ℕ) = 0 := by simp [dirs]
    have hf0 : fct (0 : Fin 1 × Fin g →₀ ℕ) = 1 := by simp [fct]
    have hm0 : mD θ 0 (0 : Multiset (Fin g → ℂ)) = θ 0 := by
      unfold mD
      rw [Multiset.toList_zero]
      unfold lD
      exact iteratedFDeriv_zero_apply _
    rw [MvPolynomial.constantCoeff_eq,
      coeff_psTrunc_lemma (0 + 1) (tay θ 0) 0 (mem_degLE_lemma_2 (0 + 1) 0 hb0 hs0), hc,
      hd0, add_zero, hf0, div_one, hm0]
  have hb1 : ∀ i, (Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by
    intro i
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  have hs1 : ((Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by
    simp [Finsupp.sum_single_index]
  have hd : dirs (Finsupp.single ℓ 1) = {(Pi.single ℓ.2 1 : Fin g → ℂ)} := by
    simp [dirs, Finsupp.toMultiset_single]
  have hf : fct (Finsupp.single ℓ 1) = 1 := by
    unfold fct
    refine Finset.prod_eq_one fun p _ => ?_
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  have hm : mD θ 0 {(Pi.single ℓ.2 1 : Fin g → ℂ)} = fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    unfold mD
    rw [Multiset.toList_singleton]
    unfold lD
    show iteratedFDeriv ℂ 1 θ 0 (fun i => [(Pi.single ℓ.2 1 : Fin g → ℂ)].get i) = _
    rw [iteratedFDeriv_one_apply]
    rfl
  have hl : MvPolynomial.coeff (Finsupp.single ℓ 1) (psTrunc (0 + 1) (tay θ 0)) =
      fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    rw [coeff_psTrunc_lemma (0 + 1) (tay θ 0) (Finsupp.single ℓ 1)
      (mem_degLE_lemma_2 (0 + 1) (Finsupp.single ℓ 1) hb1 hs1), hc, hd, add_zero, hf, div_one, hm]
  rw [h1, aeval_tan, h0, hl]

theorem appLE_congr_hom {A : CommRingCat.{0}} {q q' : Spec A ⟶ Y} (hq : q = q') (U : Y.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U)
    (h' : ⊤ ≤ q' ⁻¹ᵁ U) : q.appLE U ⊤ h = q'.appLE U ⊤ h' := by
  subst hq
  rfl

theorem isLocalHom_jetTan (ℓ : Fin 1 × Fin g) :
    IsLocalHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) := by
  constructor
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : IsUnit (MvPolynomial.aeval
      (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) p) := hx
  rw [aeval_tan] at hx'
  have hc : MvPolynomial.constantCoeff p ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hx'
    have := congrArg TrivSqZeroExt.fst u.mul_inv
    rw [TrivSqZeroExt.fst_mul, hu] at this
    simp [h0] at this
  have hq : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ orig ℂ (Fin 1 × Fin g) := by
    unfold orig
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl]
      exact sub_self _
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hm0 (Finsupp.ext hne)
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p))) := by
    refine ⟨0 + 1 + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (MvPolynomial.C (MvPolynomial.constantCoeff p))) :=
    ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C).map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  simpa using this

set_option backward.isDefEq.respectTransparency false in

theorem jetPt_tan (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (ℓ : Fin 1 × Fin g)
    (v : Sp (DualNumber ℂ) ⟶ Y) (hd : IsDerivAt0 e (Pi.single ℓ.2 1) v) :
    spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) ≫ jetPt e hol (0 + 1) = v := by
  haveI := isLocalHom_jetTan (g := g) ℓ
  haveI hfl : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol (0 + 1) V hV ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) =
      jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol _ U hU f ((isLocalHom_jetTan ℓ).map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hv : v (IsLocalRing.closedPoint _) = e 0 cpt := by
    rw [← hd.1, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
  refine hom_ext_of_local (hpt.trans hv.symm) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  have h0 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v) ⁻¹ᵁ U := by
    have := top_le_of_mem hU
    rwa [← hd.1] at this
  have hfst := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h₂
  rw [appLE_congr_hom hd.1 U h0 (top_le_of_mem hU)] at hfst
  have hf1 : ∀ f, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ (top_le_of_mem hU) f) =
      TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h₂ f)) := fun f => by
    have := ConcreteCategory.congr_hom hfst f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  ext f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).fst = _
    rw [jetTan_jetOf, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      valAt'_of _ _ (top_le_of_mem hU)]
    exact hf1 f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).snd = _
    rw [jetTan_jetOf, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    exact (hd.2 U h₂ f).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem one_left'' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  congr 1

def anE (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) :
    (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left) :=
  fun z => (F.ex i P z).left

theorem anHol (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : IsHolFam (anE F i P) := by
  have hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h2 := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  intro U f
  obtain ⟨ho, hd⟩ := h2 U f
  have hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  have hc := hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)
  refine ⟨?_, ?_⟩
  · convert ho.preimage hι.continuous using 1
    ext z
    simp [anE]
  · convert hc using 1
    all_goals
      ext z
      simp [anE]

variable [Algebra c.F ℂ]

def anX (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (m : ℕ) : jO y g m 1 ⟶ Xo.univ.t.G :=
  Over.homMk (jetPt (anE F i P) (anHol F i P hP) m) (by
    rw [jetPt_over (anE F i P) (anHol F i P hP) Xo.univ.t.G.hom (F.u i P) (fun z => Over.w (F.ex i P z)) m, ← hy]
    rfl)

variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)



include hP in
theorem ex_zero_eq_one : F.ex i P 0 = 1 := by
  simpa using F.ex_add i P hP 0 0


theorem basis_single (e' : Fin g ≃ Lt1 Dw) (v : Fin g → ℂ) :
    ∃! a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = v j := by
  have key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j) := by
    intro a j
    rw [Fintype.sum_eq_single (e' j)]
    · simp
    · intro ℓ hℓ
      have hne : j ≠ e'.symm ℓ := by
        intro h
        apply hℓ
        rw [h, Equiv.apply_symm_apply]
      simp [hne]
  refine ⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp
  · funext ℓ
    have h1 := ha (e'.symm ℓ)
    rw [key, Equiv.apply_symm_apply] at h1
    exact h1

def anAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Fin g → MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun k => MvPowerSeries.C (ty k (a : E)) * MvPowerSeries.X ((0 : Fin 1), k)

theorem jetSubstP_anAct (m : ℕ) (a : 𝓞 E) (b : Jet ℂ (Fin 1 × Fin g) m) :
    jetSubstP m (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) b =
      jetScaleP m (fun k => ty k (a : E)) b := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  unfold jetSubstP jetScaleP
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]
  have key : ∀ p : Fin 1 × Fin g,
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) =
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (MvPolynomial.C (ty p.2 (a : E)) * MvPolynomial.X p) := by
    rintro ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq
    have hps : psTrunc m (anAct ty a k) =
        if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then
          MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0 := by
      unfold psTrunc anAct
      by_cases hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))
      · rw [if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]
        · simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]
        · intro e _ he
          simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]
        · intro h
          exact absurd hmem h
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ Finsupp.single q 1 := fun h => hmem (h ▸ he)
        simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]
    rw [hps]
    by_cases hm0 : m = 0
    · subst hm0
      have hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        intro hmem
        rw [degLE, Finset.mem_filter] at hmem
        have := hmem.2
        rw [Finsupp.sum_single_index rfl] at this
        omega
      rw [if_neg hnot]
      simp only [map_zero, sub_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · have hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        rw [degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]
        refine ⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩
        ext j
        by_cases hj : j = q
        · subst hj
          simp
        · simp [hj, Finsupp.single_apply, Ne.symm hj]
      rw [if_pos hmem]
      simp [MvPolynomial.constantCoeff_X, hq]
  show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext p
  exact key p


theorem fst_jetTan (ℓ : Fin 1 × Fin g) (a : Jet ℂ (Fin 1 × Fin g) (0 + 1)) :
    ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) a).fst =
      (jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [jetTan, jetAug, liftJet]
  try simp only [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  induction p using MvPolynomial.induction_on with
  | C r => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = ℓ <;> simp [hj, hp]

theorem epsMul_algebraMap (cc : ℂ) (a : ℂ) : epsMul cc (algebraMap ℂ (DualNumber ℂ) a) = algebraMap ℂ _ a := by
  ext <;> simp [epsMul]

def epsHom (x : Sp ℂ ⟶ Xo.X) (cc : ℂ) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul cc)) (by
    show spMap (epsMul cc) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a => epsMul_algebraMap cc a)

theorem spMap_epsMul_zero_jetTan (ℓ : Fin 1 × Fin g) :
    spMap (epsMul (0 : ℂ)) ≫ spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
  have h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp
      ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · simp [epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem epsMul_one : epsMul (1 : ℂ) = RingHom.id (DualNumber ℂ) := by
  ext x <;> simp [epsMul]



end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
