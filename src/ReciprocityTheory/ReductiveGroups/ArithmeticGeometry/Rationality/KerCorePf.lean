import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FunKerSt

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

def KerCoreStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (Fam : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁], (V →ₗ[K] K₁) → Prop),
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁), Fam K₁ f →
      W ≤ LinearMap.ker f) →
    (∀ v : V, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁),
      Fam K₁ f → f v = 0) → v ∈ W) →
    (∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁]
      [Algebra K K₁] (e : K' →ₐ[K] K₁) (f : V →ₗ[K] K'), Fam K' f →
      ∃ f₁ : V →ₗ[K] K₁, Fam K₁ f₁ ∧ ∀ v, f₁ v = e (f v)) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (ρ : ℕ)
      (g : Fin ρ → (V →ₗ[K] K₁)) (cfL : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ i, Fam K₁ (g i)) ∧ (∀ i v, cfL i ((1 : K₁) ⊗ₜ[K] v) = g i v) ∧
      (∀ x : K₁ ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ baseSpan K₁ W) ∧
      Module.finrank K W + ρ = Module.finrank K V

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype

theorem incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem baseSpan_eq_range (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem mem_baseSpan_iff (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (x : F ⊗[K] V) : x ∈ baseSpan F U ↔ LinearMap.lTensor F U.mkQ x = 0 := by
  have hex := lTensor_exact F (LinearMap.exact_subtype_mkQ U) (Submodule.mkQ_surjective U)
  rw [hex x, baseSpan_eq_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, (incU_apply_eq_lTensor F U y).symm⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, incU_apply_eq_lTensor F U y⟩

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def fldIncl (K₁ : IntermediateField K Ω) : K₁ →ₗ[K] Ω :=
  (IsScalarTower.toAlgHom K K₁ Ω).toLinearMap

theorem fldIncl_injective (K₁ : IntermediateField K Ω) : Function.Injective (fldIncl K₁) :=
  (algebraMap K₁ Ω).injective

theorem inclT_tmul' (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) ⊗ₜ[K] v := rfl

theorem lTensor_mkQ_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V) :
    LinearMap.lTensor Ω U.mkQ (inclT K₁ V x) =
      LinearMap.rTensor (V ⧸ U) (fldIncl K₁) (LinearMap.lTensor K₁ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [inclT_tmul', fldIncl]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mem_baseSpan_of_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : inclT K₁ V x ∈ baseSpan Ω U) : x ∈ baseSpan K₁ U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT] at h
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := V ⧸ U) _ (fldIncl_injective K₁)
  rw [h, map_zero]

theorem inclT_mem_baseSpan (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : x ∈ baseSpan K₁ U) : inclT K₁ V x ∈ baseSpan Ω U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT, h, map_zero]

theorem inclT_tmul (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) • ((1 : Ω) ⊗ₜ[K] v) := by
  rw [inclT_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem definedOver_iff (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) :
    DefinedOver c K' ↔ ∀ v : V, c ((1 : Ω) ⊗ₜ[K] v) ∈ K' := by
  constructor
  · intro h v
    obtain ⟨y, hy⟩ := h ((1 : K') ⊗ₜ[K] v)
    rw [inclT_tmul] at hy
    simp only [OneMemClass.coe_one, one_smul] at hy
    rw [← hy]; exact y.2
  · intro h x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a v =>
      refine ⟨a * ⟨_, h v⟩, ?_⟩
      rw [inclT_tmul, map_smul, smul_eq_mul]
      simp
    | add y z hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩

theorem DefinedOver.mono {c : Module.Dual Ω (Ω ⊗[K] V)} {K' K₁ : IntermediateField K Ω}
    (h : DefinedOver c K') (hle : K' ≤ K₁) : DefinedOver c K₁ := by
  rw [definedOver_iff] at h ⊢
  exact fun v => hle (h v)

theorem incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h

theorem finrank_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]

theorem finiteDimensional_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : FiniteDimensional F (baseSpan F U) := by
  rw [baseSpan_eq_range]; infer_instance

theorem exists_ratFun {c : Module.Dual Ω (Ω ⊗[K] V)} {K₁ : IntermediateField K Ω}
    (h : DefinedOver c K₁) :
    ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V), ∀ x, algebraMap K₁ Ω (φ x) = c (inclT K₁ V x) := by
  let ψ : K₁ ⊗[K] V →ₗ[K₁] Ω := (c.restrictScalars K₁).comp (inclT K₁ V)
  have hr : ∀ x, ψ x ∈ LinearMap.range (Algebra.linearMap K₁ Ω) := fun x => by
    obtain ⟨y, hy⟩ := h x; exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective (Algebra.linearMap K₁ Ω) (algebraMap K₁ Ω).injective
  refine ⟨e.symm.toLinearMap ∘ₗ ψ.codRestrict _ hr, fun x => ?_⟩
  have h1 : ((e (e.symm ⟨ψ x, hr x⟩) : LinearMap.range (Algebra.linearMap K₁ Ω)) : Ω) = ψ x := by
    rw [e.apply_symm_apply]
  exact h1

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finiteDetect_holds : FiniteDetectStatement := by
  intro L E _ _ _ _ W FF hkill hdet
  classical
  let S : Set (Submodule L E) :=
    {P | ∃ s : Finset (Module.Dual L E), ↑s ⊆ FF ∧ (⨅ c ∈ s, LinearMap.ker c) = P}
  have hS : S.Nonempty := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨P, ⟨s, hsFF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  refine ⟨s, hsFF, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxW
    obtain ⟨c, hcFF, hcx⟩ := hdet x hxW
    have hmem : (⨅ d ∈ insert c s, LinearMap.ker d) ∈ S :=
      ⟨insert c s, by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hcFF
        · exact hsFF hd, rfl⟩
    apply hmin _ hmem
    refine lt_of_le_of_ne ?_ ?_
    · exact le_iInf₂ fun d hd => iInf₂_le d (Finset.mem_insert_of_mem hd)
    · intro heq
      have hx' : x ∈ ⨅ d ∈ insert c s, LinearMap.ker d := heq ▸ hx
      have : x ∈ LinearMap.ker c :=
        (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx' c) (Finset.mem_insert_self c s)
      exact hcx this
  · exact le_iInf₂ fun c hc => hkill c (hsFF hc)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem rationality_holds : RationalityStatement := by
  intro K Ω V _ _ _ _ _ U _ W FF hWle hdef hkill hdet
  classical
  have hEfd : FiniteDimensional Ω (baseSpan Ω U) := finiteDimensional_baseSpan Ω U
  set E := baseSpan Ω U with hEdef

  let FF' : Set (Module.Dual Ω E) := (fun c => c ∘ₗ E.subtype) '' FF
  obtain ⟨s', hs'FF, hs'W⟩ := finiteDetect_holds Ω E (W.comap E.subtype) FF'
    (by rintro _ ⟨c, hc, rfl⟩ x hx; exact hkill c hc hx)
    (by
      intro x hx
      obtain ⟨c, hc, hcx⟩ := hdet x x.2 hx
      exact ⟨_, ⟨c, hc, rfl⟩, hcx⟩)
  have hpre : ∀ c' ∈ s', ∃ c ∈ FF, c ∘ₗ E.subtype = c' := fun c' hc' => hs'FF hc'
  choose! pre hpreFF hpreEq using hpre
  have hR2 : ∀ y (hy : y ∈ E), y ∈ W ↔ ∀ c' ∈ s', pre c' y = 0 := by
    intro y hy
    rw [show y ∈ W ↔ (⟨y, hy⟩ : E) ∈ W.comap E.subtype from Iff.rfl, ← hs'W]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall₂_congr fun c' hc' => ?_
    conv_lhs => rw [← hpreEq c' hc']
    rfl

  have hfld : ∀ c' ∈ s', ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧
      DefinedOver (pre c') K' := fun c' hc' => hdef _ (hpreFF c' hc')
  choose! fld hfldfin hflddef using hfld
  let K₁ : IntermediateField K Ω := ⨆ c' : s', fld c'
  have : ∀ c' : s', FiniteDimensional K (fld c') := fun c' => hfldfin c' c'.2
  have hK₁fin : FiniteDimensional K K₁ := IntermediateField.finiteDimensional_iSup_of_finite
  have hdefK₁ : ∀ c' ∈ s', DefinedOver (pre c') K₁ := fun c' hc' =>
    (hflddef c' hc').mono (le_iSup (fun c'' : s' => fld c'') ⟨c', hc'⟩)
  have hrat : ∀ c' ∈ s', ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V),
      ∀ x, algebraMap K₁ Ω (φ x) = pre c' (inclT K₁ V x) := fun c' hc' =>
    exists_ratFun (hdefK₁ c' hc')
  choose! Φ hΦ using hrat

  have hDfd : FiniteDimensional K₁ (baseSpan K₁ U) := finiteDimensional_baseSpan K₁ U
  set D := baseSpan K₁ U with hDdef
  let φ : s' → Module.Dual K₁ D := fun c' => Φ c' ∘ₗ D.subtype
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent K₁ (Set.range φ)
  have htfin : t.Finite := (Set.finite_range φ).subset htsub
  have : Fintype t := htfin.fintype
  set ρ := Fintype.card t with hρ
  let eT := Fintype.equivFin t
  have hsel : ∀ i : Fin ρ, ∃ c' : s', φ c' = (eT.symm i : Module.Dual K₁ D) :=
    fun i => htsub (eT.symm i).2
  choose sel hsel using hsel
  let cc : Fin ρ → Module.Dual Ω (Ω ⊗[K] V) := fun i => pre (sel i)
  let ph : Fin ρ → Module.Dual K₁ D := fun i => (eT.symm i : Module.Dual K₁ D)
  have hph_li : LinearIndependent K₁ ph := htli.comp eT.symm eT.symm.injective
  have hph_span : Submodule.span K₁ (Set.range ph) = Submodule.span K₁ (Set.range φ) := by
    rw [← htspan]
    congr 1
    ext f
    constructor
    · rintro ⟨i, rfl⟩; exact (eT.symm i).2
    · intro hf; exact ⟨eT ⟨f, hf⟩, by simp [ph]⟩
  have hph_cc : ∀ i (x : D), algebraMap K₁ Ω (ph i x) = cc i (inclT K₁ V x) := by
    intro i x
    show algebraMap K₁ Ω ((eT.symm i : Module.Dual K₁ D) x) = _
    rw [← hsel i]
    exact hΦ _ (sel i).2 x
  have hR1 : ∀ x : D, (∀ i, ph i x = 0) → ∀ c' ∈ s', pre c' (inclT K₁ V x) = 0 := by
    intro x hx c' hc'
    have hmem : φ ⟨c', hc'⟩ ∈ Submodule.span K₁ (Set.range ph) :=
      hph_span ▸ Submodule.subset_span ⟨_, rfl⟩
    have hker : Submodule.span K₁ (Set.range ph) ≤ LinearMap.ker (Module.Dual.eval K₁ D x) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [hx i])
    have h0 : φ ⟨c', hc'⟩ x = 0 := by simpa using hker hmem
    rw [← hΦ c' hc' x]
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply] at h0
    simp [h0]

  have hdescmem : ∀ x : K₁ ⊗[K] V, x ∈ descend K₁ W ↔ ∃ hx : x ∈ D, ∀ i, ph i ⟨x, hx⟩ = 0 := by
    intro x
    rw [show x ∈ descend K₁ W ↔ inclT K₁ V x ∈ W from Iff.rfl]
    constructor
    · intro hx
      have hxE : inclT K₁ V x ∈ E := hWle hx
      refine ⟨mem_baseSpan_of_inclT K₁ U x hxE, fun i => ?_⟩
      apply (algebraMap K₁ Ω).injective
      rw [hph_cc, map_zero]
      exact ((hR2 _ hxE).mp hx) _ (sel i).2
    · rintro ⟨hxD, hi⟩
      exact (hR2 _ (inclT_mem_baseSpan K₁ U x hxD)).mpr (hR1 ⟨x, hxD⟩ hi)

  let Φ1 : D →ₗ[K₁] (Fin ρ → K₁) := LinearMap.pi ph
  have hkerΦ1 : LinearMap.ker Φ1 = (Submodule.span K₁ (Set.range ph)).dualCoannihilator := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_dualCoannihilator]
    constructor
    · intro hx f hf
      have hker : Submodule.span K₁ (Set.range ph) ≤ LinearMap.ker (Module.Dual.eval K₁ D x) :=
        Submodule.span_le.mpr (by
          rintro _ ⟨i, rfl⟩
          simpa [Φ1] using congrFun hx i)
      simpa using hker hf
    · intro h
      funext i
      simpa [Φ1] using h (ph i) (Submodule.subset_span ⟨i, rfl⟩)
  have hfinD : Module.finrank K₁ D = Module.finrank K U := finrank_baseSpan K₁ U
  have hfinE : Module.finrank Ω E = Module.finrank K U := finrank_baseSpan Ω U
  have hker_rank : Module.finrank K₁ (LinearMap.ker Φ1) + ρ = Module.finrank K U := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span K₁ (Set.range ph))
    rw [finrank_span_eq_card hph_li, Fintype.card_fin, ← hkerΦ1, hfinD] at h1
    omega
  have hΦ1surj : LinearMap.range Φ1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h2 := LinearMap.finrank_range_add_finrank_ker Φ1
    rw [Module.finrank_fin_fun, hfinD] at *
    omega
  have hd : ∀ j : Fin ρ, ∃ d : D, Φ1 d = Pi.single j 1 := fun j => by
    have : Pi.single j 1 ∈ LinearMap.range Φ1 := hΦ1surj ▸ Submodule.mem_top
    exact this
  choose d hd using hd
  have hphd : ∀ i j, ph i (d j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hd j) i
    simp only [Φ1, LinearMap.pi_apply] at this
    rw [this, Pi.single_apply]

  have hdesc_map : descend K₁ W = (LinearMap.ker Φ1).map D.subtype := by
    ext x
    rw [hdescmem, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hi⟩
      exact ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr (funext fun i => by simpa [Φ1] using hi i), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun i => ?_⟩
      have := congrFun (LinearMap.mem_ker.mp hy) i
      simpa [Φ1] using this
  have hfin_desc : Module.finrank K₁ (descend K₁ W) = Module.finrank K₁ (LinearMap.ker Φ1) := by
    rw [hdesc_map, Submodule.finrank_map_subtype_eq]
  have hdesc_inf : descend K₁ W =
      D ⊓ ⨅ i, LinearMap.ker ((cc i).restrictScalars K₁ ∘ₗ inclT K₁ V) := by
    ext x
    rw [hdescmem]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨hx, hi⟩
      refine ⟨hx, fun i => ?_⟩
      have := hph_cc i ⟨x, hx⟩
      rw [hi i, map_zero] at this
      exact this.symm
    · rintro ⟨hx, hi⟩
      refine ⟨hx, fun i => ?_⟩
      apply (algebraMap K₁ Ω).injective
      rw [hph_cc, map_zero]
      exact hi i

  set S := Submodule.span Ω (inclT K₁ V '' (descend K₁ W : Set (K₁ ⊗[K] V))) with hSdef
  have hSW : S ≤ W := Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  let dd : Fin ρ → Ω ⊗[K] V := fun j => inclT K₁ V (d j)
  let Qm : (Ω ⊗[K] V) →ₗ[Ω] (Ω ⊗[K] V) := LinearMap.id - ∑ j, (cc j).smulRight (dd j)
  have hQm_apply : ∀ y, Qm y = y - ∑ j, cc j y • dd j := by
    intro y
    simp only [Qm, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply]
  have hQm : ∀ y ∈ E, Qm y ∈ S := by
    intro y hy
    have hle : E ≤ S.comap Qm := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨u, hu, rfl⟩
      have hxD : ((1 : K₁) ⊗ₜ[K] u) ∈ D := Submodule.subset_span ⟨u, hu, rfl⟩
      set x : D := ⟨(1 : K₁) ⊗ₜ[K] u, hxD⟩ with hxdef
      have hx1 : inclT K₁ V (x : K₁ ⊗[K] V) = (1 : Ω) ⊗ₜ[K] u := by
        simp [x, inclT_tmul']
      let m : D := x - ∑ j, ph j x • d j
      have hm : ∀ i, ph i m = 0 := by
        intro i
        simp only [m, map_sub, map_sum, map_smul, smul_eq_mul, hphd, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
      have hmdesc : (m : K₁ ⊗[K] V) ∈ descend K₁ W := (hdescmem _).mpr ⟨m.2, hm⟩
      have hval : inclT K₁ V (m : K₁ ⊗[K] V) = Qm ((1 : Ω) ⊗ₜ[K] u) := by
        rw [hQm_apply]
        simp only [m, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, map_sub, map_sum,
          map_smul]
        rw [hx1]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hx1, ← hph_cc j x, algebraMap_smul]
      show Qm ((1 : Ω) ⊗ₜ[K] u) ∈ S
      rw [← hval]
      exact Submodule.subset_span ⟨_, hmdesc, rfl⟩
    exact hle hy
  have hWS : W ≤ S := by
    intro y hy
    have h := hQm y (hWle hy)
    have h0 : ∀ j, cc j y = 0 := fun j => LinearMap.mem_ker.mp (hkill _ (hpreFF _ (sel j).2) hy)
    rwa [hQm_apply, Finset.sum_eq_zero (fun j _ => by rw [h0 j, zero_smul]), sub_zero] at h
  have hSeq : S = W := le_antisymm hSW hWS

  have hdfd : FiniteDimensional K₁ (descend K₁ W) := by
    rw [hdesc_map]; infer_instance
  have hle1 : Module.finrank Ω W ≤ Module.finrank K₁ (descend K₁ W) := by
    let bd := Module.finBasis K₁ (descend K₁ W)
    let gen : Fin (Module.finrank K₁ (descend K₁ W)) → Ω ⊗[K] V :=
      fun k => inclT K₁ V (bd k : K₁ ⊗[K] V)
    have hsub : S ≤ Submodule.span Ω (Set.range gen) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      have hrep : x = ∑ k, bd.repr ⟨x, hx⟩ k • (bd k : K₁ ⊗[K] V) := by
        have := congrArg Subtype.val (bd.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hrep, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul, ← algebraMap_smul Ω]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have : FiniteDimensional Ω (Submodule.span Ω (Set.range gen)) :=
      FiniteDimensional.span_of_finite Ω (Set.finite_range _)
    calc Module.finrank Ω W = Module.finrank Ω S := by rw [hSeq]
      _ ≤ Module.finrank Ω (Submodule.span Ω (Set.range gen)) := Submodule.finrank_mono hsub
      _ ≤ Fintype.card (Fin (Module.finrank K₁ (descend K₁ W))) := finrank_range_le_card _
      _ = _ := Fintype.card_fin _
  have hle2 : Module.finrank Ω E ≤ Module.finrank Ω W + ρ := by
    have hsub : E ≤ W ⊔ Submodule.span Ω (Set.range dd) := by
      intro y hy
      have h1 : Qm y ∈ W := hSW (hQm y hy)
      have h2 : ∑ j, cc j y • dd j ∈ Submodule.span Ω (Set.range dd) :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      have hy' : y = Qm y + ∑ j, cc j y • dd j := by rw [hQm_apply]; abel
      rw [hy']
      exact Submodule.add_mem_sup h1 h2
    have : FiniteDimensional Ω (Submodule.span Ω (Set.range dd)) :=
      FiniteDimensional.span_of_finite Ω (Set.finite_range _)
    have : FiniteDimensional Ω W := Submodule.finiteDimensional_of_le hWle
    have h3 : Module.finrank Ω (Submodule.span Ω (Set.range dd)) ≤ ρ := by
      exact (finrank_range_le_card dd).trans (Fintype.card_fin ρ).le
    calc Module.finrank Ω E ≤ Module.finrank Ω ↥(W ⊔ Submodule.span Ω (Set.range dd)) :=
          Submodule.finrank_mono hsub
      _ ≤ Module.finrank Ω ↥W + Module.finrank Ω ↥(Submodule.span Ω (Set.range dd)) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ Module.finrank Ω W + ρ := by omega
  refine ⟨K₁, hK₁fin, ρ, cc, fun i => ⟨hpreFF _ (sel i).2, hdefK₁ _ (sel i).2⟩, hdesc_inf, hSeq,
    ?_, ?_⟩
  · rw [hfinE] at hle2
    omega
  · rw [hfin_desc]; exact hker_rank

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl




end SlopeTestRemainingChoices


end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

theorem exists_finset_inf_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by
  classical
  have hwf : WellFoundedLT (Submodule K V) := inferInstance
  obtain ⟨N0, ⟨t0, ht0S, rfl⟩, hmin⟩ := hwf.wf.has_min
    {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}
    ⟨⊤, ∅, by simp, by simp⟩
  refine ⟨t0, ht0S, fun N hN => ?_⟩
  have hmem : (insert N t0).inf id ∈
      {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id} :=
    ⟨insert N t0, by
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨hN, ht0S⟩, rfl⟩
  have hle : (insert N t0).inf id ≤ t0.inf id := Finset.inf_mono (Finset.subset_insert _ _)
  have heq : (insert N t0).inf id = t0.inf id := eq_of_le_of_not_lt hle (hmin _ hmem)
  rw [Finset.inf_insert] at heq
  calc t0.inf id = N ⊓ t0.inf id := heq.symm
    _ ≤ N := inf_le_left

theorem kerCore_holds : KerCoreStatement := by
  intro K _ _ V _ _ _ W Fam hkill hdet henl
  classical

  let S : Set (Submodule K V) := {N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
    (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}
  obtain ⟨t, htS, htinf⟩ := exists_finset_inf_eq S
  have hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
      (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f := fun N => htS N.2
  choose Ki fKi nfKi aKi fi hfam hNker using hmem
  have hWinf : t.inf id = W := by
    apply le_antisymm
    · intro v hv
      apply hdet v
      intro K₁ _ _ _ f hf
      have := htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv
      exact this
    · refine Finset.le_inf fun N hN => ?_
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      show W ≤ N
      rw [h1]
      exact hkill _ _ (hfam ⟨N, hN⟩)
  have hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0 := by
    intro v
    rw [← hWinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, id]
    constructor
    · intro hv N
      have h1 := hv N N.2
      rw [hNker N] at h1
      exact h1
    · intro h N hN
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      rw [h1]
      exact h ⟨N, hN⟩

  let Ω := AlgebraicClosure K
  have hfinKi : ∀ N, FiniteDimensional K (Ki N) := fun N =>
    Module.Finite.of_restrictScalars_finite ℚ K (Ki N)
  let ιi : ∀ N : t, Ki N →ₐ[K] Ω := fun N =>
    have := hfinKi N
    IsAlgClosed.lift
  let M : IntermediateField K Ω := ⨆ N : t, (ιi N).fieldRange
  have hMfin : FiniteDimensional K M := by
    have : ∀ N : t, FiniteDimensional K (ιi N).fieldRange := fun N =>
      haveI := hfinKi N
      (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional
    exact IntermediateField.finiteDimensional_iSup_of_finite
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hLfin : FiniteDimensional K L := inferInstance
  have hLgal : IsGalois K L := inferInstance
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hQL : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hnfL : NumberField L := ⟨⟩

  have hrange : ∀ N (x : Ki N), ιi N x ∈ L := fun N x =>
    hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)
  let e0 : ∀ N : t, Ki N →ₐ[K] L := fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)

  have hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v) :=
    fun N e => henl (Ki N) L e (fi N) (hfam N)
  choose g hgfam hgval using hg
  let gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V) :=
    fun p => (g p.1 p.2).liftBaseChange L
  have hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v := fun p v =>
    LinearMap.liftBaseChange_one_tmul _ _ _
  let Kc : Submodule L (L ⊗[K] V) := ⨅ p, LinearMap.ker (gh p)

  have hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V),
      gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x) := by
    intro σ N e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul,
        AlgHom.comp_apply]
      congr 1
      exact (σ.apply_symm_apply _).symm
    | add y z hy hz => simp only [map_add, hy, hz]
  have hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc := by
    intro σ x hx
    rw [Submodule.mem_iInf] at hx ⊢
    rintro ⟨N, e⟩
    rw [LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]
  have hGD := galoisDescent_holds K L V Kc hstab
  have hkP : kPoints Kc = W := by
    ext v
    rw [hWmem]
    show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h N
      have h1 := LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)
      have h2 : e0 N (fi N v) = 0 := by
        have h3 := hgval N (e0 N) v
        rw [← h3]
        simpa [hgh1] using h1
      exact (e0 N).toRingHom.injective (by simpa using h2)
    · intro h p
      rw [LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]
  have hKc : Kc = baseSpan L W := by rw [hGD, hkP]

  let G : Set (Module.Dual L (L ⊗[K] V)) := Set.range gh
  obtain ⟨t', ht'sub, ht'span, ht'li⟩ := exists_linearIndependent L G
  have ht'fin : t'.Finite := ht'li.setFinite
  have : Fintype t' := ht'fin.fintype
  set ρ := Fintype.card t' with hρ
  let eT := Fintype.equivFin t'
  have hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V)) :=
    fun i => ht'sub (eT.symm i).2
  choose pk hpk using hpick
  let cfL : Fin ρ → Module.Dual L (L ⊗[K] V) := fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))
  have hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc := by
    intro x
    constructor
    · intro h
      rw [Submodule.mem_iInf]
      intro p
      rw [LinearMap.mem_ker]
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun φ hφ => ?_
        have := h (eT ⟨φ, hφ⟩)
        simpa [cfL] using this
      have hmem : gh p ∈ Submodule.span L t' := ht'span ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa using hsp hmem
    · intro hx i
      rw [Submodule.mem_iInf] at hx
      show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0
      rw [← hpk i]
      exact LinearMap.mem_ker.mp (hx (pk i))
  have hcoan : (Submodule.span L t').dualCoannihilator = Kc := by
    ext x
    rw [Submodule.mem_dualCoannihilator, ← hcomm]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span (eT.symm i).2)
    · intro h φ hφ
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun ψ hψ => ?_
        have := h (eT ⟨ψ, hψ⟩)
        simpa [cfL] using this
      simpa using hsp hφ
  have hWfd : FiniteDimensional K W := inferInstance
  have hdim : Module.finrank K W + ρ = Module.finrank K V := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')
    rw [hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange] at h1
    have h2 : Module.finrank L (Submodule.span L t') = ρ := by
      rw [hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]
    omega
  refine ⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL,
    fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩
  · rw [show cfL i = gh (pk i) from (hpk i).symm, hgh1]
  · rw [hcomm, hKc]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
