import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

section
set_option autoImplicit false

noncomputable section

open NumberField TensorProduct GlobalTheory.RealMult

namespace GlobalTheory.KSSymm

theorem dual_smul_comm {S L : Type*} [CommRing S] [AddCommGroup L] [Module S L] [Module.Invertible S L]
    (ℓ : Module.Dual S L) (x y : L) : ℓ x • y = ℓ y • x := by
  have e := congrArg (fun z ↦ TensorProduct.lid S L (ℓ.rTensor L z))
    (show x ⊗ₜ[S] y = y ⊗ₜ[S] x from Module.Invertible.tmul_comm ..)
  simpa using e

theorem eq_zero_of_coprime {M : Type*} [AddCommGroup M] {x : M}
    (h : ∀ l : ℕ, l.Prime → ∃ n : ℕ, n.Coprime l ∧ n • x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨l, hl, hd⟩ := Nat.exists_prime_and_dvd (n := addOrderOf x) (by rwa [Ne, AddMonoid.addOrderOf_eq_one_iff])
  obtain ⟨n, hn, e⟩ := h l hl
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hn.symm (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero e)))

theorem symm_of_casimir {R S L W ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup L] [Module R L]
    [Module S L] [IsScalarTower R S L] [Module.Invertible S L] [AddCommGroup W] [Module R W] [Fintype ι]
    (e t : ι → S) (τ : S →ₗ[R] R) (n m : ℕ)
    (cas : ∀ (f : S →ₗ[R] R) (s : S), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i)
    (tr : ∑ i, τ (t i) • e i = n)
    (ρ : S → W → W) (β : W →ₗ[R] L →ₗ[R] R) (hβ : ∀ s f v, β (ρ s f) v = β f (s • v))
    (rad : ∀ f, β f = 0 → m • f = 0) (κ : W →ₗ[R] L) (hκ : ∀ s f, κ (ρ s f) = s • κ f) (f f' : W) :
    (m * n * n) • (β f (κ f') - β f' (κ f)) = 0 := by
  let Φ : W → Module.Dual S L := fun f ↦
    { toFun v := ∑ i, β f (e i • v) • t i
      map_add' := fun v w ↦ by simp only [smul_add, map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun s v ↦ by
        have := cas (β f ∘ₗ (LinearMap.toSpanSingleton S L v).restrictScalars R) s
        simpa [smul_smul, mul_comm] using this }
  have Φv : ∀ f v, Φ f v = ∑ i, β f (e i • v) • t i := fun _ _ ↦ rfl
  have Φρ : ∀ s f v, Φ (ρ s f) v = s * Φ f v := fun s f v ↦ by
    rw [← smul_eq_mul, ← map_smul]
    simp only [Φv, hβ, smul_comm s]
  have Φsub : ∀ f f' v, Φ (f - f') v = Φ f v - Φ f' v := fun f f' v ↦ by
    simp only [Φv, map_sub, LinearMap.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have τΦ : ∀ f v, τ (Φ f v) = n • β f v := fun f v ↦ by
    have : β f ((∑ i, τ (t i) • e i) • v) = n • β f v := by rw [tr, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [← this, Φv, Finset.sum_smul, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_assoc, τ.map_smul, (β f).map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have k : ∀ u, (m * n) • (Φ f u • κ f' - Φ f' u • κ f) = 0 := fun u ↦ by
    have z : β (n • (ρ (Φ f u) f' - ρ (Φ f' u) f)) = 0 := LinearMap.ext fun v ↦ by
      have c := congrArg (Φ f') (dual_smul_comm (Φ f) u v)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at c
      rw [map_nsmul, LinearMap.smul_apply, ← τΦ, Φsub, Φρ, Φρ, c, mul_comm, sub_self, map_zero, LinearMap.zero_apply]
    have := congrArg κ (rad _ z)
    rwa [← mul_smul, map_nsmul, map_sub, hκ, hκ, map_zero] at this
  have k' : ∀ w : Module.Dual S L ⊗[S] L,
      (m * n) • (contractLeft S L w * (Φ f (κ f') - Φ f' (κ f))) = 0 := fun w ↦ by
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, add_mul, smul_add, hx, hy, add_zero]
    | tmul ℓ u =>
      have c := congrArg ℓ (k u)
      have c₁ := congrArg (Φ f) (dual_smul_comm ℓ u (κ f'))
      have c₂ := congrArg (Φ f') (dual_smul_comm ℓ u (κ f))
      simp only [map_nsmul, map_sub, map_smul, smul_eq_mul, map_zero] at c c₁ c₂
      rw [contractLeft_apply, mul_sub, c₁, c₂, ← c, mul_comm (ℓ _), mul_comm (ℓ _)]
  obtain ⟨w, hw⟩ := (Module.Invertible.bijective (R := S) (M := L)).2 1
  have := congrArg τ (k' w)
  rwa [hw, one_mul, map_nsmul, map_sub, τΦ, τΦ, map_zero, ← smul_sub, ← mul_smul] at this

theorem exists_form (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ (n : ℕ) (τ : 𝓞 F →ₗ[ℤ] ℤ) (t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → 𝓞 F), n.Coprime l ∧
      (∀ i x, τ (t i * x) = n * (RingOfIntegers.basis F).repr x i) ∧ ∀ y, (∀ x, τ (y * x) = 0) → y = 0 := by
  classical
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  let 𝔡 : FracId F := Units.mk0 (FractionalIdeal.dual ℤ ℚ 1) (FractionalIdeal.dual_ne_zero ℤ ℚ h1)
  have mem : ∀ x : F, x ∈ 𝔡.elt ↔ ∀ a : 𝓞 F, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ F (x * a) := fun x ↦ by
    refine (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h1).trans ⟨fun h a ↦ ?_, fun h a ha ↦ ?_⟩
    · exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      exact h a
  have dual : ∀ i (x : 𝓞 F), Algebra.trace ℚ F ((integralBasis F).traceDual i * x) =
      ((RingOfIntegers.basis F).repr x i : ℚ) := fun i x ↦ by
    conv_lhs => rw [← (RingOfIntegers.basis F).sum_repr x]
    simp only [map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, ← integralBasis_apply,
      RingOfIntegers.coe_eq_algebraMap, Module.Basis.trace_traceDual_mul]
    simp
  obtain ⟨δ, hδ, hgen⟩ := GlobalTheory.FracGen.exists_gen F 𝔡 l
  obtain ⟨n, -, hn, hu⟩ := GlobalTheory.PolPrimeTo.exists_uniform 𝔡 l δ hgen
  choose τ hτ using (mem δ).1 δ.2
  choose t ht using fun i ↦ hu ⟨(integralBasis F).traceDual i, (mem _).2 fun a ↦ ⟨_, (dual i a).symm⟩⟩
  refine ⟨n, (AddMonoidHom.mk' τ fun a b ↦ Int.cast_injective (α := ℚ) ?_).toIntLinearMap, t, hn,
    fun i x ↦ Int.cast_injective (α := ℚ) ?_, fun y hy ↦ ?_⟩
  · rw [Int.cast_add, hτ, hτ, hτ, ← map_add, ← mul_add]
    simp
  · have e := congrArg Subtype.val (ht i)
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast] at e
    change ((τ _ : ℤ) : ℚ) = _
    rw [hτ, Int.cast_mul, ← dual, Int.cast_natCast, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, ← mul_assoc, e]
    simp [mul_comm, mul_left_comm]
  · have z : (δ : F) * y = 0 := by
      refine (traceForm_nondegenerate ℚ F).1 _ fun x ↦ ?_
      rw [← (integralBasis F).sum_repr x, map_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have e : ((τ (y * RingOfIntegers.basis F i) : ℤ) : ℚ) = 0 := by exact_mod_cast hy _
      rw [hτ] at e
      rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, mul_assoc]
      simpa using Or.inr e
    simpa using (mul_eq_zero.1 z).resolve_left hδ

theorem exists_casimir (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] :
    ∃ (n : ℕ) (e t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R ⊗[ℤ] 𝓞 F) (τ : R ⊗[ℤ] 𝓞 F →ₗ[R] R), n.Coprime l ∧
      (∀ (f : R ⊗[ℤ] 𝓞 F →ₗ[R] R) (s : R ⊗[ℤ] 𝓞 F), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i) ∧
      ∑ i, τ (t i) • e i = n := by
  obtain ⟨n, τ, t, hn, ht, nd⟩ := exists_form F l
  set b := RingOfIntegers.basis F
  have cas : ∀ a j, a * t j = ∑ i, b.repr (a * b i) j • t i := fun a j ↦ sub_eq_zero.1 <| nd _ fun x ↦ by
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, mul_comm a, mul_assoc, ht, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, ht, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  refine ⟨n, fun i ↦ 1 ⊗ₜ b i, fun i ↦ 1 ⊗ₜ t i, (AlgebraTensorModule.rid ℤ R R).toLinearMap ∘ₗ τ.baseChange R, hn,
    fun f s ↦ ?_, ?_⟩
  · induction s with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, hx, hy]
    | tmul r a =>
      have e₁ : ∀ i, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] b i) = r • ∑ j, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] b j := fun i ↦ by
        simp only [← tmul_smul, ← tmul_sum, b.sum_repr]
        simp [smul_tmul']
      have e₂ : ∀ j, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] t j) = r • ∑ i, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] t i := fun j ↦ by
        simp only [← tmul_smul, ← tmul_sum, ← cas]
        simp [smul_tmul']
      simp only [Finset.mul_sum, mul_smul_comm, e₁, e₂, map_smul, map_sum, map_zsmul, Finset.smul_sum,
        Finset.sum_smul, smul_assoc]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [smul_comm (f _), smul_comm (f _)]
  · have e : ∀ i, τ (t i) = n * b.repr 1 i := fun i ↦ by rw [← ht, mul_one]
    have e' : ∑ i, τ (t i) • b i = n := by
      simp only [e, mul_smul, ← Finset.smul_sum, b.sum_repr]
      simp
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
      smul_assoc, one_smul, ← tmul_smul, ← tmul_sum, e']
    exact map_natCast (Algebra.TensorProduct.includeRight (R := ℤ) (A := R)) n

end GlobalTheory.KSSymm
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSymm

theorem exists_leftInverse {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {g : ℕ}
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [hf : IsMonHom f] {m : ℕ} (hm : 0 < m)
    (hker : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) :
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m := by
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (IsogenyQuasiInverse.flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (IsogenyQuasiInverse.flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  exact (exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hker T x hx]).1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))

theorem additive [IsTotallyReal F] (c : 𝔠.elt) : IsAdditive (X.P c) ∧ IsAdditive (swap (X.P c)) := by
  obtain ⟨c₁, hc₁⟩ := fracId_exists_totPos F 𝔠
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  exact BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem cupSquare (HR : AbelianDeRham) : CupSquare (dp0 R) (𝟙 _) (X.A ⊗ X.A) :=
  cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)

variable {X}

theorem nsmul_eq_zero_of_radical [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) {c : 𝔠.elt} {m : ℕ}
    (hm0 : 0 < m) (hm : ∀ d : 𝔠.elt, ∃ t : 𝓞 F, (m : 𝓞 F) • d = t • c) {ψ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hψ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ) {y : HdR X.A} (hy : ∀ x, ψ x y = 0) : m • y = 0 := by
  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  obtain ⟨a₁, a₂⟩ := additive X c
  obtain ⟨lam, hlam, hcls⟩ := BirigidLift.exists_hom hd hd'.additive (X.isLB c) a₁ a₂
  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c T x tr (m : 𝓞 F) hm
    rwa [PolPrimeTo.act_natCast, comp_pow, Category.comp_id] at k
  obtain ⟨μ', hμ', e₁⟩ := exists_leftInverse X.ab hB X.dim hBg lam hm0 hker
  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c), BirigidLift.evc_of_cls hd.isLB (X.isLB c) hcls, Category.comp_id]
  have z : push (dp0 R) (𝟙 _) lam y = 0 := (injective_iff_map_eq_zero _).1 (hperf φ hφ).1.bijective_right.1 _ <|
    LinearMap.ext fun x ↦ by
      have k := IsCorrForm.adjoint (cupSquare X HR) hd.isLB (X.isLB c) hφ hψ (𝟙 X.A) lam e x y
      rw [push_id] at k
      exact k.trans (hy _)
  haveI := PolPrimeTo.isMonHom_id_pow X.A m
  have k := push_push (κ := dp0 R) (t := 𝟙 _) lam μ' _ e₁ y
  rw [z, map_zero, PolPrimeTo.push_id_pow] at k
  rw [← Nat.cast_smul_eq_nsmul R]
  exact k.symm

theorem form_smul (HR : AbelianDeRham) {c d : 𝔠.elt} {b : 𝓞 F} (e : d = b • c)
    {φ χ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ)
    (hχ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P d) χ) (x y : HdR X.A) :
    χ x y = φ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  subst e
  have := X.rm.hom
  obtain ⟨χ', hχ', k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique (cupSquare X HR) (X.isLB (b • c)) hχ'
  have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) x) x (push (dp0 R) (𝟙 _) (X.rm.act b) y) y (fun _ ↦ rfl) fun _ ↦ rfl
  rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e

variable (X) in

theorem exists_form_of (HR : AbelianDeRham) (c : 𝔠.elt) : ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare X HR) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem form_skew (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (x y : HdR X.A) : φ x y = -φ y x :=
  JetIsotropic.corrForm_antisymm (cupSquare X HR) (X.isLB c) (X.symm c) hφ x y

theorem form_balanced (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (s : R ⊗[ℤ] 𝓞 F) (x y : HdR X.A) :
    φ (actAlg (dp0 R) (𝟙 _) X.rm s x) y = φ x (actAlg (dp0 R) (𝟙 _) X.rm s y) := by
  induction s with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul r b =>
    obtain ⟨χ, hχ⟩ := exists_form_of X HR (b • c)
    rw [actAlg_tmul, actAlg_tmul, map_smul, map_smul, LinearMap.smul_apply, form_skew HR hφ,
      ← form_smul HR rfl hφ hχ, ← form_smul HR rfl hφ hχ, form_skew HR hχ x]

theorem form_fil (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) : ∀ a ∈ Fil X.A, ∀ b ∈ Fil X.A, φ a b = 0 := by
  intro a ha b hb
  obtain ⟨ψ, hψ, eψ⟩ := hφ.isPolForm
  have t := (HR.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim) _
    (X.isLB c) ψ hψ).1 _ (push_mem_Fil (inl X.A X.A) ha) _ (push_mem_Fil (inr X.A X.A) hb)
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one] at t
  simpa using t

theorem form_symm [IsTotallyReal F] (HR : AbelianDeRham) (HD : DualAbelianScheme) (hX : X.IsRapoport)
    (hL : LieExact X.A) {κ : Fil X.A →ₗ[R] X.Lie} (hκ : X.IsLinearKS κ) {c : 𝔠.elt}
    {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) {f f' : Fil X.A}
    {k k' : HdR X.A} (hk : hL.toLie X.rm k = κ f) (hk' : hL.toLie X.rm k' = κ f') : φ f k' = φ f' k := by
  letI := X.lieModule
  haveI : Module.Invertible (R ⊗[ℤ] 𝓞 F) X.Lie := hX
  have sm : ∀ (r : R) (b : 𝓞 F) (v : X.Lie), (r ⊗ₜ[ℤ] b : R ⊗[ℤ] 𝓞 F) • v = r • b • v := fun _ _ _ ↦ rfl
  haveI : IsScalarTower R (R ⊗[ℤ] 𝓞 F) X.Lie := ⟨fun r s v ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [smul_add, add_smul, ha, hb]
    | tmul r' b => rw [smul_tmul', sm, sm, smul_assoc]⟩
  have lie : ∀ (s : R ⊗[ℤ] 𝓞 F) x, hL.toLie X.rm (actAlg (dp0 R) (𝟙 _) X.rm s x) = s • hL.toLie X.rm x :=
    fun s x ↦ by
    induction s with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
    | tmul r b => rw [actAlg_tmul, map_smul, hL.toLie_act, sm]
  have mem : ∀ (s : R ⊗[ℤ] 𝓞 F) (x : Fil X.A), actAlg (dp0 R) (𝟙 _) X.rm s x ∈ Fil X.A := fun s x ↦ by
    have : hL.toLie X.rm x = 0 := LinearMap.mem_ker.1 ((hL.ker_toLie X.rm).ge x.2)
    refine (hL.ker_toLie X.rm).le (LinearMap.mem_ker.2 ?_)
    rw [lie, this, smul_zero]
  let ρ : R ⊗[ℤ] 𝓞 F → Fil X.A → Fil X.A := fun s x ↦ ⟨_, mem s x⟩
  have hρ : ∀ s x, κ (ρ s x) = s • κ x := fun s x ↦ by
    induction s with
    | zero => rw [zero_smul, ← map_zero κ]; exact congrArg κ (Subtype.ext (by simp [ρ]))
    | add a b ha hb =>
      rw [add_smul, ← ha, ← hb, ← map_add]
      exact congrArg κ (Subtype.ext (by simp [ρ]))
    | tmul r b =>
      rw [sm, ← hκ b x (ρ (1 ⊗ₜ b) x) ((actAlg_tmul _ _ _ _ _ _).trans (one_smul _ _)), ← map_smul]
      exact congrArg κ (Subtype.ext (by simp [ρ, actAlg_tmul]))
  refine sub_eq_zero.1 (eq_zero_of_coprime fun l hl ↦ ?_)
  haveI := Fact.mk hl
  obtain ⟨c₀, -, hgen⟩ := FracGen.exists_gen F 𝔠 l
  obtain ⟨m, hm0, hml, hm⟩ := PolPrimeTo.exists_uniform 𝔠 l c₀ hgen
  obtain ⟨n, e, t, τ, hn, cas, tr⟩ := exists_casimir F l R
  obtain ⟨φ₀, hφ₀⟩ := exists_form_of X HR c₀
  obtain ⟨b, hb⟩ := hm c
  obtain ⟨χ, hχ⟩ := exists_form_of X HR ((m : 𝓞 F) • c)
  have eφ : ∀ x y, m • φ x y = φ₀ x (actAlg (dp0 R) (𝟙 _) X.rm (1 ⊗ₜ b) y) := fun x y ↦ by
    rw [actAlg_tmul, one_smul, ← form_smul HR hb hφ₀ hχ, form_smul HR rfl hφ hχ, map_natCast, Module.End.natCast_apply,
      map_nsmul]
  have key := symm_of_casimir e t τ n m cas tr ρ (hL.filToDual X.rm φ₀ (form_fil HR hφ₀))
    (fun s x v ↦ by
      obtain ⟨y, rfl⟩ := hL.toLie_surjective X.rm v
      rw [← lie, hL.filToDual_toLie, hL.filToDual_toLie]
      exact form_balanced HR hφ₀ s x y)
    (fun x hx ↦ Subtype.ext (nsmul_eq_zero_of_radical HR HD hm0 hm hφ₀ fun y ↦ by
      rw [form_skew HR hφ₀, ← hL.filToDual_toLie X.rm φ₀ (form_fil HR hφ₀), hx, LinearMap.zero_apply, neg_zero]))
    κ hρ f (ρ (1 ⊗ₜ b) f')
  rw [hρ, ← hk, ← hk', ← lie, hL.filToDual_toLie, hL.filToDual_toLie, form_balanced HR hφ₀, ← eφ, ← eφ, ← smul_sub,
    ← mul_smul] at key
  exact ⟨_, ((hml.mul_left hn).mul_left hn).mul_left hml, key⟩

end GlobalTheory.KSSymm
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt KSSymm

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

def Comp (d : Crys (epsDP R) (DeRham.epsRed R) A) (f k : HdR A) : Prop :=
  ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (f c) + TrivSqZeroExt.inr (k c)

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

theorem Comp.unique (h : Comp d f k) (h' : Comp d f' k') : f = f' ∧ k = k' :=
  ⟨LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.fst ((h c).symm.trans (h' c)),
    LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.snd ((h c).symm.trans (h' c))⟩

theorem comp_zero : Comp (0 : Crys (epsDP R) (DeRham.epsRed R) A) 0 0 := fun _ ↦ by
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  simp

theorem Comp.add (h : Comp d f k) (h' : Comp d' f' k') : Comp (d + d') (f + f') (k + k') := fun c ↦ by
  rw [LinearMap.add_apply, h, h']
  ext <;> simp

theorem Comp.smul (h : Comp d f k) (r : DualNumber R) : Comp (r • d) (r.fst • f) (r.fst • k + r.snd • f) :=
  fun c ↦ by
  rw [LinearMap.smul_apply, h]
  ext <;> simp [mul_comm]

theorem Comp.ext (hm : (constMor A).IsBC) (h : Comp d f k) (h' : Comp d' f k) : d = d' :=
  JetIsotropic.ext_of_isBC hm fun c ↦ (h c).trans (h' c).symm

theorem Comp.corr (hm : (constMor A).IsBC) (h : Comp d f k) : (redMor A).Corr d f := fun c ↦ by
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smul, h, LinearMap.map_smulₛₗ, redMor_constMor, LinearMap.map_smul]
    simp

theorem Comp.push (h : Comp d f k) (u : A ⟶ A) [IsMonHom u] :
    Comp (push (epsDP R) (DeRham.epsRed R) u d) (push (dp0 R) (𝟙 _) u f) (push (dp0 R) (𝟙 _) u k) := fun c ↦ by
  have kk := (homMor (dp0 R) (𝟙 _) u).comp (constMor A)
  have hM := homMor (epsDP R) (DeRham.epsRed R) u
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) u) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, h]
  rfl

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

def graph (κ : Fil A →ₗ[R] Serre.Lie a) : Submodule (DualNumber R) (Crys (epsDP R) (DeRham.epsRed R) A) where
  carrier := {d | ∃ (f : Fil A) (k : HdR A), Comp d f k ∧ hL.toLie a k = κ f}
  zero_mem' := ⟨0, 0, comp_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨f, k, h, e⟩ ⟨f', k', h', e'⟩
    exact ⟨f + f', k + k', h.add h', by rw [map_add, map_add, e, e']⟩
  smul_mem' := by
    rintro r _ ⟨f, k, h, e⟩
    have z : hL.toLie a f = 0 := (hL.ker_toLie a).ge f.2
    exact ⟨r.fst • f, _, h.smul r, by rw [map_add, map_smul, map_smul, map_smul, e, z, smul_zero, add_zero]⟩

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
end
end
