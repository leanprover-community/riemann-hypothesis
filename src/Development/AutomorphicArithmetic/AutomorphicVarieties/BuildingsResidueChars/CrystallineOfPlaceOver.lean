import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

section
open Polynomial

theorem UpperTheory.exists_eigenvector_of_root :
    ∀ {L C D W : Type} [Field L] [Field C] [AddCommGroup D] [Module L D] [FiniteDimensional L D] [AddCommGroup W] [Module C W] [FiniteDimensional C W] (s : L →+* C) (j : D →+ W) (S : Module.End L D) (T : Module.End C W), (∀ (a : L) (x : D), j (a • x) = s a • j x) → Submodule.span C (Set.range j) = ⊤ → (∀ x, T (j x) = j (S x)) → ∀ (q : L[X]) (b : C), b ∈ T.charpoly.roots → q.eval₂ s b = 0 → ∃ x : D, x ≠ 0 ∧ aeval S q x = 0 := by
  intro L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq
  by_contra hcon
  have hinj : Function.Injective (aeval S q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    exact hcon ⟨x, h0, hx⟩
  have hsurj : Function.Surjective (aeval S q) := LinearMap.injective_iff_surjective.mp hinj
  have hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  have hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      intro x
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]
  have hsurj' : Function.Surjective (aeval T (q.map s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨j x, hcomm q x⟩
  have hinj' : Function.Injective (aeval T (q.map s)) :=
    LinearMap.injective_iff_surjective.mpr hsurj'
  have hroot : T.charpoly.IsRoot b := (mem_roots'.mp hb).2
  have hev : T.HasEigenvalue b := (Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv
  rw [eval_map, hq, zero_smul] at h1
  exact hv.2 (hinj' (by rw [h1, map_zero]))
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.weil_deligne_span_crystalline :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → IsCrys (P.PD K) ρ → Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} = ⊤ := by
  intro l _ P ι K LL V _ _ _ _ _ ρ hV hc
  have hk := mem_Dst_and_monV_eq_zero_iff l P K LL V ρ
  set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS
  have key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S := by
    intro x hx
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_
      (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)
    · rintro _ ⟨c, s, hs, rfl⟩
      have hsD : s ∈ Dpst P ρ := Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1
      obtain ⟨x₀, hx₀, e⟩ := hs
      refine ⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩
      have h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S := Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩
      have h2 := S.smul_mem (ι (c : Om l)) h1
      rw [← wdMk_mul] at h2
      exact h2
    · refine ⟨zero_mem _, ?_⟩
      have h1 : wdMk P ι ρ 0 ∈ S := by rw [wdMk_zero]; exact zero_mem _
      exact h1
    · rintro y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩
      refine ⟨add_mem hy hz, ?_⟩
      have h3 := S.add_mem h1 h2
      rw [← wdMk_add] at h3
      exact h3
    · rintro y _ ⟨hy, h1⟩
      refine ⟨neg_mem hy, ?_⟩
      have h2 := S.smul_mem (ι (((-1 : ↥LL.1) : ↥LL.1) : Om l)) h1
      rw [← wdMk_smul, neg_one_smul] at h2
      exact h2
  rw [eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact (key x.1 x.2).2
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.local_crystalline_of_induced :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (σ : ↥(Weil h)), deg σ = -1 → ∀ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD Bw.Kw) ρ → (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x → ((weilD Bw h P ρ σ y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) x) := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ _ σ hσ x y hx hy
  have hφ : ∀ z : V ⊗[ℚ_[l]] P.R.B, phiV P ↥LL.1 V (crisIncl P ↥LL.1 V z) =
      crisIncl P ↥LL.1 V (φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [φVB, P.PD_φ]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hpow : ∀ n : ℕ, (((phiD P ρ ^ n) y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) :
        Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih, hφ]
  have hfix : actD P ρ (weilToGK Bw h σ) y = y := by
    refine Subtype.ext ?_
    rw [coe_actD, hy, stRep_crisIncl]
    congr 1
    have h1 := (Submodule.mem_iInf _).mp hx (weilToGK Bw h σ)
    simpa [sub_eq_zero] using h1
  have ha : -alpha l σ = ((resDeg l w : ℕ) : ℤ) := by simp [alpha, hσ]
  rw [weilD_apply, (commute_actD_phiU P ρ _ _).eq, End.mul_apply, hfix, ha, zpow_natCast,
    Units.val_pow_eq_pow_val, coe_phiU, hpow]
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem map_pow_of_commuting {R S M N : Type} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] (f : M → N) (a : Module.End R M) (b : Module.End S N)
    (hf : ∀ x, f (a x) = b (f x)) (n : ℕ) (x : M) : f ((a ^ n) x) = (b ^ n) (f x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hf]

private theorem aeval_restriction_commute {F L M : Type} [Field F] [Field L] [Algebra F L] [AddCommGroup M] [Module L M]
    [Module F M] [IsScalarTower F L M] (D : Submodule L M) (S : Module.End L D) (T : Module.End F M)
    (hf : ∀ x : D, ((S x : D) : M) = T x) (q : F[X]) (x : D) :
    ((aeval S (q.map (algebraMap F L)) x : D) : M) = aeval T q (x : M) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      algebraMap_smul, map_pow_of_commuting (fun x : D => (x : M)) S T hf]

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

private theorem mem_aux {x : V ⊗[ℚ_[l]] P.R.B} : x ∈ Dcris (P.PD K) ρ ↔ ∀ g, actVB (P.PD K) ρ g x = x := by
  simp [Dcris, sub_eq_zero]

private theorem pullback_fin_relation [FiniteDimensional ↥LL.1 V] (hC : IsCrys (P.PD K) ρ) :
    FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  rcases subsingleton_or_nontrivial V with hs | hn
  · haveI : Subsingleton (V ⊗[ℚ_[l]] P.R.B) := inferInstance
    infer_instance
  · haveI := (P.PD K).finK₀
    apply Module.finite_of_finrank_pos
    rw [hC]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

private theorem frobenius_preserves_crystalline : ∀ x ∈ Dcris (P.PD K) ρ,
    φVB (P.PD K) (LL := ↥LL.1) (V := V) x ∈ Dcris (P.PD K) ρ := by
  intro x hx
  rw [mem_aux] at hx ⊢
  intro g
  have : ∀ y, actVB (P.PD K) ρ g (φVB (P.PD K) (LL := ↥LL.1) (V := V) y) =
      φVB (P.PD K) (LL := ↥LL.1) (V := V) (actVB (P.PD K) ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [actVB, φVB, (P.PD K).φ_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this, hx]

private theorem crystalline_mem_potentially_semistable : ∀ x ∈ Dcris (P.PD K) ρ, crisIncl P ↥LL.1 V x ∈ Dpst P ρ := by
  intro x hx
  exact (mem_Dpst P ρ).mpr ⟨K, fun g _ => by rw [stRep_crisIncl, (mem_aux P ρ).mp hx g]⟩

private noncomputable def crystallineInclusion : ↥(Dcris (P.PD K) ρ) →ₗ[↥LL.1] ↥(Dpst P ρ) :=
  (crisIncl P ↥LL.1 V).restrict (crystalline_mem_potentially_semistable P ρ)

private theorem coe_crystalline_inclusion (x : ↥(Dcris (P.PD K) ρ)) :
    ((crystallineInclusion P ρ x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x := rfl

private noncomputable def frobeniusRestriction : Module.End ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  (φVB (P.PD K) (LL := ↥LL.1) (V := V)).restrict (frobenius_preserves_crystalline P ρ)

private theorem coe_frobenius_restriction_pow (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private theorem coe_frobenius_restriction_pow_base (n : ℕ) (x : ↥(Dcris (P.PD K) ρ)) :
    (((frobeniusRestriction P ρ ^ n) x : ↥(Dcris (P.PD K) ρ)) : V ⊗[ℚ_[l]] P.R.B) =
      ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) x :=
  map_pow_of_commuting (fun x : ↥(Dcris (P.PD K) ρ) => x.1) (frobeniusRestriction P ρ)
    (φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) (fun _ => rfl) n x

private noncomputable def crystallineToWeilDeligne (ι : Om l ≃+* ℂ) : ↥(Dcris (P.PD K) ρ) →+ WDSpace P ι ρ :=
  AddMonoidHom.mk' (fun x => wdMk P ι ρ (crystallineInclusion P ρ x)) fun x y => by rw [map_add, wdMk_add]


private theorem span_crystalline_weil_deligne_top [FiniteDimensional ↥LL.1 V] (ι : Om l ≃+* ℂ) (hV : IsPst P ρ) (hC : IsCrys (P.PD K) ρ) :
    Submodule.span ℂ (Set.range (crystallineToWeilDeligne P ρ ι)) = ⊤ := by
  rw [eq_top_iff, ← UpperTheory.weil_deligne_span_crystalline P ι ρ hV hC]
  refine Submodule.span_mono ?_
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact ⟨⟨x, hx⟩, congrArg (wdMk P ι ρ) (Subtype.ext hy.symm)⟩

private theorem eval_root_transport (ι : Om l ≃+* ℂ) (b : ℂ) (q : ℚ_[l][X]) (hq : aeval (ι.symm b) q = 0) :
    (q.map (algebraMap ℚ_[l] ↥LL.1)).eval₂ (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) b = 0 := by
  rw [eval₂_map]
  have h1 := congrArg ι.toRingHom hq
  rw [map_zero, aeval_def, hom_eval₂] at h1
  have e1 : (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))).comp (algebraMap ℚ_[l] ↥LL.1) =
      ι.toRingHom.comp (algebraMap ℚ_[l] (Om l)) := by
    rw [IsScalarTower.algebraMap_eq ℚ_[l] ↥LL.1 (Om l)]; rfl
  rw [e1]
  simpa using h1

private theorem crystalline_to_weil_deligne_smul (ι : Om l ≃+* ℂ) (a : ↥LL.1) (x : ↥(Dcris (P.PD K) ρ)) :
    crystallineToWeilDeligne P ρ ι (a • x) = (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) a • crystallineToWeilDeligne P ρ ι x :=
  (congrArg (wdMk P ι ρ) ((crystallineInclusion P ρ).map_smul a x)).trans (wdMk_smul P ι ρ a _)

private theorem fin_step (n : ℕ) (q : ℚ_[l][X])
    (H : ∃ x : ↥(Dcris (P.PD K) ρ), x ≠ 0 ∧ aeval (frobeniusRestriction P ρ ^ n) (q.map (algebraMap ℚ_[l] ↥LL.1)) x = 0) :
    ∃ x ∈ Dcris (P.PD K) ρ, x ≠ 0 ∧
      aeval ((φVB (P.PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ n) q x = 0 := by
  obtain ⟨x, hx0, hx⟩ := H
  refine ⟨x.1, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  exact (aeval_restriction_commute (Dcris (P.PD K) ρ) (frobeniusRestriction P ρ ^ n) _ (coe_frobenius_restriction_pow_base P ρ n) q x).symm.trans
    (congrArg Subtype.val hx)

end SlopeTestRemainingChoices

theorem UpperTheory.crystalline_of_place_over :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), IsPst P ρ → IsCrys (P.PD Bw.Kw) ρ → ∀ σ : ↥(Weil h), deg σ = -1 → ∀ b ∈ (wdPst P ι Bw h hj ρ).eig σ, ∀ q : ℚ_[l][X], aeval (ι.symm b) q = 0 → ∃ x ∈ Dcris (P.PD Bw.Kw) ρ, x ≠ 0 ∧ aeval ((φVB (P.PD Bw.Kw) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) q x = 0 := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ hV hC σ hσ b hb q hq
  haveI := hV.finite
  haveI := pullback_fin_relation P ρ hC
  have hb' : b ∈ (wdRho P ι Bw h hj ρ σ).charpoly.roots := by
    rw [← GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ]
    exact hb
  have hT : ∀ x, wdRho P ι Bw h hj ρ σ (crystallineToWeilDeligne P ρ ι x) = crystallineToWeilDeligne P ρ ι ((frobeniusRestriction P ρ ^ resDeg l w) x) := fun x =>
    (wdRho_mk P ι Bw h hj ρ σ (crystallineInclusion P ρ x)).trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((UpperTheory.local_crystalline_of_induced P Bw h hj ρ σ hσ x.1 (crystallineInclusion P ρ x) x.2 (coe_crystalline_inclusion P ρ x)).trans
        ((coe_crystalline_inclusion P ρ _).trans (congrArg (crisIncl P ↥LL.1 V) (coe_frobenius_restriction_pow P ρ _ x))).symm)))
  exact fin_step P ρ _ q (UpperTheory.exists_eigenvector_of_root (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (crystallineToWeilDeligne P ρ ι)
    (frobeniusRestriction P ρ ^ resDeg l w) (wdRho P ι Bw h hj ρ σ) (crystalline_to_weil_deligne_smul P ρ ι)
    (span_crystalline_weil_deligne_top P ρ ι hV hC) hT (q.map (algebraMap ℚ_[l] ↥LL.1)) b hb' (eval_root_transport ι b q hq))
end
