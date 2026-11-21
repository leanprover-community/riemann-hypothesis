import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

namespace UpperTheory.V.Kum

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]

variable [IsAlgClosure F Ω] {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

end

end UpperTheory.V.Kum

private theorem cycZ_eq_of_intertwined {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (σ : Ω ≃+* Ω) (u v : G F Ω) (h : ∀ x, v (σ x) = σ (u x)) : cycZ F Ω l v = cycZ F Ω l u := by
  have key : MulSemiringAction.toRingAut (G F Ω) Ω v * σ = σ * MulSemiringAction.toRingAut (G F Ω) Ω u := by
    ext x
    exact h x
  have e := congrArg (cyclotomicCharacter Ω l) key
  rw [map_mul, map_mul, mul_comm (cyclotomicCharacter Ω l σ)] at e
  exact mul_right_cancel e

private theorem mem_levU_of_intertwined {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (U : Subgroup (G F Ω)) (n : ℕ) (σ : Ω ≃+* Ω) (u v : G F Ω) (hu : u ∈ levU l U n) (hv : v ∈ U)
    (h : ∀ x, v (σ x) = σ (u x)) : v ∈ levU l U n := by
  refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
  have hu2 := (Subgroup.mem_inf.mp hu).2
  rw [Subgroup.mem_comap] at hu2 ⊢
  rw [cycZ_eq_of_intertwined l σ u v h]
  exact hu2

private theorem mem_cycU_of_intertwined {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (U : Subgroup (G F Ω)) (σ : Ω ≃+* Ω) (u v : G F Ω) (hu : u ∈ cycU l U) (hv : v ∈ U)
    (h : ∀ x, v (σ x) = σ (u x)) : v ∈ cycU l U := by
  refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
  have hu2 := (Subgroup.mem_inf.mp hu).2
  rw [MonoidHom.mem_ker] at hu2 ⊢
  rw [cycZ_eq_of_intertwined l σ u v h]
  exact hu2

private theorem levU_antitone {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (U : Subgroup (G F Ω)) {n m : ℕ} (h : n ≤ m) : levU l U m ≤ levU l U n :=
  inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti h))

private theorem fix_lemma_5 (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (hU : IsClosed (U : Set (G F Ω))) (n : ℕ)
    (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [AddCommGroup M]
    (ψ₀ : levU l U n → M) (hψ₀ : IsLocallyConstant ψ₀) (c : T → G F Ω → G F Ω)
    (hc : Continuous fun p : T × G F Ω => c p.1 p.2)
    (hcU : ∀ t u, u ∈ levU l U n → c t u ∈ levU l U n) (A : T → M → M)
    (hA : ∀ x, IsLocallyConstant fun t => A t x)
    (h0 : ∀ t (u : levU l U n), (u : G F Ω) ∈ cycU l U → ψ₀ ⟨c t u, hcU t u u.2⟩ = A t (ψ₀ u)) :
    ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), (u : G F Ω) ∈ levU l U m →
      ψ₀ ⟨c t u, hcU t u u.2⟩ = A t (ψ₀ u) := by
  have h1 : IsLocallyConstant fun p : T × levU l U n => ψ₀ ⟨c p.1 p.2, hcU p.1 p.2 p.2.2⟩ :=
    hψ₀.comp_continuous (Continuous.subtype_mk
      (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _)
  have h2 : IsLocallyConstant fun p : T × levU l U n => ψ₀ p.2 := hψ₀.comp_continuous continuous_snd
  have hloc : IsLocallyConstant fun p : T × levU l U n =>
      ψ₀ ⟨c p.1 p.2, hcU p.1 p.2 p.2.2⟩ - A p.1 (ψ₀ p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t₀, u₀⟩
    have h3 : IsLocallyConstant fun p : T × levU l U n => A p.1 (ψ₀ u₀) :=
      (hA (ψ₀ u₀)).comp_continuous continuous_fst
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp h1 (t₀, u₀),
      (IsLocallyConstant.iff_eventually_eq _).mp h2 (t₀, u₀),
      (IsLocallyConstant.iff_eventually_eq _).mp h3 (t₀, u₀)] with p e1 e2 e3
    rw [e1, e2, e3]
  obtain ⟨m, hnm, hm⟩ := levCompact F Ω l U n T M _ hU hloc
    (fun t u hu => sub_eq_zero.mpr (h0 t u hu))
  exact ⟨m, hnm, fun t u hu => sub_eq_zero.mp (hm t u hu)⟩

private theorem restr_restr {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] {A B C : Subgroup (G F Ω)} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (ψ : C → M) : restr R M h1 (restr R M h2 ψ) = restr R M h3 ψ := by
  funext x
  rfl

private theorem eqHom_cycU_exists_lift_levU (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [hUn : U.Normal]
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M)
    (hN : N ≠ 0) (hU : IsClosed (U : Set (G F Ω))) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) :
    ∀ φ ∈ EqHom N (cycU l U) ρ, ∃ n, ∃ ψ ∈ EqHom N (levU l U n) ρ,
      restr R M (cycU_le_levU l U n) ψ = φ := by
  intro φ hφ
  obtain ⟨hφX, hφC⟩ := Submodule.mem_inf.mp hφ
  obtain ⟨n, ψ₀, hψ₀X, hres⟩ := xdualExt F Ω l N U R M hN hU φ hφX
  have hloc : IsLocallyConstant ψ₀ := hψ₀X.1
  have hcU : ∀ g u, u ∈ levU l U n → g * u * g⁻¹ ∈ levU l U n := fun g u hu =>
    mem_levU_of_intertwined l U n g.toRingEquiv u _ hu (hUn.conj_mem u (levU_le l U n hu) g)
      (fun x => by simp [AlgEquiv.mul_apply])
  have h0 : ∀ g (u : levU l U n), (u : G F Ω) ∈ cycU l U →
      ψ₀ ⟨g * u * g⁻¹, hcU g u u.2⟩ = ρ g (ψ₀ u) := by
    intro g u hu
    have hw' : g * (u : G F Ω) * g⁻¹ ∈ cycU l U :=
      mem_cycU_of_intertwined l U g.toRingEquiv u _ hu (hUn.conj_mem u (levU_le l U n u.2) g)
        (fun x => by simp [AlgEquiv.mul_apply])
    have e1 : ψ₀ ⟨g * u * g⁻¹, hcU g u u.2⟩ = φ ⟨g * u * g⁻¹, hw'⟩ := by
      rw [← hres]
      rfl
    have e2 : ψ₀ u = φ ⟨u, hu⟩ := by
      rw [← hres]
      rfl
    rw [e1, e2]
    exact (Submodule.mem_iInf _).mp hφC g ⟨u, hu⟩ ⟨g * u * g⁻¹, hw'⟩
      (fun x => by simp [AlgEquiv.mul_apply])
  obtain ⟨m, hnm, hm⟩ := fix_lemma_5 F Ω l U hU n (G F Ω) M ψ₀ hloc (fun g u => g * u * g⁻¹)
    ((continuous_fst.mul continuous_snd).mul continuous_fst.inv) hcU (fun g x => ρ g x) hρ h0
  refine ⟨m, restr R M (levU_antitone l U hnm) ψ₀, Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (restrMem F Ω N _ _ (levU_antitone l U hnm) R M ρ).1 (Submodule.mem_map_of_mem hψ₀X)
  · refine (Submodule.mem_iInf _).mpr fun g => ?_
    intro u u' hrel
    have hu' : (u' : G F Ω) = g * u * g⁻¹ := by
      ext x
      have e := hrel (g⁻¹ x)
      simp only [AlgEquiv.coe_ringEquiv] at e
      simp only [AlgEquiv.mul_apply, ← e]
      simp
    have e := hm g (Subgroup.inclusion (levU_antitone l U hnm) u) u.2
    show ψ₀ (Subgroup.inclusion _ u') = ρ g (ψ₀ (Subgroup.inclusion _ u))
    rw [← e]
    congr 1
    exact Subtype.ext hu'
  · exact (restr_restr R M _ _ (cycU_le_levU l U n) ψ₀).trans hres

theorem UpperTheory.V.Kum.eqExt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), N ≠ 0 → IsClosed (U : Set (G F Ω)) → (∀ m, IsLocallyConstant fun g => ρ g m) →
    (∀ φ ∈ EqHom N (cycU l U) ρ, ∃ n, ∃ ψ ∈ EqHom N (levU l U n) ρ, restr R M (cycU_le_levU l U n) ψ = φ) ∧
    ∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω) (h : IsLift τ σ) (s : R), (∀ u ∈ U, conjGal h.symm u ∈ U) → ∀ φ ∈ EqEig N (cycU l U) ρ σ s, ∃ n, ∃ ψ ∈ EqEig N (levU l U n) ρ σ s, restr R M (cycU_le_levU l U n) ψ = φ := by
  intro F Ω _ _ _ _ _ l _ N U hUn R M _ _ _ ρ hN hU hρ
  refine ⟨eqHom_cycU_exists_lift_levU F Ω l N U R M ρ hN hU hρ, ?_⟩
  intro τ σ h s hUσ φ hφ
  obtain ⟨hφH, hφS⟩ := Submodule.mem_inf.mp hφ
  obtain ⟨n, ψ, hψ, hres⟩ := eqHom_cycU_exists_lift_levU F Ω l N U R M ρ hN hU hρ φ hφH
  have hloc : IsLocallyConstant ψ := (Submodule.mem_inf.mp hψ).1.1
  have hrelc : ∀ (u : G F Ω) x, conjGal h.symm u (σ x) = σ (u x) := by
    intro u x
    simp [conjGal_apply]
  have hcU : ∀ (t : Unit) u, u ∈ levU l U n → conjGal h.symm u ∈ levU l U n := fun _ u hu =>
    mem_levU_of_intertwined l U n σ u _ hu (hUσ u (levU_le l U n hu)) (hrelc u)
  have h0 : ∀ (t : Unit) (u : levU l U n), (u : G F Ω) ∈ cycU l U →
      ψ ⟨conjGal h.symm u, hcU t u u.2⟩ = s • ψ u := by
    intro t u hu
    have hw' : conjGal h.symm (u : G F Ω) ∈ cycU l U :=
      mem_cycU_of_intertwined l U σ u _ hu (hUσ u (levU_le l U n u.2)) (hrelc u)
    have e1 : ψ ⟨conjGal h.symm u, hcU t u u.2⟩ = φ ⟨conjGal h.symm u, hw'⟩ := by
      rw [← hres]
      rfl
    have e2 : ψ u = φ ⟨u, hu⟩ := by
      rw [← hres]
      rfl
    rw [e1, e2]
    exact hφS ⟨u, hu⟩ ⟨conjGal h.symm u, hw'⟩ (hrelc u)
  obtain ⟨m, hnm, hm⟩ := fix_lemma_5 F Ω l U hU n Unit M ψ hloc (fun _ u => conjGal h.symm u)
    ((continuous_conjGal h.symm).comp continuous_snd) hcU (fun _ x => s • x)
    (fun _ => IsLocallyConstant.const _) h0
  refine ⟨m, restr R M (levU_antitone l U hnm) ψ, Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (restrMem F Ω N _ _ (levU_antitone l U hnm) R M ρ).2.1 (Submodule.mem_map_of_mem hψ)
  · intro u u' hrel
    have hu' : (u' : G F Ω) = conjGal h.symm u := by
      ext x
      have e := hrel (σ.symm x)
      simp only [RingEquiv.apply_symm_apply] at e
      rw [e]
      simp [conjGal_apply]
    have e := hm () (Subgroup.inclusion (levU_antitone l U hnm) u) u.2
    show ψ (Subgroup.inclusion _ u') = s • ψ (Subgroup.inclusion _ u)
    rw [← e]
    congr 1
    exact Subtype.ext hu'
  · exact (restr_restr R M _ _ (cycU_le_levU l U n) ψ).trans hres
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum



section Index

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M)
  (H : Subgroup Γ) (hH : ∀ g g', g ∉ H → g' ∉ H → g * g' ∈ H)
include hH




end Index
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

section Lim

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m := by
  intro g hg
  simp only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢
  exact ⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩

omit [IsAlgClosure F Ω] in

theorem len_le_of_layers (U : Subgroup (G F Ω)) (W : Submodule R (cycU l U → M)) (P : ∀ n, Submodule R (levU l U n → M))
    (hP : ∀ m n (h : m ≤ n), (P m).map (restr R M (levU_anti U h)) ≤ P n)
    (hW : ∀ φ ∈ W, ∃ n, ∃ ψ ∈ P n, restr R M (cycU_le_levU l U n) ψ = φ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) : Module.length R W ≤ Bd := by
  refine lenDirected R _ W (fun n => (P n).map (restr R M (cycU_le_levU l U n))) Bd ?_ ?_ ?_
  · rintro m n h _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, hP m n h ⟨ψ, hψ, rfl⟩, rfl⟩
  · intro φ hφ
    obtain ⟨n, ψ, hψ, rfl⟩ := hW φ hφ
    exact Submodule.mem_iSup_of_mem n ⟨ψ, hψ, rfl⟩
  · intro n₀
    obtain ⟨n, h, hn⟩ := hB n₀
    exact ⟨n, h, (Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)).trans hn⟩

theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  have := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]

omit [NumberField F] in
theorem length_map_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y)
    (N : Submodule R X) : Module.length R (N.map f) ≤ Module.length R N :=
  Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective f N)




private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0) {w : ℤ_[l]ˣ}
    (hw : w ∈ KStar.TotallyRealRoots.princ l k) : (w : ℤ_[l]) • x = x := by
  rw [KStar.TotallyRealRoots.mem_princ] at hw
  obtain ⟨c, hc⟩ := hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (KStar.TotallyRealRoots.isOpen_princ k).mem_nhds
    simp only [mul_inv_cancel]
    exact (KStar.TotallyRealRoots.princ l k).one_mem
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) =
      (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]




variable [IsCMField F]





end Lim

end UpperTheory.V.Kum

end
end
