import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination

section
open scoped TensorProduct

namespace GlobalTheory.ProjBij

theorem eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this

theorem one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y

theorem bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
      apply eq_bot_of_forall_le_smul _ Module.Finite.fg_top
      intro m hm y _
      letI := Ideal.Quotient.field m
      have hi : Function.Injective (f.baseChange (R ⧸ m)) := by
        rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨x, rfl⟩ := exists_one_tmul m z
        rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
        exact (one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := hs (1 ⊗ₜ n)
      obtain ⟨x, rfl⟩ := exists_one_tmul m z
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub,
        one_tmul_eq_zero_iff] at hz
      have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz
      rw [Submodule.map_smul''] at h2
      have h3 := Submodule.smul_mono (le_refl m) le_top h2
      have h4 : (LinearMap.range f).mkQ (f x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)
      rw [map_sub, h4, zero_sub] at h3
      exact (Submodule.neg_mem_iff _).1 h3
    intro n
    have : (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _) := by
      rw [← key]; trivial
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨?_, hsurj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ n, f (s n) = n := fun n => LinearMap.congr_fun hs n
  let p : M →ₗ[R] M := LinearMap.id - s ∘ₗ f
  have hp : Submodule.map p ⊤ = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      simp [p, hs']
    · intro x hx
      exact ⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_of_forall_le_smul
  · rw [← hp]; exact Module.Finite.fg_top.map p
  · intro m hm x hx
    have hx0 : f x = 0 := hx
    have h1 := hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)
    have h2 := Submodule.mem_map_of_mem (f := p) h1
    rw [Submodule.map_smul'', hp] at h2
    simpa [p, hx0] using h2

end GlobalTheory.ProjBij
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (x : Y.X), x ∈ U.1 → ∃ (f : Γ(Y.X, U.1)) (W : Y.X.affineOpens) (hW : W.1 ≤ U.1) (m : ℕ) (t : Fin m → Γ(Y.X, W.1)) (b : Module.Basis (Fin Dw.dim) Γ(Y.X, W.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) W)), x ∈ W.1 ∧ W.1 = Y.X.basicOpen f ∧ (∀ g ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W, g ∈ Ideal.span {∏ i, t i}) ∧ ∏ i, t i ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W ∧ ∀ (i : Fin m) (k : Fin Dw.dim), ((b k).1 : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (t i) = if (k : ℕ) = i then t i else 0 := by
  first | exact @GlobalTheory.LogBasis.exists_logDer_basis | exact GlobalTheory.LogBasis.exists_logDer_basis | (intros; apply GlobalTheory.LogBasis.exists_logDer_basis <;> assumption)
end

section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
end
end

section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end

section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LogDerProj

namespace GlobalTheory.LogDerProj

theorem isLocalizedModule_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ J : Ideal R, IsLocalizedModule (Submonoid.powers f) (res (S := S) f φ J) := by
  intro k R S _ _ _ _ f _ φ hφ J
  refine IsLocalizedModule.mk (fun x => ?_) (GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway f φ hφ J) (GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq f φ hφ J _ _)
  have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
  rw [Module.End.isUnit_iff]
  constructor
  · intro n n' h
    have h' : algebraMap R S x • n.1 = algebraMap R S x • n'.1 := by
      simpa [algebraMap_smul] using congrArg Subtype.val h
    exact Subtype.ext ((hu.smul_left_cancel).1 h')
  · intro n
    refine ⟨⟨((hu.unit⁻¹ : Sˣ) : S) • n.1, (show _ ∈ logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S)) from
      Submodule.smul_mem _ _ n.2)⟩, Subtype.ext ?_⟩
    change (x : R) • (((hu.unit⁻¹ : Sˣ) : S) • n.1) = n.1
    rw [← algebraMap_smul S (x : R), smul_smul, IsUnit.mul_val_inv, one_smul]

theorem finrank_fibre : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : R) (d : ℕ) (ϕ : M →ₗ[R] (Fin d → Localization.Away f)), IsLocalizedModule (Submonoid.powers f) ϕ → ∀ m : Ideal R, m.IsMaximal → f ∉ m → Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = d := by
  intro R M _ _ _ f d ϕ hϕ m hm hf
  letI := Ideal.Quotient.field m
  have hu : IsUnit (algebraMap R (R ⧸ m) f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  letI : Algebra (Localization.Away f) (R ⧸ m) := (IsLocalization.Away.lift f hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away f) (R ⧸ m) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hbc : IsBaseChange (Localization.Away f) ϕ := IsLocalizedModule.isBaseChange (Submonoid.powers f) _ ϕ
  let e1 := hbc.equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f) (R ⧸ m) (R ⧸ m) M
  let e3 := LinearEquiv.baseChange (Localization.Away f) (R ⧸ m) _ _ e1
  rw [← e2.finrank_eq, e3.finrank_eq, Module.finrank_eq_card_basis
    (Algebra.TensorProduct.basis (R ⧸ m) (Pi.basisFun (Localization.Away f) (Fin d))), Fintype.card_fin]

end GlobalTheory.LogDerProj

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LogDerProj.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, Module.Finite Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ Module.Projective Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U
  haveI : SmoothOfRelativeDimension Dw.dim Y.s := smooth_gen_iff.1 hsm
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  set I := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl with hI
  let φ : c.F →+* Γ(Y.X, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.s U.1
  have hφ : φ.FiniteType := by
    have h1 : (Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hM : logDer Y.s I U = GlobalTheory.LogDerProj.logSub φ (I.ideal U) := rfl
  have loc : ∀ q : PrimeSpectrum Γ(Y.X, U.1), ∃ r ∉ q.asIdeal,
      ∃ ϕ : GlobalTheory.LogDerProj.logSub φ (I.ideal U) →ₗ[Γ(Y.X, U.1)] (Fin Dw.dim → Localization.Away r),
        IsLocalizedModule (Submonoid.powers r) ϕ := by
    intro q
    have hU : IsAffineOpen U.1 := U.2
    have hxU : hU.fromSpec q ∈ U.1 := by
      change _ ∈ (U.1 : Set Y.X)
      rw [← hU.range_fromSpec]
      exact ⟨q, rfl⟩
    have key := GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc E H Dw l Xo c Y h1 hsm hsnc U (hU.fromSpec q) hxU
    obtain ⟨f, W, hW, m, t, b, hxW, hWf, -⟩ := key
    have hq : f ∉ q.asIdeal := by
      have : q ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen f := by rw [← hWf]; exact hxW
      rw [hU.fromSpec_preimage_basicOpen] at this
      exact this
    letI : Algebra Γ(Y.X, U.1) Γ(Y.X, W.1) := (Y.X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    have hloc : ∀ (V : Y.X.Opens) (hV : V ≤ U.1), V = Y.X.basicOpen f →
        letI := (Y.X.presheaf.map (homOfLE hV).op).hom.toAlgebra; IsLocalization.Away f Γ(Y.X, V) := by
      rintro V hV rfl
      exact U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away f Γ(Y.X, W.1) := hloc W.1 hW hWf
    have hc : ∀ a, algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1) (φ a) = constFn Y.s W.1 a :=
      fun a => congr(($(Scheme.Hom.appLE_map Y.s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a))
    have hid : (I.ideal U).map (algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)) = I.ideal W := I.map_ideal (U := W) (V := U) hW
    have hN : logDer Y.s I W = GlobalTheory.LogDerProj.logSub
        ((algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)).comp φ) ((I.ideal U).map (algebraMap _ _)) := by
      ext D
      rw [GlobalTheory.LogDerProj.mem_logSub, hid]
      simp only [RingHom.comp_apply, hc]
      rfl
    let b' := b.map (LinearEquiv.ofEq _ _ hN)
    let e := (b'.equivFun.restrictScalars Γ(Y.X, U.1)).trans (LinearEquiv.piCongrRight fun _ =>
      (IsLocalization.algEquiv (Submonoid.powers f) Γ(Y.X, W.1) (Localization.Away f)).toLinearEquiv)
    haveI := GlobalTheory.LogDerProj.isLocalizedModule_res (S := Γ(Y.X, W.1)) f φ hφ (I.ideal U)
    exact ⟨f, hq, e.toLinearMap ∘ₗ GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U),
      IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U)) e⟩
  rw [hM]
  obtain ⟨hfin, hproj⟩ := GlobalTheory.LocFreeProj.finite_projective_of_locally_free _ _ fun q => by
    obtain ⟨r, hr, ϕ, hϕ⟩ := loc q
    exact ⟨r, hr, Fin Dw.dim → Localization.Away r, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ϕ, hϕ⟩
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  obtain ⟨r, hr, ϕ, hϕ⟩ := loc ⟨m, hm.isPrime⟩
  exact GlobalTheory.LogDerProj.finrank_fibre r Dw.dim ϕ hϕ m hm hr
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProj.Alg

open Module

theorem trace_matrix_end {R : Type} [CommRing R] {n : ℕ}
    (f : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ f = ∑ i, ∑ j, f (Matrix.single i j 1) i j := by
  rw [LinearMap.trace_eq_matrix_trace R (Matrix.stdBasis R (Fin n) (Fin n)), Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]
  simp [Matrix.stdBasis]

def sand {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun Θ := Pᵀ * Θ * Q
  map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun r x => by simp

theorem trace_sand {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ (sand P Q) = P.trace * Q.trace := by
  rw [trace_matrix_end, Matrix.trace, Matrix.trace, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [sand, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem trace_sand_transpose {R : Type} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ (sand P Q ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) R R).toLinearMap) =
      (Q * P).trace := by
  rw [trace_matrix_end, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [sand, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_comm]

theorem finrank_retract {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (N : Submodule R M) (r : M →ₗ[R] N) (hr : r ∘ₗ N.subtype = LinearMap.id)
    (k : Type) [Field k] [Algebra R k] :
    (finrank k (k ⊗[R] N) : k) = algebraMap R k (LinearMap.trace R M (N.subtype ∘ₗ r)) := by
  have : Module.Finite R N := Module.Finite.of_surjective r
    (fun x => ⟨x, LinearMap.congr_fun hr x⟩)
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.trace_comp_comm',
    ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id, LinearMap.trace_id]

section abstract

variable {O R J : Type} [CommRing R] [Fintype J] {n : ℕ} {A : O → Matrix (Fin n) (Fin n) R} {χ : J → O → R}
  {P : J → Matrix (Fin n) (Fin n) R}

theorem eq_zero_of_unit {M : Type} [AddCommGroup M] [Module R M] {x y : R} (h : IsUnit (x - y)) {v : M}
    (hv : x • v = y • v) : v = 0 := by
  rw [← sub_eq_zero, ← sub_smul] at hv
  exact (h.smul_eq_zero).1 hv

theorem orth (hl : ∀ τ a, A a * P τ = χ τ a • P τ) (hr : ∀ τ a, P τ * A a = χ τ a • P τ)
    (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) {σ τ : J} (h : σ ≠ τ) : P σ * P τ = 0 := by
  obtain ⟨a, ha⟩ := hs σ τ h
  refine eq_zero_of_unit ha ?_
  rw [← Matrix.smul_mul, ← hr, ← Matrix.mul_smul, ← hl, Matrix.mul_assoc]

theorem eigRank_eq (h1 : ∑ τ, P τ = 1) (hl : ∀ τ a, A a * P τ = χ τ a • P τ)
    (hr : ∀ τ a, P τ * A a = χ τ a • P τ) (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
    {k : Type} [Field k] (φ : R →+* k) (σ : J) : (eigRank φ A (χ σ) : k) = φ (P σ).trace := by
  have hm : ∀ (x : R) (X : Matrix (Fin n) (Fin n) R), (x • X).map φ = φ x • X.map φ := fun x X => by
    ext i j; simp
  have hp : LinearMap.IsProj (eigSp (fun a => (A a).map φ) (fun a => φ (χ σ a)))
      (Matrix.toLin' ((P σ).map φ)ᵀ) := by
    constructor
    · intro c a
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, ← Matrix.map_mul, hr, hm,
        Matrix.vecMul_smul]
    · intro c hc
      have h0 : ∀ τ, τ ≠ σ → c ᵥ* (P τ).map φ = 0 := fun τ h => by
        obtain ⟨a, ha⟩ := hs τ σ h
        have ha' := ha.map φ
        rw [map_sub] at ha'
        refine eq_zero_of_unit ha' ?_
        rw [← Matrix.vecMul_smul, ← hm, ← hl, Matrix.map_mul, ← Matrix.vecMul_vecMul, hc a, Matrix.smul_vecMul]
      have h2 : ∑ τ, (P τ).map φ = 1 := by
        have := congrArg φ.mapMatrix h1
        rw [map_sum, map_one] at this
        exact this
      rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]
      conv_rhs => rw [← Matrix.vecMul_one c, ← h2, Matrix.vecMul_sum]
      rw [Finset.sum_eq_single σ (fun τ _ h => h0 τ h) (by simp)]
  rw [eigRank, ← hp.trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]
  simp [Matrix.trace]

theorem exists_retract (h1 : ∑ τ, P τ = 1) (hl : ∀ τ a, A a * P τ = χ τ a • P τ)
    (hr : ∀ τ a, P τ * A a = χ τ a • P τ) (hs : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
    (bar : O → O) (c : J → J) (hcc : ∀ τ, c (c τ) = τ) (hc : ∀ τ, c τ ≠ τ)
    (hb : ∀ τ a, χ τ (bar a) = χ (c τ) a) (u : R) (hu : 2 * u = 1) :
    ∃ r : Matrix (Fin n) (Fin n) R →ₗ[R] balanced bar A, r ∘ₗ (balanced bar A).subtype = LinearMap.id ∧
      2 * LinearMap.trace R _ ((balanced bar A).subtype ∘ₗ r) = ∑ τ, (P τ).trace * (P (c τ)).trace := by
  let T := (Matrix.transposeLinearEquiv (Fin n) (Fin n) R R).toLinearMap
  let S : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R := ∑ τ, sand (P τ) (P (c τ))
  have hS : ∀ Θ, S Θ = ∑ τ, (P τ)ᵀ * Θ * P (c τ) := fun Θ => by
    simp only [S, LinearMap.sum_apply]; rfl
  let q : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R := u • (S + S ∘ₗ T)
  have hq : ∀ Θ, q Θ = u • S (Θ + Θᵀ) := fun Θ => by
    rw [map_add]; rfl
  have hmem : ∀ Θ, q Θ ∈ balanced bar A := fun Θ => by
    rw [hq]
    refine Submodule.smul_mem _ _ ?_
    rw [hS]
    refine ⟨?_, fun a => ?_⟩
    · rw [Matrix.transpose_sum]
      refine Fintype.sum_bijective c (Function.Involutive.bijective hcc) _ _ fun τ => ?_
      rw [hcc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add,
        Matrix.transpose_transpose, add_comm, Matrix.mul_assoc]
    · rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hr, Matrix.mul_assoc _ (P (c τ)), hr,
        hb, hcc, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
  have hfix : ∀ Θ ∈ balanced bar A, q Θ = Θ := fun Θ hΘ => by
    have h0 : ∀ σ τ, τ ≠ c σ → (P σ)ᵀ * Θ * P τ = 0 := fun σ τ h => by
      obtain ⟨a, ha⟩ := hs σ (c τ) (fun e => h (by rw [e, hcc]))
      refine eq_zero_of_unit ha ?_
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, ← hl, Matrix.transpose_mul,
        Matrix.mul_assoc _ _ Θ, hΘ.2 a, ← hb, ← Matrix.mul_smul, ← hl]
      simp only [Matrix.mul_assoc]
    have h2 : S Θ = Θ := by
      rw [hS]
      conv_rhs => rw [← Matrix.one_mul Θ, ← Matrix.transpose_one, ← h1, Matrix.transpose_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      conv_rhs => rw [← Matrix.mul_one ((P σ)ᵀ * Θ), ← h1, Matrix.mul_sum]
      rw [Finset.sum_eq_single (c σ) (fun τ _ h => h0 σ τ h) (by simp)]
    rw [hq, hΘ.1, map_add, h2, ← two_smul R, smul_smul, mul_comm, hu, one_smul]
  refine ⟨q.codRestrict _ hmem, ?_, ?_⟩
  · ext1 x
    exact Subtype.ext (hfix x.1 x.2)
  · have hT : LinearMap.trace R _ (S ∘ₗ T) = 0 := by
      have e : S ∘ₗ T = ∑ τ, sand (P τ) (P (c τ)) ∘ₗ T := by
        ext1 x
        simp only [S, LinearMap.sum_apply, LinearMap.comp_apply]
      rw [e, map_sum]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [trace_sand_transpose, orth hl hr hs (hc τ), Matrix.trace_zero]
    rw [LinearMap.subtype_comp_codRestrict]
    simp only [q]
    rw [map_smul, map_add, hT, add_zero, smul_eq_mul, ← _root_.mul_assoc, hu, _root_.one_mul]
    simp only [S]
    rw [map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_sand _ _

end abstract

theorem exists_projectors {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type} [CommRing R] (iF : F →+* R) {n : ℕ}
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (h1 : A 1 = 1) (ha : ∀ a b, A (a + b) = A a + A b)
    (hm : ∀ a b, A (a * b) = A a * A b) :
    ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) R, ∑ τ, P τ = 1 ∧
      (∀ τ a, A a * P τ = embR F hF iF τ a • P τ) ∧ (∀ τ a, P τ * A a = embR F hF iF τ a • P τ) := by
  classical
  let b := (RingOfIntegers.basis E).reindex (equivReindex E).symm
  let M : Matrix (E →+* ℂ) (E →+* ℂ) F := Matrix.of fun i τ => ⟨τ (b i : E), hF τ _⟩
  have hM : IsUnit M.det := by
    have e : (algebraMap F ℂ).mapMatrix M = basisMatrix E := by
      ext i τ
      simp [M, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    rw [isUnit_iff_ne_zero]
    intro h
    apply det_of_basisMatrix_non_zero E
    rw [← e, ← RingHom.map_det, h, map_zero]
  let χ : (E →+* ℂ) → 𝓞 E → R := embR F hF iF
  have hχa : ∀ τ a a', χ τ (a + a') = χ τ a + χ τ a' := fun τ a a' => by
    simp only [χ, embR]; rw [← map_add]; congr 1; ext; simp
  have hχm : ∀ τ a a', χ τ (a * a') = χ τ a * χ τ a' := fun τ a a' => by
    simp only [χ, embR]; rw [← map_mul]; congr 1; ext; simp
  have hχ1 : ∀ τ, χ τ 1 = 1 := fun τ => by
    simp only [χ, embR]; rw [← map_one iF]; congr 1; ext; simp
  let M' := iF.mapMatrix M
  let N := iF.mapMatrix M⁻¹
  have hMN : M' * N = 1 := by rw [← map_mul, Matrix.mul_nonsing_inv _ hM, map_one]
  have hNM : N * M' = 1 := by rw [← map_mul, Matrix.nonsing_inv_mul _ hM, map_one]
  have hM' : ∀ i τ, M' i τ = χ τ (b i) := fun i τ => rfl
  have ind : ∀ X : (E →+* ℂ) → Matrix (Fin n) (Fin n) R, (∀ a, ∑ τ, χ τ a • X τ = 0) → ∀ σ, X σ = 0 := by
    intro X hX σ
    have : ∑ i, N σ i • ∑ τ, χ τ (b i) • X τ = X σ := by
      simp only [Finset.smul_sum, smul_smul, ← hM']
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, hNM]
      simp [Matrix.one_apply]
    rw [← this]
    simp [hX]
  let P : (E →+* ℂ) → Matrix (Fin n) (Fin n) R := fun τ => ∑ i, N τ i • A (b i)
  have hA : ∀ a, A a = ∑ τ, χ τ a • P τ := by
    let f : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A ha
    let g : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' (fun a => ∑ τ, χ τ a • P τ) fun a a' => by
      simp only [hχa, add_smul, Finset.sum_add_distrib]
    have : f.toIntLinearMap = g.toIntLinearMap := b.ext fun j => by
      show A (b j) = ∑ τ, χ τ (b j) • ∑ i, N τ i • A (b i)
      simp only [Finset.smul_sum, smul_smul, ← hM']
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, hMN]
      simp [Matrix.one_apply]
    exact fun a => LinearMap.congr_fun this a
  refine ⟨P, ?_, fun τ a => ?_, fun τ a => ?_⟩
  · rw [← h1, hA 1]
    simp [hχ1]
  · refine sub_eq_zero.1 (ind (fun τ => A a * P τ - χ τ a • P τ) (fun a' => ?_) τ)
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← hχm, ← Matrix.mul_smul, ← Matrix.mul_sum, ← hA]
    rw [mul_comm a', hm, sub_self]
  · refine sub_eq_zero.1 (ind (fun τ => P τ * A a - χ τ a • P τ) (fun a' => ?_) τ)
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← hχm, ← Matrix.smul_mul, ← Matrix.sum_mul, ← hA]
    rw [hm, sub_self]

theorem embR_sep {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type} [CommRing R] (iF : F →+* R) (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (embR F hF iF σ a - embR F hF iF τ a) := by
  have : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hh
    push Not at hh
    exact h (IsFractionRing.ringHom_ext (A := 𝓞 E) hh)
  obtain ⟨a, ha⟩ := this
  refine ⟨a, ?_⟩
  rw [embR, embR, ← map_sub]
  refine IsUnit.map iF (isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun e => ha ?_))
  exact congrArg Subtype.val e

theorem balanced_finite_projective_rank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → Module.Finite R (balanced H.bar A) ∧ Module.Projective R (balanced H.bar A) ∧ ∀ (m : Ideal R) [m.IsMaximal], 2 * Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] balanced H.bar A) = ∑ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) * GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF (NumberField.ComplexEmbedding.conjugate τ)) := by
  intro E _ _ _ H F hF R _ iF n A h1 ha hm
  obtain ⟨P, hP, hl, hr⟩ := exists_projectors F hF iF A h1 ha hm
  have hs := embR_sep F hF iF
  obtain ⟨r, hr1, hr2⟩ := exists_retract hP hl hr hs H.bar NumberField.ComplexEmbedding.conjugate
    (fun τ => star_star τ)
    (fun τ h => IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h))
    (fun τ a => by
      simp only [embR]
      congr 2
      rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj])
    (iF 2⁻¹) (by rw [← map_ofNat iF 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one])
  refine ⟨Module.Finite.of_surjective r (fun x => ⟨x, LinearMap.congr_fun hr1 x⟩),
    Module.Projective.of_split _ r hr1, fun m _ => ?_⟩
  letI := Ideal.Quotient.field m
  haveI : CharZero m.ResidueField :=
    charZero_of_injective_ringHom (f := (algebraMap R m.ResidueField).comp iF) (RingHom.injective _)
  apply Nat.cast_injective (R := m.ResidueField)
  have h2 := congrArg (algebraMap (R ⧸ m) m.ResidueField) (finrank_retract _ r hr1 (R ⧸ m))
  rw [map_natCast, ← IsScalarTower.algebraMap_apply] at h2
  push_cast
  simp only [eigRank_eq hP hl hr hs, ← map_mul, ← map_sum, ← hr2]
  rw [map_mul, map_ofNat]
  exact congrArg _ h2

end GlobalTheory.BalProj.Alg
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → Module.Finite R (balanced H.bar A) ∧ Module.Projective R (balanced H.bar A) ∧ ∀ (m : Ideal R) [m.IsMaximal], 2 * Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] balanced H.bar A) = ∑ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) * GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF (NumberField.ComplexEmbedding.conjugate τ)) := by
  atlas_forward_decl GlobalTheory.BalProj.Alg.balanced_finite_projective_rank
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add, LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by
      rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_actionMatrices_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  atlas_forward_decl GlobalTheory.BalProj.actMat_ringHom
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjOpen

open GlobalTheory.BalProj

theorem eigSp_eq_range {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (P : Matrix (Fin n) (Fin n) k) (hP : ∀ a, P * B a = χ a • P) (hfix : ∀ c ∈ eigSp B χ, c ᵥ* P = c) :
    eigSp B χ = LinearMap.range (Matrix.vecMulLinear P) := by
  ext c
  constructor
  · intro hc
    exact ⟨c, hfix c hc⟩
  · rintro ⟨d, rfl⟩ a
    show (d ᵥ* P) ᵥ* B a = χ a • (d ᵥ* P)
    rw [Matrix.vecMul_vecMul, hP a, Matrix.vecMul_smul]

theorem finrank_range_eq_trace {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hP : P * P = P) :
    (Module.finrank k (LinearMap.range (Matrix.vecMulLinear P)) : k) = P.trace := by
  have h1 : Matrix.vecMulLinear P = Matrix.toLin' Pᵀ := by
    ext c i
    simp [Matrix.mulVec_transpose]
  have hi : IsIdempotentElem (Matrix.toLin' Pᵀ) := by
    show Matrix.toLin' Pᵀ * Matrix.toLin' Pᵀ = Matrix.toLin' Pᵀ
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.transpose_mul, hP]
  rw [h1, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]

theorem eigRank_cast_eq_trace {O R k : Type} [CommRing O] [CommRing R] [Field k] (φ : R →+* k) {n : ℕ}
    (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) :
    (eigRank φ A χ : k) = φ (∑ i, f i • A (b i)).trace := by
  set P := ∑ i, f i • A (b i) with hPdef
  have hPA : ∀ a, P * A a = χ a • P := by
    intro a
    rw [← h2 a, hPdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← hmul, mul_comm]
  have hPP : P * P = P := by
    conv_lhs => arg 2; rw [hPdef]
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hPA, smul_smul, ← Finset.sum_smul, h1, one_smul]
  set Pb := P.map φ
  have hPbA : ∀ a, Pb * (A a).map φ = φ (χ a) • Pb := by
    intro a
    rw [← Matrix.map_mul, hPA a]
    ext i j
    simp [Pb]
  have hfix : ∀ c ∈ eigSp (fun a => (A a).map φ) (fun a => φ (χ a)), c ᵥ* Pb = c := by
    intro c hc
    have : Pb = ∑ i, φ (f i) • (A (b i)).map φ := by
      ext i j
      simp [Pb, hPdef, Matrix.sum_apply, map_sum]
    rw [this, Matrix.vecMul_sum]
    simp_rw [Matrix.vecMul_smul, hc _, smul_smul, ← Finset.sum_smul, ← map_mul, ← map_sum, h1, map_one, one_smul]
  have hPbPb : Pb * Pb = Pb := by rw [← Matrix.map_mul, hPP]
  unfold eigRank
  rw [eigSp_eq_range _ _ Pb hPbA hfix, finrank_range_eq_trace Pb hPbPb]
  simp [Pb, Matrix.trace, map_sum]

theorem isOpen_eigRank_eq_of_datum {O R K : Type} [CommRing O] [CommRing R] [Field K] [CharZero K] (j : K →+* R)
    {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) (N : ℕ) :
    IsOpen {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} := by
  set t := (∑ i, f i • A (b i)).trace with ht
  have key : ∀ (𝔭 : PrimeSpectrum R) (M : ℕ),
      eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = M ↔ t - M ∈ 𝔭.asIdeal := by
    intro 𝔭 M
    haveI : CharZero 𝔭.asIdeal.ResidueField :=
      (RingHom.charZero_iff ((algebraMap R 𝔭.asIdeal.ResidueField).comp j).injective).1 inferInstance
    rw [← Nat.cast_inj (R := 𝔭.asIdeal.ResidueField), eigRank_cast_eq_trace _ A hmul χ f b h1 h2,
      ← Ideal.algebraMap_residueField_eq_zero, map_sub, map_natCast, sub_eq_zero]
  have hle : ∀ 𝔭 : PrimeSpectrum R, eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ ≤ n := by
    intro 𝔭
    unfold eigRank
    exact (Submodule.finrank_le _).trans (by simp)
  have hset : {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} =
      (⋃ M ∈ (Finset.range (n + 1)).filter (· ≠ N), PrimeSpectrum.zeroLocus {t - (M : R)})ᶜ := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, exists_prop, not_exists, not_and]
    constructor
    · intro h M hM hM'
      exact hM.2 (((key 𝔭 M).2 hM').symm.trans h)
    · intro h
      by_contra hne
      exact h _ ⟨Nat.lt_succ_of_le (hle 𝔭), hne⟩ ((key 𝔭 _).1 rfl)
  rw [hset]
  exact (isClosed_biUnion_finset fun M _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

theorem exists_datum {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ)
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (hadd : ∀ a b, A (a + b) = A a + A b) (τ : E →+* ℂ) :
    ∃ (J : Type) (_ : Fintype J) (f : J → R) (b : J → 𝓞 E),
      ∑ i, f i * embR F hF iF τ (b i) = 1 ∧
      ∀ a, ∑ i, f i • A (a * b i) = embR F hF iF τ a • ∑ i, f i • A (b i) := by
  classical
  set bO := RingOfIntegers.basis E
  set bE := integralBasis E
  have hnd := _root_.traceForm_nondegenerate ℚ E
  obtain ⟨d, hd⟩ : ∃ d, d = (Algebra.traceForm ℚ E).dualBasis hnd bE := ⟨_, rfl⟩
  have hdr : ∀ i j, Algebra.trace ℚ E (bE i * d j) = if i = j then 1 else 0 := by
    intro i j
    rw [← Algebra.traceForm_apply, hd]
    exact LinearMap.BilinForm.apply_dualBasis_right hnd (Algebra.traceForm_isSymm ℚ) bE i j
  have hdrep0 : ∀ (y : E) i, d.repr y i = Algebra.trace ℚ E (y * bE i) := by
    intro y i
    rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  set g : E →+* R := iF.comp (τ.codRestrict F.toSubfield (hF τ))
  have hg : ∀ a : 𝓞 E, embR F hF iF τ a = g (a : E) := fun a => rfl
  have hbE : ∀ i, bE i = (bO i : E) := fun i => integralBasis_apply E i
  have hrep : ∀ (y : E) i, bE.repr y i = Algebra.trace ℚ E (y * d i) := by
    intro y i
    conv_rhs => rw [← bE.sum_repr y]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, hdr, smul_eq_mul, mul_ite, _root_.mul_one]
    simp
  have hdrep : ∀ y : E, y = ∑ i, Algebra.trace ℚ E (y * bE i) • d i := by
    intro y
    conv_lhs => rw [← d.sum_repr y]
    simp_rw [hdrep0]
  have hA : ∑ i, d i * bE i = 1 := by
    rw [← sub_eq_zero]
    refine hnd.1 _ fun y => ?_
    rw [Algebra.traceForm_apply, sub_mul, map_sub, _root_.one_mul, Finset.sum_mul, map_sum, sub_eq_zero,
      Algebra.trace_eq_matrix_trace bE y, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep]
    congr 1
    ring
  have hB : ∀ (a : 𝓞 E) j, ∑ i, ((bO.repr (a * bO i) j : ℤ) : E) * d i = (a : E) * d j := by
    intro a j
    conv_rhs => rw [hdrep ((a : E) * d j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Algebra.trace ℚ E ((a : E) * d j * bE i) = bE.repr ((a : E) * bE i) j := by
      rw [hrep]; congr 1; ring
    have h2 : bE.repr ((a : E) * bE i) j = ((bO.repr (a * bO i) j : ℤ) : ℚ) := by
      rw [hbE]
      exact integralBasis_repr_apply E (a * bO i) j
    rw [h1, h2, Algebra.smul_def, eq_ratCast, Rat.cast_intCast]
  have hexp : ∀ x : 𝓞 E, A x = ∑ j, bO.repr x j • A (bO j) := by
    intro x
    let Aa : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A hadd
    conv_lhs => rw [← bO.sum_repr x]
    exact (map_sum Aa _ _).trans (Finset.sum_congr rfl fun j _ => map_zsmul Aa _ _)
  refine ⟨_, inferInstance, fun i => g (d i), bO, ?_, ?_⟩
  · simp_rw [hg, ← map_mul, ← map_sum, ← hbE, hA, map_one]
  · intro a
    calc ∑ i, g (d i) • A (a * bO i)
        = ∑ i, ∑ j, (g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp (a * bO i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_smul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = ∑ j, (embR F hF iF τ a * g (d j)) • A (bO j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [hg, ← map_mul, ← hB a j, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul g, map_intCast g, _root_.mul_comm]
      _ = _ := by
          rw [Finset.smul_sum]
          simp_rw [smul_smul]

theorem isOpen_eigRank_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  intro E _ _ _ F hF R _ iF n A h1 hadd hmul τ N
  obtain ⟨J, _, f, b, hf1, hf2⟩ := exists_datum F hF R iF n A hadd τ
  exact isOpen_eigRank_eq_of_datum iF A hmul _ f b hf1 hf2 N

end GlobalTheory.BalProjOpen
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  atlas_forward_decl GlobalTheory.BalProjOpen.isOpen_eigRank_eq
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ArLieBase.exists_eig_subspace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)), GlobalTheory.LineNorm.IsTanBasis Z.t x e → ∀ (K : Type) [Field K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧ ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left), IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  intro E _ _ _ H Dw l Xo c Z R _ x τ g e he K _ ψ φ hφ
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjInt

open GlobalTheory.ShFam.Pad GlobalTheory.ArLieBase GlobalTheory.BalProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_act {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comb_act_mat {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x0 (u i)) (a : 𝓞 E)
    {B : Matrix (Fin m) (Fin m) S} (hB : ∀ i, IsCombAtG t x0 u (B i) (u i ≫ (t.act.act a).left))
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsCombAtG t x0 u cf w) :
    IsCombAtG t x0 u (cf ᵥ* B) (w ≫ (t.act.act a).left) := by
  have := t.act.hom a
  have hu' := fun i => tan_act t a (hu i)
  have h2 : IsCombAtG t x0 (fun i => u i ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left) := by
    have h1 := (isCombAtG_iff t x0 (fun j => ovT (hu j)) cf w).1 hw
    refine (isCombAtG_iff t x0 (fun j => ovT (hu' j)) cf _).2 ?_
    rw [← h1, ← Over.comp_left, combT_post]
    congr 2
  have h3 := tanLinG u hu _ Bᵀ cf _ (fun i => hB i) h2
  rwa [Matrix.mulVec_transpose] at h3

theorem affineOpenChart_comp_structure_eq_spMap {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    chart U ≫ s = spMap (fnHom s U.1) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of K))) U.2
    (le_top : U.1 ≤ s ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [chart, ← e, ← Spec.map_comp]
  rfl

theorem exists_eig_subspace_gen {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Z : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) (K : Type) [Field K]
    (ψ : R →+* K) (φ : c.F →+* K) (hφ : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β)) :
    ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧
      ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
        IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
          (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap β := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩

theorem mem_eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) (c : Fin n → k) :
    c ∈ eigSp B χ ↔ ∀ a, c ᵥ* B a = χ a • c := Iff.rfl

theorem eigRank_field {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) (K : Type) [Field K]
    (ψ : Γ(Y.X, U.1) →+* K) (τ : E →+* ℂ) :
    eigRank ψ A (embR c.F c.conj (fnHom Y.s U.1) τ) = Dw.mult τ := by
  let φ : c.F →+* K := ψ.comp (fnHom Y.s U.1)
  have he := GlobalTheory.LineNorm.isTanBasis_of_basis E H Y.X Y.t Γ(Y.X, U.1) (chart U) n v hv hb
  have hφ : spMap ψ ≫ chart U ≫ Y.s = spMap (φ.comp (RingHom.id c.F)) := by
    rw [affineOpenChart_comp_structure_eq_spMap, Guard.sp_comp]
  obtain ⟨V, hVr, hV⟩ := exists_eig_subspace_gen Y (chart U) τ v he K ψ φ hφ
  have hvK : ∀ i, IsTanAtG Y.t (spMap ψ ≫ chart U) (spMap (dualMap ψ) ≫ v i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Y.t ψ (hv i)
  have hbK := he.2 K ψ
  have hAK : ∀ a i, IsCombAtG Y.t (spMap ψ ≫ chart U) (fun j => spMap (dualMap ψ) ≫ v j) ((A a).map ψ i)
      ((spMap (dualMap ψ) ≫ v i) ≫ (Y.t.act.act a).left) := fun a i => by
    rw [Category.assoc]
    exact GlobalTheory.LatDRFree.comb_map Y.t ψ (hA a i)
  have key : eigSp (fun a => (A a).map ψ) (fun a => ψ (embR c.F c.conj (fnHom Y.s U.1) τ a)) = V := by
    ext cf
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hvK cf
    rw [← hV cf w hw]
    have hs : ∀ a : 𝓞 E, ψ (embR c.F c.conj (fnHom Y.s U.1) τ a) • cf = fun k => φ (embK c τ a) * cf k :=
      fun a => rfl
    rw [mem_eigSp]
    constructor
    · intro h
      refine ⟨Guard.comb_tan hvK hw, fun a => ?_⟩
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      rw [h a, hs a] at h1
      exact Guard.comb_unique hvK h1 (Guard.comb_smul hvK hw (φ (embK c τ a)))
    · rintro ⟨-, h⟩ a
      have h1 := comb_act_mat Y.t hvK a (hAK a) hw
      have h2 := Guard.comb_smul hvK hw (φ (embK c τ a))
      rw [← h a] at h2
      rw [hs a]
      exact (hbK _ (Guard.comb_tan hvK h1)).unique h1 h2
  unfold eigRank
  rw [key, hVr]

end GlobalTheory.BalProjInt

theorem GlobalTheory.BalProjInt.eigRank_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ U n v A hv hb hA 𝔭 _ τ
  exact GlobalTheory.BalProjInt.eigRank_field Y U n v A hv hb hA _ _ τ
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenRank_interior_eq_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  atlas_forward_decl GlobalTheory.BalProjInt.eigRank_interior
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem chart_dense_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  intro E _ _ _ H Dw l Xo c Y U
  have hi := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : IsOpenMap (chart U).base := (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isOpenMap
  exact (dense_interior Y).preimage h

end GlobalTheory.BalProj
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_affineChart_preimage_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  atlas_forward_decl GlobalTheory.BalProj.chart_dense_interior
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem signature_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
    ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) =
      2 * (Module.finrank ℚ E / 2 * p * q) := by
  intro E _ _ _ H p q
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 : H.rt0.re * H.rt0.im = 0 := by
      simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at e2
      linarith
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at e1
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0
    exact hdpos.ne' (by exact_mod_cast this)
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hnn : H.rt0 ≠ -H.rt0 := by
    intro h
    apply hne
    have : (2 : ℂ) * H.rt0 = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
    simpa using this
  have key : ∀ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = p * q := by
    intro τ
    have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      have hrtE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
        have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
        simpa using this
      rw [← map_pow, hrtE, h0]
      simp
    have hor : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rcases hor with h | h
    · rw [if_pos h, h, hconj, if_neg (Ne.symm hnn)]
    · rw [if_neg (by rw [h]; exact Ne.symm hnn), h, map_neg, hconj, neg_neg, if_pos rfl, mul_comm]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card E ℂ, smul_eq_mul, NumberField.IsTotallyComplex.finrank]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.BalProj
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_signature_sum_eq_twice_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) * (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = 2 * (Module.finrank ℚ E / 2 * p * q) := by
  atlas_forward_decl GlobalTheory.BalProj.signature_count
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      GlobalTheory.T.eigenRank_interior_eq_signature E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((GlobalTheory.T.dense_affineChart_preimage_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  atlas_forward_decl GlobalTheory.BalProj.balanced_finite_projective_rank
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSAssembly

theorem entry_mem_of_mem_smul_top {R : Type} [CommRing R] {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R))
    (m : Ideal R) (y : N) (hy : y ∈ m • (⊤ : Submodule R N)) (a b : Fin n) : (y : Matrix (Fin n) (Fin n) R) a b ∈ m := by
  refine Submodule.smul_induction_on (p := fun y : N => (y : Matrix (Fin n) (Fin n) R) a b ∈ m) hy ?_ ?_
  · intro r hr x _
    simpa using m.mul_mem_right _ hr
  · intro x y hx hy
    simpa using m.add_mem hx hy

theorem exists_equiv {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R)) [Module.Finite R N] [Module.Projective R N]
    (K : L → Matrix (Fin n) (Fin n) R → Prop) (hex : ∀ D, ∃ Θ, K D Θ) (huniq : ∀ D Θ Θ', K D Θ → K D Θ' → Θ = Θ')
    (hlin : ∀ D D' (r : R) Θ Θ', K D Θ → K D' Θ' → K (D + D') (Θ + Θ') ∧ K (r • D) (r • Θ))
    (hN : ∀ D Θ, K D Θ → Θ ∈ N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] L) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hfib : ∀ D Θ (m : Ideal R), m.IsMaximal → K D Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule R L)) :
    ∃ e : L ≃ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (e D).1 := by
  classical
  choose Θ hΘ using hex
  let f : L →ₗ[R] N :=
    { toFun := fun D => ⟨Θ D, hN D _ (hΘ D)⟩
      map_add' := fun D D' => Subtype.ext (huniq _ _ _ (hΘ (D + D')) (hlin D D' 1 _ _ (hΘ D) (hΘ D')).1)
      map_smul' := fun r D => Subtype.ext (huniq _ _ _ (hΘ (r • D)) (hlin D D r _ _ (hΘ D) (hΘ D)).2) }
  have hf : Function.Bijective f :=
    GlobalTheory.ProjBij.bijective_of_injective_mod_maximal R L N f hrk
      (fun m hm x hx => hfib x (Θ x) m hm (hΘ x) (entry_mem_of_mem_smul_top N m (f x) hx))
  refine ⟨LinearEquiv.ofBijective f hf, fun D Θ' => ⟨fun h => huniq D Θ' (Θ D) h (hΘ D), fun h => ?_⟩⟩
  rw [h]
  exact hΘ D

set_option maxHeartbeats 2000000 in

theorem hasLogKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  intro E _ _ _ H Dw l Xo c Y hr hsm hsnc hrig
  unfold HasLogKS
  intro U n v A hv hb hA
  obtain ⟨hLf, hLp, hLr⟩ := GlobalTheory.LogDerProj.main E H Dw l Xo c Y hr hsm hsnc U
  obtain ⟨hBf, hBp, hBr⟩ := GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim E H Dw l Xo c Y hr hsm hsnc U n v A hv hb hA
  exact exists_equiv (balanced H.bar A) (fun D Θ => IsKS Y.t (interior Y) U v D.1 Θ)
    (GlobalTheory.T.exists_kodairaSpencer_regular_framed_affine E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.KSUniq.isKS_unique_model E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.LogKSLin.isKS_linear E H Dw l Xo c Y U n v A hv hb hA)
    (GlobalTheory.LogKSBal.ksClass_mem_balanced E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (fun m hm => (hLr m hm).trans (hBr m hm).symm)
    (GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)

end GlobalTheory.LogKSAssembly
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  atlas_forward_decl GlobalTheory.LogKSAssembly.hasLogKS
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  intro h E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, GlobalTheory.T.logKodairaSpencer_iso_smooth_snc_toroidalModel E H Dw l Xo c Y hr a₃ a₄ a₈⟩
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalFanKodairaSpencer_of_rigidBoundaryCharts : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  atlas_forward_decl GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan
end
