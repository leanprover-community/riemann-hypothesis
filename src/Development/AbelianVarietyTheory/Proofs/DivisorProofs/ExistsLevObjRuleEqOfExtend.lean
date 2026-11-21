import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEvalOneTmulMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreeOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOfCoefficientSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorModuleCompat

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_affine_nbhd_detGen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
    ∃ (W : M.Opens) (hW : IsAffineOpen W), y ∈ W ∧ ∃ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ ∧ Nonempty Y.DetGen := by
  intro F _ _ 𝔠 M U y
  obtain ⟨W₀, hW₀, hyW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens) (show y ∈ (⊤ : M.Opens) from trivial)
  have hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y₀, φ₀, h₀⟩ := exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y₀
  let q := hW₀.primeIdealOf ⟨y, hyW₀⟩
  let p : Ideal Γ(M, W₀) := q.asIdeal
  haveI : p.IsPrime := q.isPrime
  haveI : Module.FinitePresentation Γ(M, W₀) Y₀.Lie := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Y₀.Lie) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hg, hfree, hfr⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl Y₀.Lie) (Localization.AtPrime p)
  have hyW : y ∈ M.basicOpen g := by
    have h1 : q ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec q ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  have hW : IsAffineOpen (M.basicOpen g) := hW₀.basicOpen g
  letI : Algebra Γ(M, W₀) Γ(M, M.basicOpen g) := (M.presheaf.map (homOfLE (M.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g Γ(M, M.basicOpen g) := hW₀.isLocalization_basicOpen g
  obtain ⟨Y, ψ, hψ⟩ := exists_isPullBy (S' := Sp Γ(M, M.basicOpen g)) Y₀
    (spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)))
  have hcomp : spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)) ≫ hW₀.fromSpec = hW.fromSpec :=
    hW₀.map_fromSpec hW (homOfLE (M.basicOpen_le g)).op
  refine ⟨M.basicOpen g, hW, hyW, Y, ψ ≫ φ₀, by rw [← hcomp]; exact hψ.comp h₀, ?_⟩
  obtain ⟨e, -, -⟩ := exists_lieEquiv (R' := Γ(M, M.basicOpen g)) hψ
  haveI : Module.Finite (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie)
  have hd : Module.finrank (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) = Module.finrank ℚ F := by
    rw [hfr]
    exact hrk q
  haveI : Nontrivial (Localization.Away g) :=
    (IsLocalization.Away.lift g (S := Localization.Away g) (g := algebraMap Γ(M, W₀) (Localization.AtPrime p))
      (IsLocalization.map_units (Localization.AtPrime p) ⟨g, hg⟩)).domain_nontrivial
  let b₀ := Module.finBasisOfFinrankEq (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) hd
  haveI : IsLocalizedModule (Submonoid.powers g)
      (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Γ(M, M.basicOpen g) _).2
      (TensorProduct.isBaseChange _ _ _)
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie) (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(M, M.basicOpen g)
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars Γ(M, W₀) ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) Γ(M, M.basicOpen g)
  exact ⟨DetGen.ofBasis Y ((Module.Basis.ofRepr Ψ').map e)⟩

end GlobalTheory.RealMult.Obj
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValGlue

open GlobalTheory.RealMult.RuleDescend (detCorr_comp isPullBy_comp)

theorem exists_spMap_fromSpec {M : Scheme.{0}} {W : M.Opens} (hW : IsAffineOpen W) {T : Type} [CommRing T]
    (f : Sp T ⟶ M) (hf : Set.range f ⊆ (W : Set M)) : ∃ ψ : Γ(M, W) →+* T, spMap ψ ≫ hW.fromSpec = f := by
  have hf' : Set.range f ⊆ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')).hom, ?_⟩
  change Spec.map (Spec.preimage (IsOpenImmersion.lift hW.fromSpec f hf')) ≫ _ = _
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_span_eq_top {R : Type} [CommRing R] {M : Scheme.{0}} (b : Sp R ⟶ M) (P : M.Opens → Prop)
    (hP : ∀ x : M, ∃ W, P W ∧ x ∈ W) : ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M) := by
  refine ⟨{g | ∃ W, P W ∧ Set.range (spMap (algebraMap R (Localization.Away g)) ≫ b) ⊆ (W : Set M)}, ?_,
    fun g hg ↦ hg⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  obtain ⟨W, hW, hx⟩ := hP (b p)
  let O : Set (PrimeSpectrum R) := (b ⁻¹ᵁ W).carrier
  have ho : IsOpen O := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ O from hx) ho
  refine hpg (hle (Ideal.subset_span ⟨W, hW, ?_⟩))
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact ⟨q, rfl⟩
  exact hsub hq

theorem existsUnique_glue {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤)
    (v : ∀ g : s, Localization.Away (g : R))
    (hv : ∀ (g h : s) (T : Type) [CommRing T] (f₁ : Localization.Away (g : R) →+* T)
      (f₂ : Localization.Away (h : R) →+* T), f₁.comp (algebraMap R _) = f₂.comp (algebraMap R _) →
      f₁ (v g) = f₂ (v h)) :
    ∃! x : R, ∀ g : s, algebraMap R (Localization.Away (g : R)) x = v g := by
  refine Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs v fun g h ↦ ?_
  refine hv g h (Localization.Away (g.1 * h.1)) (IsLocalization.Away.awayToAwayRight g.1 h.1)
    (IsLocalization.Away.awayToAwayLeft h.1 g.1) (RingHom.ext fun r ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq]

theorem eq_of_loc {R : Type} [CommRing R] {s : Set R} (hs : Ideal.span s = ⊤) {x y : R}
    (h : ∀ g : s, algebraMap R (Localization.Away (g : R)) x = algebraMap R _ y) : x = y :=
  (existsUnique_glue hs (fun _ ↦ algebraMap R _ y) fun _ _ _ _ _ _ e ↦ RingHom.congr_fun e y).unique h fun _ ↦ rfl

theorem tensorEval_comp {R₀ A R R' : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] [CommRing R']
    [Algebra R₀ R'] (ψ : A →+* R) (τ : R →ₐ[R₀] R') (h : R₀ ⊗[ℤ] A) :
    tensorEval ((τ : R →+* R').comp ψ) h = τ (tensorEval ψ h) := by
  induction h with
  | zero => simp
  | tmul r a => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem existsUnique_smul {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) :
    ∃! u : R, δ'.1 = u • δ.1 := by
  haveI := X.invertible_detOmega
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : δ'.1 ∈ Submodule.span R {δ.1})
  refine ⟨a, ha.symm, fun c hc ↦ eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm, ← hc, smul_comm a, ha]

theorem presVal_exists {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) :
    ∃ v, IsPresVal k δY h δ ψ χ v := by
  obtain ⟨δ'', -, hu''⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, -, hu'⟩ := existsUnique_smul δ δ''
  refine ⟨u ^ k * tensorEval ψ h, fun δ₃ u₃ h₃ e₃ ↦ ?_⟩
  obtain rfl := hu'' δ₃ h₃
  obtain rfl := hu' u₃ e₃
  rfl

theorem presVal_unique {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap ψ) χ) {v₁ v₂ : R}
    (h₁ : IsPresVal k δY h δ ψ χ v₁) (h₂ : IsPresVal k δY h δ ψ χ v₂) : v₁ = v₂ := by
  obtain ⟨δ'', h'', -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ δ''
  rw [h₁ δ'' u h'' hu, h₂ δ'' u h'' hu]

theorem presVal_pull {R₀ : Type} [CommRing R₀] {k : ℕ} {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    {δY : Y.DetGen} {h : R₀ ⊗[ℤ] A} {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)}
    {δ : X.DetGen} {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} {v : R} (hX : X.IsPullBy Y (spMap ψ) χ)
    (hv : IsPresVal k δY h δ ψ χ v) {R' : Type} [CommRing R'] [Algebra R₀ R'] (τ : R →ₐ[R₀] R')
    {X' : Obj F 𝔠 (Sp R')} {θ : X'.A.left ⟶ X.A.left} {δ' : X'.DetGen}
    (hX' : X'.IsPullBy X (spMap (τ : R →+* R')) θ) (hδ' : Obj.DetCorr (τ : R →+* R') θ δ.1 δ'.1) :
    IsPresVal k δY h δ' ((τ : R →+* R').comp ψ) (θ ≫ χ) (τ v) := by
  intro ε' u' hε' hu'
  obtain ⟨ε, hε, -⟩ := hX.existsUnique_detGen ψ δY
  obtain ⟨u, hu, -⟩ := existsUnique_smul δ ε
  have hun : IsUnit (τ u) := (RuleDescend.isUnit_of_eq_smul δ ε u hu).map τ
  let ε'' : X'.DetGen := ⟨τ u • δ'.1, (Submodule.span_singleton_smul_eq hun _).trans δ'.2⟩
  have d : Obj.DetCorr (τ : R →+* R') θ ε.1 ε''.1 := fun w w' hw ↦ by
    change τ u • δ'.1 w' = _
    rw [hδ' w w' hw, hu]
    simp
  obtain rfl : ε' = ε'' :=
    ((isPullBy_comp hX hX').existsUnique_detGen _ δY).unique hε' (detCorr_comp hX hX' hε d)
  obtain rfl : u' = τ u := (existsUnique_smul δ' ε'').unique hu' rfl
  rw [hv ε u hε hu, map_mul, map_pow, tensorEval_comp]

theorem detCorr_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
    {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')}
    {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (hφ : X'.IsPullBy X (spMap σ) φ) (hψ : X''.IsPullBy X' (spMap τ) ψ)
    {δ : X.DetGen} {δ' : X'.DetGen} {δ'' : X''.DetGen} (h' : Obj.DetCorr σ φ δ.1 δ'.1)
    (h'' : Obj.DetCorr (τ.comp σ) (ψ ≫ φ) δ.1 δ''.1) : Obj.DetCorr τ ψ δ'.1 δ''.1 := by
  obtain ⟨δ₃, h₃, -⟩ := hψ.existsUnique_detGen τ δ'
  obtain rfl : δ'' = δ₃ :=
    ((isPullBy_comp hφ hψ).existsUnique_detGen _ δ).unique h'' (detCorr_comp hφ hψ h' h₃)
  exact h₃

theorem existsUnique_isModelVal : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
  (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k),
  (∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
    Y.IsPullBy U hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M, W), IsChartFun r₀ Y δY h) →
  (∀ (W₁ : M.Opens) (hW₁ : IsAffineOpen W₁) (Y₁ : Obj F 𝔠 (Sp Γ(M, W₁))) (φ₁ : Y₁.A.left ⟶ U.A.left),
    Y₁.IsPullBy U hW₁.fromSpec φ₁ → ∀ (δ₁ : Y₁.DetGen) (h₁ : R₀ ⊗[ℤ] Γ(M, W₁)), IsChartFun r₀ Y₁ δ₁ h₁ →
  ∀ (W₂ : M.Opens) (hW₂ : IsAffineOpen W₂) (Y₂ : Obj F 𝔠 (Sp Γ(M, W₂))) (φ₂ : Y₂.A.left ⟶ U.A.left),
    Y₂.IsPullBy U hW₂.fromSpec φ₂ → ∀ (δ₂ : Y₂.DetGen) (h₂ : R₀ ⊗[ℤ] Γ(M, W₂)), IsChartFun r₀ Y₂ δ₂ h₂ →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (ψ₁ : Γ(M, W₁) →+* R) (χ₁ : X.A.left ⟶ Y₁.A.left) (ψ₂ : Γ(M, W₂) →+* R) (χ₂ : X.A.left ⟶ Y₂.A.left),
    X.IsPullBy Y₁ (spMap ψ₁) χ₁ → X.IsPullBy Y₂ (spMap ψ₂) χ₂ →
    ∀ v₁ v₂ : R, IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁ → IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂ → v₁ = v₂) →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), levObj 𝔠 N R X → ∀ δ : X.DetGen,
    ∃! v : R, IsModelVal r₀ U X δ v := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ H1 H2 R _ _ X hlev δ
  have hN : IsUnit (N : R) := hlev.1
  obtain ⟨β⟩ := hlev.2
  have hNu : IsUnit (algebraMap ℤ R (N : ℤ)) := by simpa using hN
  obtain ⟨b, -, φb, hb, -⟩ :=
    (hDP.1 (Sp R) (spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) hNu)) X β).exists
  obtain ⟨S, hS, hSW⟩ := exists_span_eq_top b (fun W ↦ ∃ (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φY ∧ Nonempty Y.DetGen) (fun x ↦ by
    obtain ⟨W, hW, hx, Y, φY, hY, hδ⟩ := Obj.exists_affine_nbhd_detGen F 𝔠 M U x
    exact ⟨W, ⟨hW, Y, φY, hY, hδ⟩, hx⟩)

  have hloc : ∀ g : S, ∃ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W)))
      (φY : Y.A.left ⟶ U.A.left) (_ : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W))
      (_ : IsChartFun r₀ Y δY h) (ψ : Γ(M, W) →+* Localization.Away (g : R))
      (Xg : Obj F 𝔠 (Sp (Localization.Away (g : R)))) (φg : Xg.A.left ⟶ X.A.left)
      (_ : Xg.IsPullBy X (spMap (algebraMap R _)) φg) (δg : Xg.DetGen)
      (_ : Obj.DetCorr (algebraMap R _) φg δ.1 δg.1) (χ : Xg.A.left ⟶ Y.A.left)
      (_ : Xg.IsPullBy Y (spMap ψ) χ) (v : Localization.Away (g : R)), IsPresVal k δY h δg ψ χ v := by
    intro g
    obtain ⟨W, ⟨hW, Y, φY, hY, ⟨δY⟩⟩, hsub⟩ := hSW g g.2
    obtain ⟨ψ, hψ⟩ := exists_spMap_fromSpec hW _ hsub
    obtain ⟨h, hh⟩ := H1 W hW Y φY hY δY
    obtain ⟨Xg, φg, hXg⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away (g : R))))
    obtain ⟨δg, hδg, -⟩ := hXg.existsUnique_detGen _ δ
    have h1 : Xg.IsPullBy U (spMap ψ ≫ hW.fromSpec) (φg ≫ φb) := by rw [hψ]; exact hXg.comp hb
    obtain ⟨χ, hχ, -⟩ := h1.cancel hY
    obtain ⟨v, hv⟩ := presVal_exists k δY h δg hχ
    exact ⟨W, hW, Y, φY, hY, δY, h, hh, ψ, Xg, φg, hXg, δg, hδg, χ, hχ, v, hv⟩
  choose W hW Y φY hY δY hc hhc ψ Xg φg hXg δg hδg χ hχ vg hvg using hloc

  have side : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (ρ : R →+* T), ρ.comp (algebraMap R₀ R) = algebraMap R₀ T →
      ∀ (XT : Obj F 𝔠 (Sp T)) (φT : XT.A.left ⟶ X.A.left), XT.IsPullBy X (spMap ρ) φT →
      ∀ δT : XT.DetGen, Obj.DetCorr ρ φT δ.1 δT.1 →
      ∀ (g : S) (f : Localization.Away (g : R) →+* T), f.comp (algebraMap R _) = ρ →
      ∃ θ, XT.IsPullBy (Y g) (spMap (f.comp (ψ g))) θ ∧
        IsPresVal k (δY g) (hc g) δT (f.comp (ψ g)) θ (f (vg g)) := by
    intro T _ _ ρ hρ XT φT hXT δT hδT g f ef
    subst ef
    have hXT' := hXT
    rw [spMap_comp] at hXT'
    obtain ⟨θ, hθ, hθφ⟩ := hXT'.cancel (hXg g)
    have hd : Obj.DetCorr f θ (δg g).1 δT.1 := detCorr_cancel (hXg g) hθ (hδg g) (hθφ ▸ hδT)
    let fA : Localization.Away (g : R) →ₐ[R₀] T :=
      { f with
        commutes' := fun r ↦ by
          rw [IsScalarTower.algebraMap_apply R₀ R (Localization.Away (g : R)), ← hρ]
          rfl }
    refine ⟨θ ≫ χ g, by rw [spMap_comp]; exact hθ.comp (hχ g), ?_⟩
    exact presVal_pull (hχ g) (hvg g) fA hθ hd
  obtain ⟨v, hv, huniq⟩ := existsUnique_glue hS vg (by
    intro g g' T _ f₁ f₂ e
    letI : Algebra R₀ T := ((f₁.comp (algebraMap R _)).comp (algebraMap R₀ R)).toAlgebra
    obtain ⟨XT, φT, hXT⟩ := Obj.exists_isPullBy X (spMap (f₁.comp (algebraMap R _)))
    obtain ⟨δT, hδT, -⟩ := hXT.existsUnique_detGen _ δ
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T _ rfl XT φT hXT δT hδT g f₁ rfl
    obtain ⟨θ₂, hθ₂, hv₂⟩ := side T _ rfl XT φT hXT δT hδT g' f₂ e.symm
    exact H2 (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (W g') (hW g') (Y g') (φY g') (hY g')
      (δY g') (hc g') (hhc g') T XT δT _ θ₁ _ θ₂ hθ₁ hθ₂ _ _ hv₁ hv₂)
  refine ⟨v, ?_, fun v' hv' ↦ huniq v' fun g ↦ ?_⟩
  · intro R' _ _ σ X' φ' δ' hX' hδ' W' hW' Y' φY' hY' δY' h' hh' ψ' χ' hχ'
    obtain ⟨w, hw⟩ := presVal_exists k δY' h' δ' hχ'
    suffices e : σ v = w by rw [e]; exact hw
    have hS' : Ideal.span ((σ : R →+* R') '' S) = ⊤ := by rw [← Ideal.map_span, hS, Ideal.map_top]
    refine eq_of_loc hS' ?_
    rintro ⟨_, g, hg, rfl⟩
    let T := Localization.Away ((σ : R →+* R') g)
    obtain ⟨XT, θ, hθ⟩ := Obj.exists_isPullBy X' (spMap (algebraMap R' T))
    obtain ⟨δT, hδT, -⟩ := hθ.existsUnique_detGen _ δ'
    have e1 : IsPresVal k δY' h' δT ((algebraMap R' T).comp ψ') (θ ≫ χ') (algebraMap R' T w) :=
      presVal_pull hχ' hw (IsScalarTower.toAlgHom R₀ R' T) hθ hδT
    have p1 : XT.IsPullBy Y' (spMap ((algebraMap R' T).comp ψ')) (θ ≫ χ') := by
      rw [spMap_comp]; exact hθ.comp hχ'
    have ef : (Localization.awayMap (σ : R →+* R') g).comp (algebraMap R _) =
        (algebraMap R' T).comp (σ : R →+* R') := IsLocalization.map_comp _
    obtain ⟨θ₁, hθ₁, hv₁⟩ := side T ((algebraMap R' T).comp (σ : R →+* R'))
      (by rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, ← IsScalarTower.algebraMap_eq]) XT (θ ≫ φ')
      (by rw [spMap_comp]; exact hθ.comp hX') δT
      (detCorr_comp hX' hθ hδ' hδT) ⟨g, hg⟩ _ ef
    have e2 := H2 _ (hW _) _ _ (hY _) _ _ (hhc _) W' hW' Y' φY' hY' δY' h' hh' T XT δT _ θ₁ _ _ hθ₁ p1 _ _ hv₁ e1
    rw [← hv ⟨g, hg⟩] at e2
    exact (RingHom.congr_fun ef v).symm.trans e2
  · exact presVal_unique k _ _ _ (hχ g)
      (hv' _ (IsScalarTower.toAlgHom R₀ R (Localization.Away (g : R))) (Xg g) (φg g) (δg g) (hXg g) (hδg g)
        (W g) (hW g) (Y g) (φY g) (hY g) (δY g) (hc g) (hhc g) (ψ g) (χ g) (hχ g)) (hvg g)

end GlobalTheory.RealMult.ModelValGlue
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem DetGen.smul_cancel {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) {r s : R} (h : r • δ.1 = s • δ.1) : r = s := by
  haveI := Obj.invertible_detOmega X
  refine FaithfulSMul.eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_
  have hm : m ∈ Submodule.span R {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
  rw [smul_comm r t, smul_comm s t, h]

theorem isModelVal_homog : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R : Type) [CommRing R] [Algebra R₀ R]
  (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c v : R), δ'.1 = c • δ.1 → IsModelVal r₀ U X δ' v →
    IsModelVal r₀ U X δ (c ^ k * v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R _ _ X δ δ' c v hδ hv
  intro R' _ _ σ X' φ' δ'' hX' hδ'' W hW Y φY hY δY h hh ψ χ hχ δY' u hY' hu

  have hδm : δ.1 ∈ Submodule.span R {δ'.1} := by rw [δ'.2]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hδm
  have hdc : d * c = 1 := DetGen.smul_cancel X δ (by rw [mul_smul, ← hδ, hd, one_smul])

  have hgen : Submodule.span R' {((σ : R →+* R') c) • δ''.1} = ⊤ := by
    refine eq_top_iff.2 fun m _ ↦ ?_
    have hm : m ∈ Submodule.span R' {δ''.1} := by rw [δ''.2]; exact Submodule.mem_top
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
    refine Submodule.mem_span_singleton.2 ⟨t * (σ : R →+* R') d, ?_⟩
    rw [smul_smul, _root_.mul_assoc, ← map_mul, hdc, map_one, _root_.mul_one]

  have hcorr : Obj.DetCorr (σ : R →+* R') φ' δ'.1 (((σ : R →+* R') c) • δ''.1) := by
    intro w w' hw
    rw [hδ, AlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul, hδ'' w w' hw,
      map_mul]
  obtain ⟨δ''', hδ''', huniq⟩ := hX'.existsUnique_detGen (σ : R →+* R') δ'
  have heq : δ'''.1 = ((σ : R →+* R') c) • δ''.1 :=
    (congrArg Subtype.val (huniq ⟨_, hgen⟩ hcorr)).symm
  have hYm : δY'.1 ∈ Submodule.span R' {δ'''.1} := by rw [δ'''.2]; exact Submodule.mem_top
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 hYm
  have hval := hv R' σ X' φ' δ''' hX' hδ''' W hW Y φY hY δY h hh ψ χ hχ δY' u' hY' hu'.symm
  have huu : u = u' * (σ : R →+* R') c := DetGen.smul_cancel X' δ'' (by rw [← hu, ← hu', heq, smul_smul])
  rw [huu, mul_pow, map_mul, map_pow, hval]
  simp only [RingHom.coe_coe]
  ring

end GlobalTheory.RealMult
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValBaseChange

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMapR_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) :=
  RingHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [Chart.dualMapR]) (by simp [Chart.dualMapR])

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lieCorr_comp {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')} {σ : R →+* R'}
    {τ : R' →+* R''} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left} {v : X.Lie} {v' : X'.Lie}
    {v'' : X''.Lie} (h : Obj.LieCorr σ φ v v') (h' : Obj.LieCorr τ φ' v' v'') :
    Obj.LieCorr (τ.comp σ) (φ' ≫ φ) v v'' := by
  unfold Obj.LieCorr at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc, ← spMap_comp_ringHom, ← dualMapR_comp_ringHom]

theorem exists_lieCorr {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (v : X.Lie) : ∃ w : X'.Lie, Obj.LieCorr σ φ v w := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ⟨e (1 ⊗ₜ v), (he _ _).2 rfl⟩

theorem lieCorr_unique {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {w₁ w₂ : X'.Lie} (h₁ : Obj.LieCorr σ φ v w₁)
    (h₂ : Obj.LieCorr σ φ v w₂) : w₁ = w₂ := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ((he _ _).1 h₁).trans ((he _ _).1 h₂).symm

theorem isPullBy_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') :
    X''.IsPullBy X (spMap (τ.comp σ)) (φ' ≫ φ) := by
  rw [spMap_comp_ringHom]
  exact hp'.comp hp

theorem detCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') {δ : X.DetOmega} {δ' : X'.DetOmega}
    {δ'' : X''.DetOmega} (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ φ' δ' δ'') :
    Obj.DetCorr (τ.comp σ) (φ' ≫ φ) δ δ'' := by
  intro v v'' hv
  choose v' hv' using fun i ↦ exists_lieCorr hp (v i)
  choose w hw using fun i ↦ exists_lieCorr hp' (v' i)
  have hwv : w = v'' := funext fun i ↦
    lieCorr_unique (isPullBy_comp hp hp') (lieCorr_comp (hv' i) (hw i)) (hv i)
  subst hwv
  rw [hd' v' w hw, hd v v' hv', RingHom.comp_apply]

end GlobalTheory.RealMult.ModelValBaseChange

namespace GlobalTheory.RealMult

open ModelValBaseChange in

theorem isModelVal_baseChange : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R R' : Type) [CommRing R] [Algebra R₀ R]
  [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X : Obj F 𝔠 (Sp R)) (X' : Obj F 𝔠 (Sp R'))
  (φ : X'.A.left ⟶ X.A.left) (δ : X.DetGen) (δ' : X'.DetGen) (v : R), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
  Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → IsModelVal r₀ U X δ v → IsModelVal r₀ U X' δ' (σ v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R R' _ _ _ _ σ X X' φ δ δ' v hp hd hv
  intro R'' _ _ τ X'' φ'' δ'' hp'' hd'' W hW Y φY hY δY h hh ψ χ hχ
  have hc : ((τ.comp σ : R →ₐ[R₀] R'') : R →+* R'') = (τ : R' →+* R'').comp (σ : R →+* R') := rfl
  have := hv R'' (τ.comp σ) X'' (φ'' ≫ φ) δ'' (by rw [hc]; exact isPullBy_comp hp hp'')
    (by rw [hc]; exact detCorr_comp hp hp'' hd hd'') W hW Y φY hY δY h hh ψ χ hχ
  exact this

end GlobalTheory.RealMult
end
end

section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertible_of_faithfully_flat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  first | exact @GlobalTheory.FFDescent.invertible_of_invertible_baseChange | exact GlobalTheory.FFDescent.invertible_of_invertible_baseChange | (intros; apply GlobalTheory.FFDescent.invertible_of_invertible_baseChange <;> assumption)
end

section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_tensor_module_compat : ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by
  first | exact @GlobalTheory.baseChange_tensor_int_field_equiv | exact GlobalTheory.baseChange_tensor_int_field_equiv | (intros; apply GlobalTheory.baseChange_tensor_int_field_equiv <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.ChartFun

open GlobalTheory.RealMult.RuleDescend

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem eq_of_loc_away (R : Type) [CommRing R] (f : PrimeSpectrum R → R) (hf : ∀ p, f p ∉ p.asIdeal)
    (x y : R) (h : ∀ p, algebraMap R (Localization.Away (f p)) x = algebraMap R (Localization.Away (f p)) y) :
    x = y := by
  rw [← sub_eq_zero]
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R (x - y))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp := h p
    rw [← sub_eq_zero, ← map_sub] at hp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f p)) _ _).1 hp
    have hmem : f p ^ n ∈ I := by
      simp only [I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact hn
    exact hf p (hq.isPrime.mem_of_pow_mem n (hIq hmem))
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

theorem isRapoport_of_range_subset {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    (X : Obj F 𝔠 (Sp A)) (φ : X.A.left ⟶ U.A.left) (hX : X.IsPullBy U c φ) (hr : Set.range c ⊆ U.rapLocus) :
    X.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s ↦ ?_
  intro K _ t hs Y ψ hY
  obtain ⟨p, rfl⟩ := hs
  exact hr ⟨t p, rfl⟩ K (t ≫ c) ⟨p, rfl⟩ Y (ψ ≫ φ) (hY.comp hX)

theorem isRapoport_of_field_ext {K L : Type} [Field K] [Field L] (σ : K →+* L) {X : Obj F 𝔠 (Sp K)}
    {X' : Obj F 𝔠 (Sp L)} {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX' : X'.IsRapoport) :
    X.IsRapoport := by
  letI := σ.toAlgebra
  obtain ⟨e, -, he⟩ := Obj.exists_lieEquiv (R' := L) h
  letI := X.lieModule
  letI := X'.lieModule
  obtain ⟨_, hff, ⟨Φ⟩⟩ := GlobalTheory.T.base_change_tensor_module_compat K L (𝓞 F) X.Lie X'.Lie e he
  haveI : Module.Invertible (L ⊗[ℤ] 𝓞 F) X'.Lie := hX'
  haveI : IsNoetherianRing (K ⊗[ℤ] 𝓞 F) := Algebra.FiniteType.isNoetherianRing K _
  exact GlobalTheory.T.invertible_of_faithfully_flat (K ⊗[ℤ] 𝓞 F) (L ⊗[ℤ] 𝓞 F) X.Lie (Module.Invertible.congr Φ.symm)

theorem range_subset_rapLocus {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    {X : Obj F 𝔠 (Sp A)} {φ : X.A.left ⟶ U.A.left} (h : X.IsPullBy U c φ) (hX : X.IsRapoport) :
    Set.range c ⊆ U.rapLocus := by
  rintro _ ⟨x, rfl⟩ K _ t ⟨y, hy⟩ Z χ hZ
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := c) y x hy
  let L : Type := (pullback t c).residueField z
  let j : Sp L ⟶ pullback t c := (pullback t c).fromSpecResidueField z
  obtain ⟨σ, hσ⟩ : ∃ σ : K →+* L, spMap σ = j ≫ pullback.fst t c :=
    ⟨(Spec.preimage (j ≫ pullback.fst t c)).hom, Spec.map_preimage _⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A →+* L, spMap τ = j ≫ pullback.snd t c :=
    ⟨(Spec.preimage (j ≫ pullback.snd t c)).hom, Spec.map_preimage _⟩
  obtain ⟨Z', χ', hZ'⟩ := Z.exists_isPullBy (spMap σ)
  have h₁ := hZ'.comp hZ
  have e : spMap σ ≫ t = spMap τ ≫ c := by rw [hσ, hτ, Category.assoc, Category.assoc, pullback.condition]
  rw [e] at h₁
  obtain ⟨ψ, hψ, -⟩ := h₁.cancel h
  exact isRapoport_of_field_ext σ hZ' (hψ.isRapoport τ hX)

theorem val_eq_of_factor {R₀ : Type} [CommRing R₀] {k : ℕ} {Q : ObjClass 𝔠} (r : Rule Q R₀ k)
    {A S T : Type} [CommRing A] [CommRing S] [CommRing T] [Algebra R₀ S] [Algebra R₀ T]
    {Y : Obj F 𝔠 (Sp A)} {X : Obj F 𝔠 (Sp S)} {Z : Obj F 𝔠 (Sp T)} (κ : A →+* S) (ρ : S →ₐ[R₀] T) (ν : A →+* T)
    (hν : (ρ : S →+* T).comp κ = ν)
    {φ : X.A.left ⟶ Y.A.left} {χ : Z.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap κ) φ)
    (hZ : Z.IsPullBy Y (spMap ν) χ) (qX : Q S X) (qZ : Q T Z)
    {δY : Y.DetGen} {δX : X.DetGen} {δZ : Z.DetGen} (dX : Obj.DetCorr κ φ δY.1 δX.1)
    (dZ : Obj.DetCorr ν χ δY.1 δZ.1) :
    r.val T Z qZ δZ = ρ (r.val S X qX δX) := by
  subst hν
  have hZ' := hZ
  rw [RuleDescend.spMap_comp] at hZ'
  obtain ⟨ψ, hψ, hψφ⟩ := hZ'.cancel hX
  obtain ⟨ε, e⟩ := (hψ.existsUnique_detGen (ρ : S →+* T) δX).exists
  have e' := detCorr_comp hX hψ dX e
  rw [hψφ] at e'
  obtain rfl : ε = δZ := (hZ.existsUnique_detGen _ δY).unique e' dZ
  exact r.baseChange S T ρ X qX Z qZ ψ δX ε hψ e

abbrev res (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) : Γ(M, W) →+* Γ(M, W') :=
  (M.presheaf.map (homOfLE hle).op).hom

def chartMap (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] :
    Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
  (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom.comp (res M hle)

theorem chartMap_apply (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] (a : Γ(M, W)) :
    chartMap M hle R₀ a = 1 ⊗ₜ res M hle a := rfl

theorem spMap_chartMap_fromSpec (M : Scheme.{0}) {W W' : M.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] :
    spMap (chartMap M hle R₀) ≫ hW.fromSpec = coefSpecMap hW' R₀ := by
  rw [chartMap, RuleDescend.spMap_comp, Category.assoc, coefSpecMap, ← hW.map_fromSpec hW' (homOfLE hle).op]
  rfl

theorem isRapoport_chart {M : Scheme.{0}} {U : Obj F 𝔠 M} {V : M.Opens} (hV : (V : Set M) = U.rapLocus)
    {W W' : M.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W ⊓ V) (R₀ : Type) [CommRing R₀]
    {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left} (hY : Y.IsPullBy U hW.fromSpec φY)
    {X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W')))} {φ' : X'.A.left ⟶ Y.A.left}
    (hX' : X'.IsPullBy Y (spMap (chartMap M (hle.trans inf_le_left) R₀)) φ') : X'.IsRapoport := by
  have h := hX'.comp hY
  rw [spMap_chartMap_fromSpec M hW hW'] at h
  refine isRapoport_of_range_subset U _ X' _ h ?_
  rintro _ ⟨y, rfl⟩
  rw [← hV]
  have : (coefSpecMap hW' R₀) y ∈ Set.range hW'.fromSpec := ⟨_, rfl⟩
  rw [hW'.range_fromSpec] at this
  exact (hle.trans inf_le_right) this

abbrev resL (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) : Γ(M, W) →ₗ[ℤ] Γ(M, W') :=
  (res M hle).toAddMonoidHom.toIntLinearMap

def RestrictsToVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {M : Scheme.{0}} (V : M.Opens)
    {W : M.Opens} (Y : Obj F 𝔠 (Sp Γ(M, W))) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)) : Prop :=
  ∀ (W' : M.Opens), IsAffineOpen W' → ∀ (hle : W' ≤ W ⊓ V) (X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W'))))
    (φ' : X'.A.left ⟶ Y.A.left) (hX' : X'.IsRapoport) (δ' : X'.DetGen),
    X'.IsPullBy Y (spMap (chartMap M (hle.trans inf_le_left) R₀)) φ' →
    Obj.DetCorr (chartMap M (hle.trans inf_le_left) R₀) φ' δY.1 δ'.1 →
    r₀.val _ X' hX' δ' = LinearMap.lTensor R₀ (resL M (hle.trans inf_le_left)) h

theorem isChartFun_of_restrictsToVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {M : Scheme.{0}} {U : Obj F 𝔠 M} {V : M.Opens} (hV : (V : Set M) = U.rapLocus)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}
    (hY : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)) (hh : RestrictsToVal r₀ V Y δY h) :
    IsChartFun r₀ Y δY h := by
  intro R _ _ ψ X φ hX δ hp hd
  have key : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧
      algebraMap R (Localization.Away f) (r₀.val R X hX δ) = algebraMap R (Localization.Away f) (tensorEval ψ h) := by
    intro p
    have hm : (spMap ψ ≫ hW.fromSpec) p ∈ W ⊓ V := by
      refine ⟨?_, ?_⟩
      · rw [← hW.range_fromSpec]; exact ⟨_, rfl⟩
      · rw [hV]; exact range_subset_rapLocus U _ (hp.comp hY) hX ⟨p, rfl⟩
    obtain ⟨W', hW', hmW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.isBasis_affineOpens hm
    obtain ⟨f, hf, g, hg⟩ := GlobalTheory.exists_away_factor_coefSpecMap M R₀ R (spMap ψ ≫ hW.fromSpec) W' hW' p hmW'
    refine ⟨f, hf, ?_⟩
    have hτ : (g : R₀ ⊗[ℤ] Γ(M, W') →+* Localization.Away f).comp (chartMap M (hle.trans inf_le_left) R₀) =
        (algebraMap R (Localization.Away f)).comp ψ := by
      rw [← spMap_chartMap_fromSpec M hW hW' (hle.trans inf_le_left), ← Category.assoc, ← Category.assoc,
        cancel_mono, ← RuleDescend.spMap_comp, ← RuleDescend.spMap_comp] at hg
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
    obtain ⟨X', φ', hX'⟩ := Y.exists_isPullBy (spMap (chartMap M (hle.trans inf_le_left) R₀))
    obtain ⟨δ', hδ'⟩ := (hX'.existsUnique_detGen _ δY).exists
    have hr' := isRapoport_chart hV hW hW' hle R₀ hY hX'
    obtain ⟨Z, χ, hZ⟩ := X.exists_isPullBy (spMap (algebraMap R (Localization.Away f)))
    obtain ⟨δZ, hδZ⟩ := (hZ.existsUnique_detGen _ δ).exists
    have hrZ := hZ.isRapoport _ hX
    have e₁ : r₀.val _ Z hrZ δZ = algebraMap R (Localization.Away f) (r₀.val R X hX δ) :=
      r₀.baseChange R _ (IsScalarTower.toAlgHom R₀ R (Localization.Away f)) X hX Z hrZ χ δ δZ hZ hδZ
    have e₂ := val_eq_of_factor r₀ _ g _ hτ hX' (isPullBy_comp hp hZ) hr' hrZ hδ' (detCorr_comp hp hZ hd hδZ)
    rw [← e₁, e₂, hh W' hW' hle X' φ' hr' δ' hX' hδ']
    clear e₁ e₂ hh
    induction h using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      have h1 : g (1 ⊗ₜ res M (hle.trans inf_le_left) a) = algebraMap R (Localization.Away f) (ψ a) :=
        RingHom.congr_fun hτ a
      have h2 : LinearMap.lTensor R₀ (resL M (hle.trans inf_le_left)) (r ⊗ₜ a) =
          r • ((1 : R₀) ⊗ₜ[ℤ] res M (hle.trans inf_le_left) a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]; rfl
      rw [h2, map_smul, h1, tensorEval_tmul, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  choose f hf he using key
  exact eq_of_loc_away R f hf _ _ he

abbrev coefL (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] : R₀ →ₗ[ℤ] R₁ :=
  (algebraMap R₀ R₁).toAddMonoidHom.toIntLinearMap

theorem rTensor_val_eq {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {k : ℕ}
    (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k)
    (hr : ∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
      r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ)
    {M : Scheme.{0}} {W W' : M.Opens} (hle : W' ≤ W) {Y : Obj F 𝔠 (Sp Γ(M, W))} (δY : Y.DetGen)
    {Y₁ : Obj F 𝔠 (Sp (R₁ ⊗[ℤ] Γ(M, W)))} {φ₁ : Y₁.A.left ⟶ Y.A.left} {δ₁ : Y₁.DetGen}
    (hY₁ : Y₁.IsPullBy Y (spMap (chartMap M le_rfl R₁)) φ₁) (hδ₁ : Obj.DetCorr (chartMap M le_rfl R₁) φ₁ δY.1 δ₁.1)
    {X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W')))} {φ' : X'.A.left ⟶ Y.A.left} (hr' : X'.IsRapoport) {δ' : X'.DetGen}
    (hX' : X'.IsPullBy Y (spMap (chartMap M hle R₀)) φ') (hδ' : Obj.DetCorr (chartMap M hle R₀) φ' δY.1 δ'.1) :
    LinearMap.rTensor Γ(M, W') (coefL R₀ R₁) (r₀.val _ X' hr' δ') =
      LinearMap.lTensor R₁ (resL M hle) (r₁.val _ Y₁ trivial δ₁) := by
  let ρ₁ : R₁ ⊗[ℤ] Γ(M, W) →ₐ[R₁] R₁ ⊗[ℤ] Γ(M, W') :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (res M hle).toIntAlgHom
  let θ : R₀ ⊗[ℤ] Γ(M, W') →+* R₁ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.map (algebraMap R₀ R₁).toIntAlgHom (AlgHom.id ℤ Γ(M, W'))).toRingHom
  obtain ⟨Z, χ, hZ⟩ := Y.exists_isPullBy (spMap (chartMap M hle R₁))
  obtain ⟨δZ, hδZ⟩ := (hZ.existsUnique_detGen _ δY).exists
  have h₁ : (ρ₁ : R₁ ⊗[ℤ] Γ(M, W) →+* R₁ ⊗[ℤ] Γ(M, W')).comp (chartMap M le_rfl R₁) = chartMap M hle R₁ := by
    ext a; simp [ρ₁, chartMap_apply]
  have h₀ : θ.comp (chartMap M hle R₀) = chartMap M hle R₁ := by
    ext a; simp [θ, chartMap_apply]
  have hrZ : Z.IsRapoport := by
    have hZ' := hZ
    rw [← h₀, RuleDescend.spMap_comp] at hZ'
    obtain ⟨ψ, hψ, -⟩ := hZ'.cancel hX'
    exact hψ.isRapoport _ hr'
  have e₁ := val_eq_of_factor r₁ _ ρ₁ _ h₁ hY₁ hZ trivial trivial hδ₁ hδZ
  have e₀ : (r₀.extend R₁).val _ Z hrZ δZ = θ (r₀.val _ X' hr' δ') := by
    letI : Algebra R₀ (R₁ ⊗[ℤ] Γ(M, W')) :=
      ((algebraMap R₁ (R₁ ⊗[ℤ] Γ(M, W'))).comp (algebraMap R₀ R₁)).toAlgebra
    let θ' : R₀ ⊗[ℤ] Γ(M, W') →ₐ[R₀] R₁ ⊗[ℤ] Γ(M, W') := { θ with commutes' := fun x ↦ rfl }
    exact val_eq_of_factor r₀ _ θ' _ h₀ hX' hZ hr' hrZ hδ' hδZ
  have l₁ : ∀ x, LinearMap.lTensor R₁ (resL M hle) x = ρ₁ x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rfl
  have l₀ : ∀ x, LinearMap.rTensor Γ(M, W') (coefL R₀ R₁) x = θ x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rfl
  rw [l₀, l₁, ← e₁, ← e₀, hr _ Z hrZ δZ]

theorem exists_isChartFun : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
  (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) →
  ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
    Y.IsPullBy U hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M, W), IsChartFun r₀ Y δY h := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ R₁ _ _ _ hinj k r₀ r₁ hr W hW Y φY hY δY
  obtain ⟨-, -, hflat, hV, hnorm, hcod⟩ := hDP
  obtain ⟨Y₁, φ₁, hY₁⟩ := Y.exists_isPullBy (spMap (chartMap M (le_rfl : W ≤ W) R₁))
  obtain ⟨δ₁, hδ₁⟩ := (hY₁.existsUnique_detGen _ δY).exists
  let q := (LinearMap.range (coefL R₀ R₁)).mkQ
  have hex : Function.Exact (coefL R₀ R₁) q := LinearMap.exact_iff.2 (Submodule.ker_mkQ _)
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hzero : LinearMap.rTensor Γ(M, W) q (r₁.val _ Y₁ trivial δ₁) = 0 := by
    rw [← (TensorProduct.comm ℤ _ _).map_eq_zero_iff]
    refine rTensor_eq_zero_of_restrict_affine_inf N M s V hflat hnorm hcod W hW _ _ fun W' hW' hle ↦ ?_
    obtain ⟨X', φ', hX'⟩ := Y.exists_isPullBy (spMap (chartMap M (hle.trans inf_le_left) R₀))
    obtain ⟨δ', hδ'⟩ := (hX'.existsUnique_detGen _ δY).exists
    have e := rTensor_val_eq r₀ r₁ hr _ δY hY₁ hδ₁ (isRapoport_chart hV hW hW' hle R₀ hY hX') hX' hδ'
    have hc : ∀ x : R₁ ⊗[ℤ] Γ(M, W), LinearMap.rTensor _ (resL M (hle.trans inf_le_left))
        (TensorProduct.comm ℤ _ _ (LinearMap.rTensor Γ(M, W) q x)) = TensorProduct.comm ℤ _ _
          (LinearMap.rTensor Γ(M, W') q (LinearMap.lTensor R₁ (resL M (hle.trans inf_le_left)) x)) := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a => rfl
    refine (hc _).trans ?_
    rw [← e, (rTensor_exact Γ(M, W') hex hq).apply_apply_eq_zero, map_zero]
  obtain ⟨h, hh⟩ := (rTensor_exact Γ(M, W) hex hq _).1 hzero
  refine ⟨h, isChartFun_of_restrictsToVal r₀ hV hW hY δY h fun W' hW' hle X' φ' hr' δ' hX' hδ' ↦ ?_⟩
  haveI := (GlobalTheory.flat_and_isUnit_sections_of_flat_over_away N M s hflat W' hW').1
  refine Module.Flat.rTensor_preserves_injective_linearMap (M := Γ(M, W')) (coefL R₀ R₁) hinj ?_
  rw [rTensor_val_eq r₀ r₁ hr _ δY hY₁ hδ₁ hr' hX' hδ', ← hh, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

end GlobalTheory.RealMult.ChartFun
end
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem isModelVal_of_isRapoport : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R : Type) [CommRing R] [Algebra R₀ R]
  (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen), IsModelVal r₀ U X δ (r₀.val R X hX δ) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R _ _ X hX δ R' _ _ σ X' φ' δ' hX' hδ' W hW Y φY hY δY h hh ψ χ hψ δY' u hδY' hu
  have hX'R : X'.IsRapoport := hX'.isRapoport (σ : R →+* R') hX
  have e1 := hh R' ψ X' χ hX'R δY' hψ hδY'
  have e2 := r₀.homog R' X' hX'R δ' δY' u hu
  have e3 := r₀.baseChange R R' σ X hX X' hX'R φ' δ δ' hX' hδ'
  rw [← e3, ← e2, e1]

theorem exists_levObj_rule_eq_of_extend : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ),
  3 ≤ N → ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) →
  ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∃ r : Rule (levObj 𝔠 N) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ := by
  intro hDP F _ _ _ 𝔠 N hN R₀ R₁ _ _ _ hinj k r₀ r₁ H
  obtain ⟨M, s, U, α, V, hM⟩ := exists_isDPModel hDP F 𝔠 N hN
  have hS1 : ∀ (N' : ℕ) (M' : Scheme.{0}) (s' : M' ⟶ Sp (Localization.Away (N' : ℤ))) (U' : Obj F 𝔠 M')
      (α' : U'.Level N') (V' : M'.Opens), 3 ≤ N' → IsDPModel N' s' U' α' V' → (∀ (W : M'.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M', W))) (φY : Y.A.left ⟶ U'.A.left),
    Y.IsPullBy U' hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M', W), IsChartFun r₀ Y δY h) :=
    fun N' M' s' U' α' V' _ hM' ↦ GlobalTheory.RealMult.ChartFun.exists_isChartFun F 𝔠 N' M' s' U' α' V' hM' R₀ R₁ hinj k r₀ r₁ H
  have key := GlobalTheory.RealMult.ModelValGlue.existsUnique_isModelVal F 𝔠 N M s U α V hM R₀ k r₀ (hS1 N M s U α V hN hM)
    (GlobalTheory.RealMult.ChartIndep.presVal_indep hDP F 𝔠 N hN M s U α V hM R₀ k r₀ hS1)
  refine ⟨{ val := fun R _ _ X hX δ ↦ (key R X hX δ).exists.choose
            homog := fun R _ _ X hX δ δ' c hc ↦ (key R X hX δ).unique
              (GlobalTheory.RealMult.isModelVal_homog F 𝔠 R₀ k r₀ M U R X δ δ' c _ hc (key R X hX δ').exists.choose_spec)
              (key R X hX δ).exists.choose_spec
            baseChange := fun R R' _ _ _ _ σ X hX X' hX' φ δ δ' hφ hδ ↦ (key R' X' hX' δ').unique
              (key R' X' hX' δ').exists.choose_spec
              (GlobalTheory.RealMult.isModelVal_baseChange F 𝔠 R₀ k r₀ M U R R' σ X X' φ δ δ' _ hφ hδ (key R X hX δ).exists.choose_spec) }, ?_⟩
  intro R _ _ X h hX δ
  exact (key R X h δ).unique (key R X h δ).exists.choose_spec (isModelVal_of_isRapoport F 𝔠 R₀ k r₀ M U R X hX δ)

end GlobalTheory.RealMult
end
end
