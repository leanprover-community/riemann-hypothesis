import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreeOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverWithLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevObjRuleEqOfExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.GlueTwo

theorem existsUnique_of_coprime {R W : Type} [CommRing R] [CommRing W] [Algebra R W] (a b : R) (hab : IsCoprime a b)
    [IsLocalization.Away (a * b) W] (f₁ : Localization.Away a →+* W) (f₂ : Localization.Away b →+* W)
    (hf₁ : f₁.comp (algebraMap R _) = algebraMap R W) (hf₂ : f₂.comp (algebraMap R _) = algebraMap R W)
    (x₁ : Localization.Away a) (x₂ : Localization.Away b) (h : f₁ x₁ = f₂ x₂) :
    ∃! x : R, algebraMap R (Localization.Away a) x = x₁ ∧ algebraMap R (Localization.Away b) x = x₂ := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj a x₁
    obtain ⟨m, d, hd⟩ := IsLocalization.Away.surj b x₂
    have e1 : f₁ x₁ * algebraMap R W a ^ n = algebraMap R W c := by
      have := congrArg f₁ hc
      rwa [map_mul, map_pow, ← RingHom.comp_apply f₁, ← RingHom.comp_apply f₁, hf₁] at this
    have e2 : f₂ x₂ * algebraMap R W b ^ m = algebraMap R W d := by
      have := congrArg f₂ hd
      rwa [map_mul, map_pow, ← RingHom.comp_apply f₂, ← RingHom.comp_apply f₂, hf₂] at this
    have key : algebraMap R W (c * b ^ m) = algebraMap R W (d * a ^ n) := by
      rw [map_mul, map_mul, ← e1, ← e2, h, map_pow, map_pow]
      ring
    obtain ⟨l, hl⟩ := IsLocalization.Away.exists_of_eq (a * b) key
    obtain ⟨u, v, huv⟩ := hab.pow (m := n + l) (n := m + l)
    have hl' : (c * a ^ l) * b ^ (m + l) = (d * b ^ l) * a ^ (n + l) := by
      linear_combination hl
    have hx₁ : (u * (c * a ^ l) + v * (d * b ^ l)) * a ^ (n + l) = c * a ^ l := by
      linear_combination (c * a ^ l) * huv - v * hl'
    have hx₂ : (u * (c * a ^ l) + v * (d * b ^ l)) * b ^ (m + l) = d * b ^ l := by
      linear_combination (d * b ^ l) * huv + u * hl'
    refine ⟨u * (c * a ^ l) + v * (d * b ^ l), ?_, ?_⟩
    · have hu : IsUnit (algebraMap R (Localization.Away a) (a ^ (n + l))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit a).pow _
      rw [← hu.mul_left_inj, ← map_mul, hx₁, pow_add, map_mul, map_mul, map_pow, map_pow, ← _root_.mul_assoc, hc]
    · have hu : IsUnit (algebraMap R (Localization.Away b) (b ^ (m + l))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit b).pow _
      rw [← hu.mul_left_inj, ← map_mul, hx₂, pow_add, map_mul, map_mul, map_pow, map_pow, ← _root_.mul_assoc, hd]
  · rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq a (hx₁.trans hy₁.symm)
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq b (hx₂.trans hy₂.symm)
    obtain ⟨u, v, huv⟩ := hab.pow (m := n) (n := m)
    linear_combination u * hn + v * hm - (x - y) * huv

theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id_two (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem dualMapR_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR]

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem isPullBy_comp_two {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R')
    (τ : R' →+* R'') (ρ : R →+* R'') (hρ : τ.comp σ = ρ) {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) : X''.IsPullBy X (spMap ρ) (ψ ≫ φ) := by
  subst hρ
  rw [spMap_comp_two]
  exact h'.comp h

theorem detCorr_comp_two {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R')
    (τ : R' →+* R'') (ρ : R →+* R'') (hρ : τ.comp σ = ρ) {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) {δ : X.DetOmega} {δ' : X'.DetOmega}
    {δ'' : X''.DetOmega} (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ ψ δ' δ'') :
    Obj.DetCorr ρ (ψ ≫ φ) δ δ'' := by
  have hc := isPullBy_comp_two σ τ ρ hρ h h'
  subst hρ
  intro v v'' hv
  letI : Algebra R R' := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R := R) (R' := R') h
  letI : Algebra R' R'' := τ.toAlgebra
  obtain ⟨e', he', -⟩ := Obj.exists_lieEquiv (R := R') (R' := R'') h'
  letI : Algebra R R'' := (τ.comp σ).toAlgebra
  obtain ⟨e'', he'', -⟩ := Obj.exists_lieEquiv (R := R) (R' := R'') hc
  have h1 : ∀ i, Obj.LieCorr σ φ (v i) (e (1 ⊗ₜ v i)) := fun i => (he _ _).2 rfl
  have h2 : ∀ i, Obj.LieCorr τ ψ (e (1 ⊗ₜ v i)) (e' (1 ⊗ₜ e (1 ⊗ₜ v i))) := fun i => (he' _ _).2 rfl
  have h3 : ∀ i, Obj.LieCorr (τ.comp σ) (ψ ≫ φ) (v i) (e' (1 ⊗ₜ e (1 ⊗ₜ v i))) := by
    intro i
    unfold Obj.LieCorr at h1 h2 ⊢
    rw [← Category.assoc, h2 i, Category.assoc, h1 i, dualMapR_comp_two, spMap_comp_two, Category.assoc]
  have h4 : v'' = fun i => e' (1 ⊗ₜ e (1 ⊗ₜ v i)) :=
    funext fun i => ((he'' _ _).1 (hv i)).trans ((he'' _ _).1 (h3 i)).symm
  rw [h4, hd' _ _ h2, hd v _ h1]
  rfl

theorem val_eq_of_isPullBy_two {Q : ObjClass 𝔠} {R₀ : Type} [CommRing R₀] {k : ℕ} (u : Rule Q R₀ k)
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra R₀ R'] (ρ : R →+* R') {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {Y₁ Y₂ : Obj F 𝔠 (Sp R')} (hQ₁ : Q R' Y₁) (hQ₂ : Q R' Y₂) {φ₁ : Y₁.A.left ⟶ X.A.left}
    {φ₂ : Y₂.A.left ⟶ X.A.left} (h₁ : Y₁.IsPullBy X (spMap ρ) φ₁) (h₂ : Y₂.IsPullBy X (spMap ρ) φ₂)
    {δ₁ : Y₁.DetGen} {δ₂ : Y₂.DetGen} (hd₁ : Obj.DetCorr ρ φ₁ δ.1 δ₁.1) (hd₂ : Obj.DetCorr ρ φ₂ δ.1 δ₂.1) :
    u.val R' Y₁ hQ₁ δ₁ = u.val R' Y₂ hQ₂ δ₂ := by
  have h₂' : Y₂.IsPullBy X (spMap (RingHom.id R') ≫ spMap ρ) φ₂ := by
    rwa [spMap_id_two, Category.id_comp]
  obtain ⟨ψ, hψ, hψφ⟩ := Obj.IsPullBy.cancel h₂' h₁
  obtain ⟨δ', hδ', -⟩ := hψ.existsUnique_detGen (RingHom.id R') δ₁
  have hc := detCorr_comp_two ρ (RingHom.id R') ρ (RingHom.id_comp ρ) h₁ hψ hd₁ hδ'
  rw [hψφ] at hc
  obtain rfl : δ' = δ₂ := (h₂.existsUnique_detGen ρ δ).unique hc hd₂
  exact (u.baseChange R' R' (AlgHom.id R₀ R') Y₁ hQ₁ Y₂ hQ₂ ψ δ₁ δ' hψ hδ').symm

theorem isUnit_natCast_away_two (R : Type) [CommRing R] (n : ℕ) :
    IsUnit ((n : ℕ) : Localization.Away ((n : ℕ) : R)) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ((n : ℕ) : R)) ((n : ℕ) : R)

theorem map_val_two {R₀ : Type} [CommRing R₀] {k n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R W' : Type} [CommRing R]
    [Algebra R₀ R] [CommRing W'] [Algebra R₀ W'] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (Y₀ : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R)))) (φ₀ : Y₀.A.left ⟶ X.A.left)
    (h₀ : Y₀.IsPullBy X (spMap (algebraMap R _)) φ₀) (δ₀ : Y₀.DetGen)
    (hd₀ : Obj.DetCorr (algebraMap R _) φ₀ δ.1 δ₀.1) (g : Localization.Away ((n : ℕ) : R) →ₐ[R₀] W')
    (ρ : R →+* W') (hρ : (g : Localization.Away ((n : ℕ) : R) →+* W').comp (algebraMap R _) = ρ)
    (Z : Obj F 𝔠 (Sp W')) (ψ : Z.A.left ⟶ X.A.left) (hZ : Z.IsPullBy X (spMap ρ) ψ) (δZ : Z.DetGen)
    (hdZ : Obj.DetCorr ρ ψ δ.1 δZ.1) (hu : IsUnit ((n : ℕ) : W')) :
    g (u.val _ Y₀ (isUnit_natCast_away_two R n) δ₀) = u.val W' Z hu δZ := by
  obtain ⟨Z', χ, hZ'⟩ := Obj.exists_isPullBy Y₀ (spMap (g : Localization.Away ((n : ℕ) : R) →+* W'))
  obtain ⟨δZ', hdZ', -⟩ := hZ'.existsUnique_detGen _ δ₀
  rw [← u.baseChange _ W' g Y₀ (isUnit_natCast_away_two R n) Z' hu χ δ₀ δZ' hZ' hdZ']
  exact val_eq_of_isPullBy_two u ρ hu hu (isPullBy_comp_two _ _ ρ hρ h₀ hZ') hZ
    (detCorr_comp_two _ _ ρ hρ h₀ hZ' hd₀ hdZ') hdZ

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

def GoodAt {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    (δ : X.DetGen) (x : R) : Prop :=
  ∀ (Y : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R)))) (φ : Y.A.left ⟶ X.A.left),
    Y.IsPullBy X (spMap (algebraMap R _)) φ → ∀ δY : Y.DetGen, Obj.DetCorr (algebraMap R _) φ δ.1 δY.1 →
      algebraMap R _ x = u.val _ Y (isUnit_natCast_away_two R n) δY

theorem exists_pull_two {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) :
    ∃ (Y : Obj F 𝔠 (Sp S)) (φ : Y.A.left ⟶ X.A.left) (_ : Y.IsPullBy X (spMap ρ) φ) (δY : Y.DetGen),
      Obj.DetCorr ρ φ δ.1 δY.1 := by
  obtain ⟨Y, φ, h⟩ := Obj.exists_isPullBy X (spMap ρ)
  obtain ⟨δY, hd, -⟩ := h.existsUnique_detGen ρ δ
  exact ⟨Y, φ, h, δY, hd⟩

theorem goodAt_of_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (Y₀ : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R))))
    (φ₀ : Y₀.A.left ⟶ X.A.left) (h₀ : Y₀.IsPullBy X (spMap (algebraMap R _)) φ₀) (δ₀ : Y₀.DetGen)
    (hd₀ : Obj.DetCorr (algebraMap R _) φ₀ δ.1 δ₀.1) (x : R)
    (hx : algebraMap R _ x = u.val _ Y₀ (isUnit_natCast_away_two R n) δ₀) : GoodAt u X δ x := by
  intro Y φ h δY hd
  rw [hx]
  exact map_val_two u X δ Y₀ φ₀ h₀ δ₀ hd₀ (AlgHom.id R₀ _) (algebraMap R _) rfl Y φ h δY hd _

theorem algebraMap_eq_of_goodAt_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) {x y : R} (hx : GoodAt u X δ x) (hy : GoodAt u X δ y) :
    algebraMap R (Localization.Away ((n : ℕ) : R)) x = algebraMap R _ y := by
  obtain ⟨Y, φ, h, δY, hd⟩ := exists_pull_two (algebraMap R (Localization.Away ((n : ℕ) : R))) X δ
  rw [hx Y φ h δY hd, hy Y φ h δY hd]

theorem isUnit_of_detGen_two {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c : R)
    (hc : δ'.1 = c • δ.1) : IsUnit c := by
  haveI := Obj.invertible_detOmega X
  have hmem : δ.1 ∈ Submodule.span R {δ'.1} := by rw [δ'.2]; trivial
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hmem
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton R X.DetOmega δ.1) := by
    intro m
    have hm : m ∈ Submodule.span R {δ.1} := by rw [δ.2]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
    exact ⟨a, ha⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  have h1 : d * c = 1 := hinj (by
    simp only [LinearMap.toSpanSingleton_apply, mul_smul, ← hc, hd, one_smul])
  exact ⟨⟨c, d, by rw [mul_comm]; exact h1, h1⟩, rfl⟩

theorem goodAt_homog_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c : R) (hc : δ'.1 = c • δ.1) {x : R} (hx : GoodAt u X δ' x) :
    GoodAt u X δ (c ^ k * x) := by
  intro Y φ h δY hd
  have hcu := isUnit_of_detGen_two X δ δ' c hc
  obtain ⟨δY', hdY', -⟩ := h.existsUnique_detGen _ δ'
  have e : δY'.1 = algebraMap R (Localization.Away ((n : ℕ) : R)) c • δY.1 := by
    let g₁ : Y.DetGen := Subtype.mk (algebraMap R (Localization.Away ((n : ℕ) : R)) c • δY.1) (by
      rw [Submodule.span_singleton_smul_eq (hcu.map _)]; exact δY.2)
    have hγ : Obj.DetCorr (algebraMap R _) φ δ'.1 g₁.1 := by
      intro v v' hv
      simp [g₁, hd v v' hv, hc]
    exact congrArg Subtype.val ((h.existsUnique_detGen _ δ').unique hdY' hγ)
  rw [map_mul, map_pow, hx Y φ h δY' hdY']
  exact u.homog _ Y _ δY δY' _ e

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem goodAt_baseChange_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R R' : Type} [CommRing R] [Algebra R₀ R]
    [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X : Obj F 𝔠 (Sp R)) (X' : Obj F 𝔠 (Sp R'))
    (φ' : X'.A.left ⟶ X.A.left) (h' : X'.IsPullBy X (spMap (σ : R →+* R')) φ') (δ : X.DetGen) (δ' : X'.DetGen)
    (hd' : Obj.DetCorr (σ : R →+* R') φ' δ.1 δ'.1) {x : R} (hx : GoodAt u X δ x) : GoodAt u X' δ' (σ x) := by
  intro Y ψ h δY hd
  obtain ⟨Y₀, φ₀, h₀, δ₀, hd₀⟩ := exists_pull_two (algebraMap R (Localization.Away ((n : ℕ) : R))) X δ
  have hunit : IsUnit (((IsScalarTower.toAlgHom R₀ R' (Localization.Away ((n : ℕ) : R'))).comp σ) ((n : ℕ) : R)) := by
    simpa using isUnit_natCast_away_two R' n
  let g : Localization.Away ((n : ℕ) : R) →ₐ[R₀] Localization.Away ((n : ℕ) : R') :=
    IsLocalization.Away.liftAlgHom ((n : ℕ) : R) hunit
  have hg : (g : Localization.Away ((n : ℕ) : R) →+* Localization.Away ((n : ℕ) : R')).comp (algebraMap R _) =
      (algebraMap R' (Localization.Away ((n : ℕ) : R'))).comp (σ : R →+* R') :=
    RingHom.ext fun a => by simp [g]
  have key := map_val_two u X δ Y₀ φ₀ h₀ δ₀ hd₀ g _ hg Y (ψ ≫ φ')
    (isPullBy_comp_two _ _ _ rfl h' h) δY (detCorr_comp_two _ _ _ rfl h' h hd' hd) (isUnit_natCast_away_two R' n)
  rw [← key, ← hx Y₀ φ₀ h₀ δ₀ hd₀]
  simp [g]

theorem goodAt_rap_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) (r₀ : Rule (rapObj 𝔠) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hn : IsUnit ((n : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), u.val R X hn δ = r₀.val R X hX δ)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen) :
    GoodAt u X δ (r₀.val R X hX δ) := by
  intro Y φ h δY hd
  rw [H _ Y _ (h.isRapoport _ hX) δY]
  exact (r₀.baseChange R _ (IsScalarTower.toAlgHom R₀ R _) X hX Y _ φ δ δY h hd).symm

theorem isCoprime_three_two (R : Type) [CommRing R] : IsCoprime ((3 : ℕ) : R) ((2 : ℕ) : R) :=
  ⟨1, -1, by push_cast; ring⟩

theorem existsUnique_glued (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R))
      (h₂ : IsUnit ((2 : ℕ) : R)) (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ)
    (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) :
    ∃! x : R, GoodAt s X δ x ∧ GoodAt t X δ x := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨Y₃, φ₃, h₃, δ₃, hd₃⟩ := exists_pull_two (algebraMap R (Localization.Away ((3 : ℕ) : R))) X δ
    obtain ⟨Y₂, φ₂, h₂, δ₂, hd₂⟩ := exists_pull_two (algebraMap R (Localization.Away ((2 : ℕ) : R))) X δ
    let W := Localization.Away (((3 : ℕ) : R) * ((2 : ℕ) : R))
    have u6 : IsUnit (algebraMap R W (((3 : ℕ) : R) * ((2 : ℕ) : R))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at u6
    have u3 : IsUnit ((IsScalarTower.toAlgHom R₀ R W) ((3 : ℕ) : R)) := isUnit_of_mul_isUnit_left u6
    have u2 : IsUnit ((IsScalarTower.toAlgHom R₀ R W) ((2 : ℕ) : R)) := isUnit_of_mul_isUnit_right u6
    let f₃ : Localization.Away ((3 : ℕ) : R) →ₐ[R₀] W := IsLocalization.Away.liftAlgHom ((3 : ℕ) : R) u3
    let f₂ : Localization.Away ((2 : ℕ) : R) →ₐ[R₀] W := IsLocalization.Away.liftAlgHom ((2 : ℕ) : R) u2
    have hf₃ : (f₃ : Localization.Away ((3 : ℕ) : R) →+* W).comp (algebraMap R _) = algebraMap R W :=
      RingHom.ext fun a => by simp [f₃]
    have hf₂ : (f₂ : Localization.Away ((2 : ℕ) : R) →+* W).comp (algebraMap R _) = algebraMap R W :=
      RingHom.ext fun a => by simp [f₂]
    obtain ⟨Z, ψ, hZ, δZ, hdZ⟩ := exists_pull_two (algebraMap R W) X δ
    have w3 : IsUnit ((3 : ℕ) : W) := by rw [← map_natCast (algebraMap R W) 3]; exact u3
    have w2 : IsUnit ((2 : ℕ) : W) := by rw [← map_natCast (algebraMap R W) 2]; exact u2
    have e3 := map_val_two s X δ Y₃ φ₃ h₃ δ₃ hd₃ f₃ _ hf₃ Z ψ hZ δZ hdZ w3
    have e2 := map_val_two t X δ Y₂ φ₂ h₂ δ₂ hd₂ f₂ _ hf₂ Z ψ hZ δZ hdZ w2
    obtain ⟨x, ⟨hx₃, hx₂⟩, -⟩ := existsUnique_of_coprime (W := W) _ _ (isCoprime_three_two R)
      (f₃ : Localization.Away ((3 : ℕ) : R) →+* W) (f₂ : Localization.Away ((2 : ℕ) : R) →+* W) hf₃ hf₂ _ _
      (show f₃ _ = f₂ _ from e3.trans ((H W Z w3 w2 δZ).trans e2.symm))
    exact ⟨x, goodAt_of_two s X δ Y₃ φ₃ h₃ δ₃ hd₃ x hx₃, goodAt_of_two t X δ Y₂ φ₂ h₂ δ₂ hd₂ x hx₂⟩
  · rintro x y ⟨hx₃, hx₂⟩ ⟨hy₃, hy₂⟩
    let W := Localization.Away (((3 : ℕ) : R) * ((2 : ℕ) : R))
    have u6 : IsUnit (algebraMap R W (((3 : ℕ) : R) * ((2 : ℕ) : R))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at u6
    let f₃ : Localization.Away ((3 : ℕ) : R) →+* W :=
      IsLocalization.Away.lift ((3 : ℕ) : R) (isUnit_of_mul_isUnit_left u6)
    let f₂ : Localization.Away ((2 : ℕ) : R) →+* W :=
      IsLocalization.Away.lift ((2 : ℕ) : R) (isUnit_of_mul_isUnit_right u6)
    obtain ⟨z, -, hz⟩ := existsUnique_of_coprime (W := W) _ _ (isCoprime_three_two R) f₃ f₂
      (IsLocalization.Away.lift_comp _ _) (IsLocalization.Away.lift_comp _ _)
      (algebraMap R _ x) (algebraMap R _ x) (by simp [f₃, f₂])
    exact (hz x ⟨rfl, rfl⟩).trans (hz y ⟨(algebraMap_eq_of_goodAt_two s X δ hx₃ hy₃).symm,
      (algebraMap_eq_of_goodAt_two t X δ hx₂ hy₂).symm⟩).symm

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

def glueRule (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R))
      (h₂ : IsUnit ((2 : ℕ) : R)) (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ) :
    Rule (trivialObjectCondition 𝔠) R₀ k where
  val R _ _ X _ δ := (existsUnique_glued s t H R X δ).exists.choose
  homog R _ _ X _ δ δ' c hc := by
    have h' := (existsUnique_glued s t H R X δ').exists.choose_spec
    exact ((existsUnique_glued s t H R X δ).unique (existsUnique_glued s t H R X δ).exists.choose_spec
      ⟨goodAt_homog_two s X δ δ' c hc h'.1, goodAt_homog_two t X δ δ' c hc h'.2⟩).symm
  baseChange R R' _ _ _ _ σ X _ X' _ φ δ δ' h hd := by
    have h₀ := (existsUnique_glued s t H R X δ).exists.choose_spec
    exact (existsUnique_glued s t H R' X' δ').unique (existsUnique_glued s t H R' X' δ').exists.choose_spec
      ⟨goodAt_baseChange_two s σ X X' φ h δ δ' hd h₀.1, goodAt_baseChange_two t σ X X' φ h δ δ' hd h₀.2⟩

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult

theorem exists_rule_allObj_of_three_two :
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
      (r₀ : Rule (rapObj 𝔠) R₀ k) (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k),
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R)) (h₂ : IsUnit ((2 : ℕ) : R))
        (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ) →
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R)) (hX : X.IsRapoport)
        (δ : X.DetGen), s.val R X h₃ δ = r₀.val R X hX δ) →
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₂ : IsUnit ((2 : ℕ) : R)) (hX : X.IsRapoport)
        (δ : X.DetGen), t.val R X h₂ δ = r₀.val R X hX δ) →
      ∃ r : Rule (trivialObjectCondition 𝔠) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport)
        (δ : X.DetGen), r.val R X trivial δ = r₀.val R X hX δ := by
  intro F _ _ 𝔠 R₀ _ k r₀ s t H H₃ H₂
  refine ⟨GlueTwo.glueRule s t H, fun R _ _ X hX δ => ?_⟩
  exact (GlueTwo.existsUnique_glued s t H R X δ).unique
    (GlueTwo.existsUnique_glued s t H R X δ).exists.choose_spec
    ⟨GlueTwo.goodAt_rap_two s r₀ H₃ X hX δ, GlueTwo.goodAt_rap_two t r₀ H₂ X hX δ⟩

end GlobalTheory.RealMult
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_level_twelve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), Nonempty (X.Level 12) →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro F _ _ _ 𝔠 R₀ _ k s t H
  apply Rule.ext
  funext R _ _ X h δ
  have h2 : IsUnit ((2 : ℕ) : R) :=
    isUnit_of_dvd_unit ⟨((3 : ℕ) : R), by rw [← Nat.cast_mul]⟩ h
  have h12 : IsUnit ((12 : ℕ) : R) := by
    have : ((12 : ℕ) : R) = ((6 : ℕ) : R) * ((2 : ℕ) : R) := by rw [← Nat.cast_mul]
    rw [this]; exact h.mul h2
  obtain ⟨R', _, σ, X', φ, hff, hpull, hlev⟩ := GlobalTheory.RealMult.exists_faithfullyFlat_level F 𝔠 12 (by norm_num) R h12 X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σa : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  have h' : IsUnit ((6 : ℕ) : R') := by
    have := h.map σ
    rwa [map_natCast] at this
  obtain ⟨δ', hδ', -⟩ := hpull.existsUnique_detGen σ δ
  have e1 := s.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e2 := t.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e3 := H R' X' h' hlev δ'
  apply hff.injective
  change σa (s.val R X h δ) = σa (t.val R X h δ)
  rw [← e1, ← e2, e3]

end GlobalTheory.RealMult
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_rule_ext_of_level_twelve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), Nonempty (X.Level 12) →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  atlas_forward_decl GlobalTheory.RealMult.Rule.eq_of_eq_on_level_twelve
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_affine_nbhd_detGen_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_affine_determinant_generator : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
    ∃ (W : M.Opens) (hW : IsAffineOpen W), y ∈ W ∧ ∃ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ ∧ Nonempty Y.DetGen := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.exists_affine_nbhd_detGen_basicOpen
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_factor_basicOpen_affineOpen :
    ∀ (M : Scheme.{0}) (W : M.Opens) (hW : IsAffineOpen W) (R : Type) [CommRing R] (b : Sp R ⟶ M) (p : PrimeSpectrum R),
    b p ∈ W → ∃ (f : R) (g : Γ(M, W) →+* Localization.Away f), f ∉ p.asIdeal ∧
      spMap g ≫ hW.fromSpec = spMap (algebraMap R (Localization.Away f)) ≫ b := by
  intro M W hW R _ b p hp
  have hopen : IsOpen (X := PrimeSpectrum R) (b ⁻¹ᵁ W).carrier := (b ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := p) (show p ∈ (b ⁻¹ᵁ W).carrier from hp) hopen
  have H : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hx : (spMap (algebraMap R (Localization.Away f))) x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨x, rfl⟩
    exact hsub hx
  let h := IsOpenImmersion.lift hW.fromSpec _ H
  refine ⟨f, (Spec.preimage h).hom, hpf, ?_⟩
  have e : spMap (Spec.preimage h).hom = h := by
    simp [spMap, Spec.map_preimage]
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_local_factorization : ∀ (M : Scheme.{0}) (W : M.Opens) (hW : IsAffineOpen W) (R : Type) [CommRing R] (b : Sp R ⟶ M) (p : PrimeSpectrum R),
    b p ∈ W → ∃ (f : R) (g : Γ(M, W) →+* Localization.Away f), f ∉ p.asIdeal ∧
      spMap g ≫ hW.fromSpec = spMap (algebraMap R (Localization.Away f)) ≫ b := by
  atlas_forward_decl GlobalTheory.affine_factor_basicOpen_affineOpen
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_extScalars : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  intro F _ _ 𝔠 R₀ _ k s t A _ Y ⟨δ₀⟩ hst h6 B _ _ σ Y' φ hY' h δ
  let inr : A →ₐ[ℤ] R₀ ⊗[ℤ] A := Algebra.TensorProduct.includeRight
  let τ : R₀ ⊗[ℤ] A →ₐ[R₀] B :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ B) σ.toIntAlgHom fun _ _ ↦ Commute.all _ _
  have hτinr : (τ : R₀ ⊗[ℤ] A →+* B).comp inr.toRingHom = σ := by
    ext a
    simp [τ, inr]
  have hsp : spMap σ = spMap (τ : R₀ ⊗[ℤ] A →+* B) ≫ spMap inr.toRingHom := by
    rw [← hτinr]
    simp [spMap, Spec.map_comp]
  have h6C : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A) := by
    have := h6.map inr
    rwa [map_natCast] at this
  obtain ⟨YC, ψ, hYC⟩ := Obj.exists_isPullBy Y (spMap inr.toRingHom)
  obtain ⟨ψ', hψ', -⟩ := Obj.IsPullBy.cancel (hsp ▸ hY') hYC
  obtain ⟨δC, hδC, -⟩ := hYC.existsUnique_detGen inr.toRingHom δ₀
  obtain ⟨δB, hδB, -⟩ := hψ'.existsUnique_detGen (τ : R₀ ⊗[ℤ] A →+* B) δC
  have e1 := s.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e2 := t.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e3 := hst YC ψ hYC h6C δC
  have hB : s.val B Y' h δB = t.val B Y' h δB := by rw [e1, e2, e3]
  obtain ⟨c, hc⟩ : ∃ c : B, δB.1 = c • δ.1 := by
    have : δB.1 ∈ Submodule.span B {δ.1} := by rw [δ.2]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨c, hc.symm⟩
  rw [← s.homog B Y' h δ δB c hc, ← t.homog B Y' h δ δB c hc, hB]

end GlobalTheory.RealMult
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_rule_base_change : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  atlas_forward_decl GlobalTheory.RealMult.Rule.eq_of_eq_extScalars
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem rule_eq_on_extend_chart : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  intro F _ _ 𝔠 R₀ _ k s t N M sM U V hflat hnorm hcodim W hW hagree Y φ hY YC ψ hYC h δ
  set d := s.val _ YC h δ - t.val _ YC h δ with hd
  suffices hd0 : TensorProduct.comm ℤ R₀ Γ(M, W) d = 0 by
    have : d = 0 := by simpa using congrArg (TensorProduct.comm ℤ R₀ Γ(M, W)).symm hd0
    exact sub_eq_zero.mp this
  refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcodim W hW R₀ _ ?_
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let τ' : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
    Algebra.TensorProduct.map (AlgHom.id R₀ R₀) ρ.toIntAlgHom
  have hswap : ∀ x : R₀ ⊗[ℤ] Γ(M, W), LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap
      (TensorProduct.comm ℤ R₀ Γ(M, W) x) = TensorProduct.comm ℤ R₀ Γ(M, W') (τ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [τ']
    | add x y hx hy => simp only [map_add, hx, hy]
  change LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap _ = 0
  rw [hswap]
  suffices hτ : τ' d = 0 by rw [hτ, map_zero]

  let incR : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W) :=
    (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom
  let incR' : Γ(M, W') →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom
  obtain ⟨Y', φ', hY'⟩ := Obj.exists_isPullBy U hW'.fromSpec
  obtain ⟨YC', ψ', hYC'⟩ := Obj.exists_isPullBy YC (spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')))
  have hcomm : (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')).comp incR = incR'.comp ρ := by
    ext x; simp [τ', incR, incR']
  have hbase : spMap (τ' : R₀ ⊗[ℤ] Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W')) ≫ spMap incR ≫ hW.fromSpec =
      spMap incR' ≫ hW'.fromSpec := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    congr 1
    exact hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op
  have hall := hYC'.comp (hYC.comp hY)
  rw [hbase] at hall
  obtain ⟨ψ'', hψ'', -⟩ := hall.cancel hY'
  obtain ⟨δ', hδ', -⟩ := hYC'.existsUnique_detGen _ δ
  have h' : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W')) := map_natCast τ' 6 ▸ h.map τ'
  have heq := hagree W' hW' hle Y' φ' hY' (R₀ ⊗[ℤ] Γ(M, W')) incR' YC' ψ'' hψ'' h' δ'
  have hs := s.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  have ht := t.baseChange _ _ τ' YC h YC' h' ψ' δ δ' hYC' hδ'
  rw [hd, map_sub, ← hs, ← ht, heq, sub_self]

end GlobalTheory.RealMult
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_normal_fibers_open_extension : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  atlas_forward_decl GlobalTheory.RealMult.rule_eq_on_extend_chart
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem eq_zero_of_forall_away {R : Type} [CommRing R] (d : R)
    (h : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧ algebraMap R (Localization.Away f) d = 0) : d = 0 := by
  set I : Submodule R R := (Submodule.span R {d}).annihilator
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton d 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨f, hf, hfd⟩ := h ⟨m, hm.isPrime⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hfd
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hfd
    have : f ^ n ∈ I := (Submodule.mem_annihilator_span_singleton d _).2 (by simpa [smul_eq_mul] using hn)
    exact (hf (hm.isPrime.mem_of_pow_mem n (hle this))).elim

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem Rule.agreeOn_of_isRapoport {R₀ : Type} [CommRing R₀] {k : ℕ} (s t : Rule (unitObj 𝔠 6) R₀ k)
    (hst : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ)
    {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (hY : Y.IsRapoport) : s.AgreeOn t Y :=
  fun B _ _ σ Y' _ hY' h δ ↦ hst B Y' h (hY'.isRapoport σ hY) δ

theorem isRapoport_of_le_rapLocus {M : Scheme.{0}} (U : Obj F 𝔠 M) (V : M.Opens) (hV : (V : Set M) = U.rapLocus)
    (W : M.Opens) (hW : IsAffineOpen W) (hle : W ≤ V) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left)
    (hY : Y.IsPullBy U hW.fromSpec φ) : Y.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun x K _ t hx Z ψ hZ ↦ ?_
  have hmem : hW.fromSpec x ∈ U.rapLocus := by
    rw [← hV]; apply hle; show hW.fromSpec x ∈ (W : Set M); rw [← hW.range_fromSpec]; exact ⟨x, rfl⟩
  refine hmem K (t ≫ hW.fromSpec) ?_ Z (ψ ≫ φ) (hZ.comp hY)
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

theorem isUnit_six_of_away {M : Scheme.{0}} (sM : M ⟶ Sp (Localization.Away (12 : ℤ))) (W : M.Opens) :
    IsUnit ((6 : ℕ) : Γ(M, W)) := by
  have h12 : IsUnit (algebraMap ℤ (Localization.Away (12 : ℤ)) 12) := IsLocalization.Away.algebraMap_isUnit _
  have h6 : IsUnit ((6 : ℕ) : Localization.Away (12 : ℤ)) := by
    have : algebraMap ℤ (Localization.Away (12 : ℤ)) 12 = ((6 : ℕ) : Localization.Away (12 : ℤ)) * 2 := by
      simp; norm_num
    rw [this] at h12
    exact isUnit_of_mul_isUnit_left h12
  let g : Localization.Away (12 : ℤ) →+* Γ(M, W) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (12 : ℤ)))).inv ≫ sM.appTop ≫
      M.presheaf.map (homOfLE le_top).op).hom
  have := h6.map g
  rwa [map_natCast] at this

end GlobalTheory.RealMult

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_rapoport_unit_six : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
  (R₀ : Type) [CommRing R₀] (k : ℕ) (s t : Rule (unitObj 𝔠 6) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
    ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro hDP F _ _ _ 𝔠 R₀ _ k s t hst
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 12 (by norm_num)
  have hchart : ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ → Nonempty Y.DetGen → s.AgreeOn t Y := by
    intro W hW Y φ hY hgen
    exact GlobalTheory.T.determinant_generator_rule_base_change F 𝔠 R₀ k s t Γ(M, W) Y hgen
      (GlobalTheory.T.flat_normal_fibers_open_extension F 𝔠 R₀ k s t 12 M sM U V hflat hnorm hcod W hW
        (fun W' hW' hle Y' φ' hY' ↦ Rule.agreeOn_of_isRapoport s t hst Y'
          (isRapoport_of_le_rapLocus U V hV W' hW' (hle.trans inf_le_right) Y' φ' hY')) Y φ hY)
      (isUnit_six_of_away sM W)
  apply GlobalTheory.T.modular_rule_ext_of_level_twelve F 𝔠 R₀ k s t
  intro R _ _ X h6 ⟨α⟩ δ
  have h6' : IsUnit (6 : R) := by exact_mod_cast h6
  have h2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left (y := (3 : R)) (by norm_num; exact h6')
  have h12 : IsUnit ((Int.castRingHom R) 12) := by
    have : (Int.castRingHom R) 12 = 6 * 2 := by simp; norm_num
    rw [this]; exact h6'.mul h2
  let τ : Localization.Away (12 : ℤ) →+* R := IsLocalization.Away.lift (12 : ℤ) h12
  obtain ⟨b, -, φ, hφ, -⟩ := (hfine (Sp R) (spMap τ) X α).exists
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_away
  intro p
  obtain ⟨W, hW, hy, Y, ψ, hY, hgen⟩ := GlobalTheory.T.local_affine_determinant_generator F 𝔠 M U (b p)
  obtain ⟨f, g, hp, hg⟩ := GlobalTheory.T.affine_open_local_factorization M W hW R b p hy
  obtain ⟨Xf, φf, hXf⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away f)))
  obtain ⟨δf, hδf, -⟩ := hXf.existsUnique_detGen _ δ
  have hXfU := hXf.comp hφ
  rw [← hg] at hXfU
  obtain ⟨χ, hχ, -⟩ := hXfU.cancel hY
  have h6f : IsUnit ((6 : ℕ) : Localization.Away f) := by
    have := h6.map (algebraMap R (Localization.Away f))
    rwa [map_natCast] at this
  refine ⟨f, hp, ?_⟩
  have e1 := s.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  have e2 := t.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  simp only [IsScalarTower.coe_toAlgHom'] at e1 e2
  rw [map_sub, ← e1, ← e2]
  exact sub_eq_zero.2 (hchart W hW Y ψ hY hgen _ g Xf χ hχ h6f δf)
end GlobalTheory.RealMult
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.RuleDescend

theorem exists_rule_unitObj :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r : Rule (levObj 𝔠 N) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ) →
  ∃ r' : Rule (unitObj 𝔠 N) R₀ k,
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X) (δ : X.DetGen),
      r'.val R X h.1 δ = r.val R X h δ) ∧
    ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((N : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), r'.val R X h δ = r₀.val R X hX δ :=
  exists_rule_unitObj_of_covers (exists_faithfullyFlat_level_of torsion_free_rank_two)

end GlobalTheory.RealMult.RuleDescend
end

section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem exists_rule_allObj_of_extend : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ R₁ : Type) [CommRing R₀]
  [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) → ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k)
  (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∃ r : Rule (trivialObjectCondition 𝔠) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport)
    (δ : X.DetGen), r.val R X trivial δ = r₀.val R X hX δ := by
  intro hDP F _ _ _ 𝔠 R₀ R₁ _ _ _ hinj k r₀ r₁ hyp
  obtain ⟨q3, hq3⟩ := GlobalTheory.RealMult.exists_levObj_rule_eq_of_extend hDP F 𝔠 3 le_rfl R₀ R₁ hinj k r₀ r₁ hyp
  obtain ⟨q4, hq4⟩ := GlobalTheory.RealMult.exists_levObj_rule_eq_of_extend hDP F 𝔠 4 (by norm_num) R₀ R₁ hinj k r₀ r₁ hyp
  obtain ⟨r3, -, hr3⟩ := GlobalTheory.RealMult.RuleDescend.exists_rule_unitObj F 𝔠 3 (by norm_num) R₀ k r₀ q3 hq3
  obtain ⟨r4, -, hr4⟩ := GlobalTheory.RealMult.RuleDescend.exists_rule_unitObj F 𝔠 4 (by norm_num) R₀ k r₀ q4 hq4
  have h42 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 2 R X → unitObj 𝔠 4 R X := by
    intro R _ X h
    change IsUnit ((2 : ℕ) : R) at h
    change IsUnit ((4 : ℕ) : R)
    have : ((4 : ℕ) : R) = ((2 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this]; exact h.mul h
  let t := r4.restrict h42
  have h63 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 6 R X → unitObj 𝔠 3 R X := by
    intro R _ X h
    change IsUnit ((6 : ℕ) : R) at h
    change IsUnit ((3 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this] at h; exact isUnit_of_mul_isUnit_left h
  have h62 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 6 R X → unitObj 𝔠 2 R X := by
    intro R _ X h
    change IsUnit ((6 : ℕ) : R) at h
    change IsUnit ((2 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this] at h; exact isUnit_of_mul_isUnit_right h
  have hov := GlobalTheory.RealMult.Rule.eq_of_eq_on_rapoport_unit_six hDP F 𝔠 R₀ k (r3.restrict h63) (t.restrict h62) (by
    intro R _ _ X h hX δ
    change r3.val R X (h63 R X h) δ = r4.val R X (h42 R X (h62 R X h)) δ
    exact (hr3 R X _ hX δ).trans (hr4 R X _ hX δ).symm)
  refine GlobalTheory.RealMult.exists_rule_allObj_of_three_two F 𝔠 R₀ k r₀ r3 t ?_ (fun R _ _ X h hX δ ↦ hr3 R X h hX δ) (fun R _ _ X h hX δ ↦ hr4 R X _ hX δ)
  intro R _ _ X h₃ h₂ δ
  have h6 : unitObj 𝔠 6 R X := by
    change IsUnit ((6 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this]; exact h₃.mul h₂
  have := congrArg (fun q : Rule (unitObj 𝔠 6) R₀ k ↦ q.val R X h6 δ) hov
  exact this

end GlobalTheory.RealMult
end
