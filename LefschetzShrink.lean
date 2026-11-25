import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

/-!
Standalone test of the RH-Shrink Lefschetz reduction. Run from the repository root:
  lake env lean LefschetzShrink.lean
Requires the original project and its compiled dependencies. The new theorem has
exactly the same statement as the original, with a different name. It does not
invoke the original nonintegral theorem. Uncompiled candidate.
-/

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1
set_option autoImplicit false

namespace RHShrinkTrial

private theorem algTrace_algEquiv {B B' C' : Type} [CommRing B] [CommRing B'] [CommRing C']
    [Algebra B B'] [Algebra B C'] [Module.Finite B B'] [Module.Projective B B']
    [Module.Finite B C'] [Module.Projective B C'] (e : B' ≃ₐ[B] C') (b : B') :
    algTrace B C' (e b) = algTrace B B' b := by
  letI : Algebra B' C' := (e : B' →+* C').toAlgebra
  haveI : IsScalarTower B B' C' := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  haveI : Algebra.IsPushout B B B' C' :=
    ⟨by
      have := IsBaseChange.ofEquiv (R := B) e.toLinearEquiv
      exact this⟩
  exact algTrace_of_isPushout (B := B) (B' := B') (C := B) (C' := C') b

section
variable {k : Type} [CommRing k] {A B Z : Scheme.{0}} {sZ : Z ⟶ Sp k} {sA : A ⟶ Sp k}
  {sB : B ⟶ Sp k}

private theorem secTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    [IsFinite (e ≫ g)] [Etale (e ≫ g)] {U : Z.Opens} (hU : IsAffineOpen U)
    (b : Sec sB (g ⁻¹ᵁ U)) :
    secTrace (f := e ≫ g) sZ sA hU (appSec sB sA e (g ⁻¹ᵁ U) b) =
      secTrace (f := g) sZ sB hU b := by
  letI := secAlg sZ sB g U
  letI := secAlg sZ sA (e ≫ g) U
  haveI := sec_finite (s := sZ) (s' := sB) (f := g) hU
  haveI := sec_etale (s := sZ) (s' := sB) (f := g) hU
  haveI := sec_finite (s := sZ) (s' := sA) (f := e ≫ g) hU
  haveI := sec_etale (s := sZ) (s' := sA) (f := e ≫ g) hU
  haveI := projective_of_etale (Sec sZ U) (Sec sB (g ⁻¹ᵁ U))
  haveI := projective_of_etale (Sec sZ U) (Sec sA ((e ≫ g) ⁻¹ᵁ U))
  have hbij : Function.Bijective (appSec sB sA e (g ⁻¹ᵁ U)) :=
    ConcreteCategory.bijective_of_isIso (e.app (g ⁻¹ᵁ U))
  let E : Sec sB (g ⁻¹ᵁ U) ≃ₐ[Sec sZ U] Sec sA ((e ≫ g) ⁻¹ᵁ U) :=
    AlgEquiv.ofBijective
      { (appSec sB sA e (g ⁻¹ᵁ U)) with
        commutes' := fun u ↦ by
          change (g.app U ≫ e.app (g ⁻¹ᵁ U)).hom u = ((e ≫ g).app U).hom u
          rw [Scheme.Hom.comp_app]
          rfl } hbij
  exact algTrace_algEquiv E b

private theorem omegaTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    [IsFinite (e ≫ g)] [Etale (e ≫ g)] (he : e ≫ sB = sA) (hg : g ≫ sZ = sB)
    (hga : (e ≫ g) ≫ sZ = sA) (j : ℕ) :
    (Scheme.Modules.pushforward g).map (omegaPull he j) ≫
        (Scheme.Modules.pushforwardComp e g).hom.app _ ≫ omegaTrace hga j = omegaTrace hg j := by
  refine omegaTrace_ext hg j _ fun U hU b' x ↦ ?_
  change (omegaTrace hga j).app U ((omegaPull he j).val.app (Opposite.op (g ⁻¹ᵁ U))
    ((toOmega sB j).app (Opposite.op (g ⁻¹ᵁ U)) (b' • formPull hg U j x))) = _
  rw [omegaPull_toOmega, formPull_smul, formPull_formPull hg he hga]
  refine (omegaTrace_toOm_smul_formPull hga j hU (appSec sB sA e (g ⁻¹ᵁ U) b') x).trans ?_
  rw [secTrace_iso e g hU b']

private theorem hodgeTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    (g' : A ⟶ Z) [IsFinite g'] [Etale g'] (hgg : g' = e ≫ g) (he : e ≫ sB = sA)
    (hg : g ≫ sZ = sB) (hga : g' ≫ sZ = sA) (j q : ℕ) (x : hodgeH sB j q) :
    hodgeTrace hga j q (hodgePull he j q x) = hodgeTrace hg j q x := by
  subst hgg
  letI := algΓ sZ; letI := algΓ sA; letI := algΓ sB
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q).surjective x
  have e1 : hodgeTrace hg j q (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q y) =
      cohOn.map k (omegaTrace hg j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hg j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q).symm_apply_apply y)
  let ψ := (Scheme.Modules.pushforward g).map (omegaPull he j) ≫
    (Scheme.Modules.pushforwardComp e g).hom.app (Omega sA j)
  have e2 : hodgePull he j q (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q y) =
      coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q (cohOn.map k ψ ⊤ q y) := by
    refine Eq.trans ?_ (cohOn.pushforwardEquiv_apply k (appTop_algebraMap hga) _ ⊤ q _).symm
    have s2 := cohOn_pull_pull (appTop_algebraMap hg) (appTop_algebraMap he)
      (appTop_algebraMap hga) (𝟙 _) (omegaPull he j) (le_refl (g ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
    rw [cohOn.pull_map, Category.comp_id]
    refine Eq.trans ?_ (s2.trans ?_)
    · rfl
    · rw [Category.id_comp]
      rfl
  rw [e2, e1]
  have e3 : hodgeTrace hga j q
      (coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q (cohOn.map k ψ ⊤ q y)) =
      cohOn.map k (omegaTrace hga j) ⊤ q (cohOn.map k ψ ⊤ q y) :=
    congrArg (cohOn.map k (omegaTrace hga j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q).symm_apply_apply _)
  have hT : ψ ≫ omegaTrace hga j = omegaTrace hg j :=
    (Category.assoc _ _ _).trans (omegaTrace_iso e g he hg hga j)
  rw [e3, ← hT]
  clear_value ψ
  rw [cohOn.map_comp]
  rfl

end

private theorem exists_iso_open {Y : Scheme.{0}} (T A : Y.Opens) (hA : A ≤ T) :
    ∃ e : (T.ι ⁻¹ᵁ A).toScheme ⟶ A.toScheme, IsIso e ∧ e ≫ A.ι = (T.ι ⁻¹ᵁ A).ι ≫ T.ι := by
  have hEq : T.ι ''ᵁ (T.ι ⁻¹ᵁ A) = A := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hA
  refine ⟨(T.ι.isoImage (T.ι ⁻¹ᵁ A)).hom ≫ (Y.isoOfEq hEq).hom, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]

private theorem hodgePull_congr {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂) (h₁ : f₁ ≫ s = s') (h₂ : f₂ ≫ s = s')
    (j q : ℕ) (x : hodgeH s j q) : hodgePull h₁ j q x = hodgePull h₂ j q x := by
  subst e
  rfl

/-- Trace base change for a clopen restriction of the source, expressed on an
open of the original source rather than on a nested open. -/
private theorem hodgePull_hodgeTrace_restrict_source
    {Y Z : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    (c : Y ⟶ Z) (V : Z.Opens) (U W : Y.Opens)
    (hWU : W ≤ U)
    (hW : U.ι ⁻¹ᵁ W = (U.ι ≫ c) ⁻¹ᵁ V)
    [IsFinite (U.ι ≫ c)] [Etale (U.ι ≫ c)]
    (p : W.toScheme ⟶ V.toScheme) [IsFinite p] [Etale p]
    (hp : p ≫ V.ι = W.ι ≫ c)
    (hf : (U.ι ≫ c) ≫ s = U.ι ≫ s')
    (hg : p ≫ V.ι ≫ s = W.ι ≫ s')
    (hk : Y.homOfLE hWU ≫ U.ι ≫ s' = W.ι ≫ s')
    (a b : ℕ) (x : hodgeH (U.ι ≫ s') a b) :
    hodgePull (f := V.ι) (s' := V.ι ≫ s) rfl a b
        (hodgeTrace hf a b x) =
      hodgeTrace hg a b (hodgePull hk a b x) := by
  let f := U.ι ≫ c
  let R := f ⁻¹ᵁ V
  have he0 : ∃ e : R.toScheme ⟶ W.toScheme,
      IsIso e ∧ e ≫ W.ι = R.ι ≫ U.ι := by
    dsimp only [R, f]
    rw [← hW]
    exact exists_iso_open U W hWU
  obtain ⟨e, heIso, hefac⟩ := he0
  letI : IsIso e := heIso
  have hek : e ≫ Y.homOfLE hWU = R.ι := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, hefac]
  have he : e ≫ W.ι ≫ s' = R.ι ≫ U.ι ≫ s' := by
    rw [← Category.assoc, hefac, Category.assoc]
  have hep : f ∣_ V = e ≫ p := by
    apply (cancel_mono V.ι).mp
    rw [morphismRestrict_ι, Category.assoc, hp, ← Category.assoc, hefac,
      Category.assoc]
  have hR : (f ∣_ V) ≫ V.ι ≫ s = R.ι ≫ U.ι ≫ s' := by
    rw [hep, Category.assoc, hg, he]
  have hcomp : (e ≫ Y.homOfLE hWU) ≫ U.ι ≫ s' = R.ι ≫ U.ι ≫ s' := by
    rw [hek]
  have hpull : hodgePull (f := R.ι) (s := U.ι ≫ s') rfl a b x =
      hodgePull he a b (hodgePull hk a b x) := by
    rw [hodgePull_comp hk he hcomp]
    exact hodgePull_congr hek.symm _ _ a b x
  calc
    _ = hodgeTrace hR a b (hodgePull (f := R.ι) rfl a b x) :=
      hodgePull_hodgeTrace_ι hf V a b x
    _ = hodgeTrace hR a b (hodgePull he a b (hodgePull hk a b x)) :=
      congrArg (hodgeTrace hR a b) hpull
    _ = _ := hodgeTrace_iso e p (f ∣_ V)
      hep he hg hR a b _

private theorem isClosed_part {X : Scheme.{0}} {M : Type} (W : M → X.Opens)
    (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hc : iSup W = ⊤) (j : M) : IsClosed (W j : Set X) := by
  rw [← isOpen_compl_iff]
  have h : (W j : Set X)ᶜ = ⋃ i ∈ {i | i ≠ j}, (W i : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · intro hx
      have hx' : x ∈ iSup W := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      exact ⟨i, fun e => hx (e ▸ hi), hi⟩
    · rintro ⟨i, hij, hi⟩ hx
      have hm : x ∈ W i ⊓ W j := ⟨hi, hx⟩
      rw [hd i j hij] at hm
      exact hm
  rw [h]
  exact isOpen_biUnion fun i _ => (W i).isOpen

open Classical in
private theorem sum_part {J T : Type} [Fintype J] (F : Finset T) (R : J → Set T)
    (h : ∀ y ∈ F, ∃! j, y ∈ R j) (g : T → ℂ) :
    ∑ j, ∑ y ∈ F with y ∈ R j, g y = ∑ y ∈ F, g y := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨j, hj, hu⟩ := h y hy
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hk
    simp [show y ∉ R k from fun h' => hk (hu k h')]
  · intro h
    exact absurd (Finset.mem_univ j) h

open Classical in
private theorem final_sum {J T : Type} [Fintype J] (D : Finset ℕ) (t : ℕ → ℂ)
    (tj : J → ℕ → ℂ) (ht : ∀ b, t b = ∑ j, tj j b) (F : Finset T) (R : J → Set T)
    (hp : ∀ y ∈ F, ∃! j, y ∈ R j) (g : T → ℂ)
    (hz : ∀ j, ∑ b ∈ D, (-1 : ℂ) ^ b * tj j b = ∑ y ∈ F with y ∈ R j, g y) :
    ∑ b ∈ D, (-1 : ℂ) ^ b * t b = ∑ y ∈ F, g y := by
  simp_rw [ht, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hz]
  exact sum_part F R hp g

private noncomputable def ptIn {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens)
    (y : CxPts (W.ι ≫ s') (RingHom.id ℂ)) : CxPts s' (RingHom.id ℂ) :=
  ⟨y.1 ≫ W.ι, by rw [Category.assoc]; exact y.2⟩

private theorem ptIn_val {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens)
    (y : CxPts (W.ι ≫ s') (RingHom.id ℂ)) : (ptIn W y).1 = y.1 ≫ W.ι := rfl

private theorem ptIn_injective {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens) :
    Function.Injective (ptIn (s' := s') W) := by
  intro y1 y2 h
  have h' : y1.1 ≫ W.ι = y2.1 ≫ W.ι := congrArg Subtype.val h
  exact Subtype.ext ((cancel_mono W.ι).1 h')

open Classical in
private theorem sum_pre {S T : Type} (φ : S → T) (hφ : Function.Injective φ) (F : Finset T)
    (g : T → ℂ) : ∑ y ∈ F.preimage φ hφ.injOn, g (φ y) = ∑ y ∈ F with y ∈ Set.range φ, g y :=
  Finset.sum_preimage' φ F hφ.injOn g

open Classical in
private theorem block_fixed {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Z}
    (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (d : ℕ) [SmoothOfRelativeDimension d s]
    (hproj : IsProjOver s) (V : Z.Opens) (hV : IsClosed (V : Set Z)) [IsIntegral V.toScheme]
    (W : Y.Opens) (c1' c2' : W.toScheme ⟶ V.toScheme) (e1 : c1' ≫ V.ι = W.ι ≫ c1)
    (e2 : c2' ≫ V.ι = W.ι ≫ c2) [IsFinite c1'] [Etale c1'] (f2 : IsFinite c2') (t2 : Etale c2')
    (g1 : c1' ≫ V.ι ≫ s = W.ι ≫ s') (g2 : c2' ≫ V.ι ≫ s = W.ι ≫ s')
    (F : Finset (CxPts s' (RingHom.id ℂ))) (hF : ∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2)
    (A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ y ∈ F, IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) (a : ℕ) :
    (∀ b, FiniteDimensional ℂ (hodgeH (V.ι ≫ s) a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hodgeTrace g1 a b ∘ₗ hodgePull g2 a b) =
      ∑ y ∈ F with y ∈ Set.range (ptIn (s' := s') W),
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
          (1 - A y).det := by
  haveI hsm : SmoothOfRelativeDimension d (V.ι ≫ s) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := d) V.ι s
    simpa using this
  have hF' : ∀ y : CxPts (W.ι ≫ s') (RingHom.id ℂ),
      y ∈ F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn ↔ y.1 ≫ c1' = y.1 ≫ c2' := by
    intro y
    rw [Finset.mem_preimage, hF, ptIn_val]
    constructor
    · intro h
      apply (cancel_mono V.ι).mp
      simp only [Category.assoc, e1, e2]
      simpa only [Category.assoc] using h
    · intro h
      have h' := congrArg (· ≫ V.ι) h
      simp only [Category.assoc, e1, e2] at h'
      simpa only [Category.assoc] using h'
  have hA' : ∀ y ∈ F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn,
      IsTan d c1' c2' g1 g2 y (A (ptIn W y)) ∧ (1 - A (ptIn W y)).det ≠ 0 := by
    intro y hy
    rw [Finset.mem_preimage] at hy
    obtain ⟨ht, hd⟩ := hA _ hy
    exact ⟨(UpperTheory.Cb.isTangentMatrix_iff_restrict_open Z Y s s' d c1 c2 h1 h2 V W c1' c2' e1 e2 (ptIn W y) y
      (ptIn_val W y).symm _).mp ht, hd⟩
  have key := UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_correspondence V.toScheme (V.ι ≫ s) d (UpperTheory.Cb.isProjOver_restrict_clopen Z s V hV hproj)
    W.toScheme (W.ι ≫ s') c1' c2' g1 g2 f2 t2
    (F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn) hF' (fun y => A (ptIn W y)) hA' a
  refine ⟨key.1, ?_⟩
  rw [key.2]
  exact sum_pre (ptIn (s' := s') W) (ptIn_injective W) F
    (fun y => (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
      (1 - A y).det)

/-- Lifting a complex point to an open is equivalent to membership of its
unique underlying point. No covering or indexing hypothesis is needed. -/
private theorem ptIn_range_iff {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ}
    (W : Y.Opens) (y : CxPts s' (RingHom.id ℂ)) :
    y ∈ Set.range (ptIn (s' := s') W) ↔
      y.1 (IsLocalRing.closedPoint ℂ) ∈ W := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.1 ≫ W.ι = y.1 := congrArg Subtype.val hz
    rw [← hz', Scheme.Hom.comp_apply]
    exact (z.1 (IsLocalRing.closedPoint ℂ)).2
  · intro hy
    have hr : Set.range y.1 ⊆ Set.range W.ι := by
      rintro _ ⟨a, rfl⟩
      rw [show a = IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _,
        Scheme.Opens.range_ι]
      exact hy
    let z : CxPts (W.ι ≫ s') (RingHom.id ℂ) :=
      ⟨IsOpenImmersion.lift W.ι y.1 hr, by
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact y.2⟩
    exact ⟨z, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩

private theorem fixed_part {Z Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ}
    {c1 c2 : Y ⟶ Z} {J : Type} (V : J → Z.Opens)
    (hd : ∀ i j (z : Z), z ∈ V i → z ∈ V j → i = j)
    (hc : ∀ z : Z, ∃ j, z ∈ V j)
    (y : CxPts s' (RingHom.id ℂ)) (hy : y.1 ≫ c1 = y.1 ≫ c2) :
    ∃! j, y ∈ Set.range (ptIn (s' := s') (c1 ⁻¹ᵁ V j ⊓ c2 ⁻¹ᵁ V j)) := by
  let x0 : (Sp ℂ : Scheme.{0}) := IsLocalRing.closedPoint ℂ
  have he : c1 (y.1 x0) = c2 (y.1 x0) := by
    have h := congrArg (fun f => f.base x0) hy
    simpa using h
  obtain ⟨j, hj⟩ := hc (c1 (y.1 x0))
  refine ⟨j, (ptIn_range_iff _ _).2 ?_, ?_⟩
  · exact ⟨hj, by simpa only [← he] using hj⟩
  · intro k hk
    have hm := (ptIn_range_iff _ _).1 hk
    exact hd k j _ hm.1 hj

theorem lefschetz_fixedPoint_finite_etale_correspondence :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  intro Z s d _ hproj Y s' c1 c2 h1 h2 _ _ f2 t2 F hF A hA a
  classical
  haveI := f2
  haveI := t2
  haveI : CompactSpace Z := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.1 Z s hproj
  obtain ⟨J, _, V, hVd, hVc, hVi⟩ := _root_.GlobalTheory.SmoothComponents.main Z s d
  have hVd' : ∀ i j (z : Z), z ∈ V i → z ∈ V j → i = j := by
    intro i j z hi hj
    by_contra hne
    have hz : z ∈ V i ⊓ V j := ⟨hi, hj⟩
    rw [hVd i j hne] at hz
    exact hz
  have hVcl : ∀ j, IsClosed (V j : Set Z) := fun j => isClosed_part V hVd hVc j
  have hVall : ∀ z : Z, ∃ j, z ∈ V j := by
    intro z
    have hz : z ∈ iSup V := by rw [hVc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hz
  -- One-sided partition of Y, followed by its diagonal subopens.
  let U : J → Y.Opens := fun j => c2 ⁻¹ᵁ V j
  let W : J → Y.Opens := fun j => c1 ⁻¹ᵁ V j ⊓ U j
  have hUcl : ∀ j, IsClosed (U j : Set Y) := fun j => (hVcl j).preimage c2.continuous
  have hWcl : ∀ j, IsClosed (W j : Set Y) := by
    intro j
    change IsClosed (c1 ⁻¹' (V j : Set Z) ∩ (U j : Set Y))
    exact ((hVcl j).preimage c1.continuous).inter (hUcl j)
  have hUd : ∀ i j, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    ext y
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    intro hi hj
    exact hij (hVd' i j (c2 y) hi hj)
  have hUc : iSup U = ⊤ := by
    change iSup (fun j => c2 ⁻¹ᵁ V j) = ⊤
    rw [← Scheme.Hom.preimage_iSup, hVc]
    rfl
  haveI : ∀ j, IsClosedImmersion (U j).ι := fun j =>
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUcl j)
  haveI hUf : ∀ j, IsFinite ((U j).ι ≫ c1) := fun j => inferInstance
  haveI hUe : ∀ j, Etale ((U j).ι ≫ c1) := fun j => inferInstance
  have hf : ∀ j, ((U j).ι ≫ c1) ≫ s = (U j).ι ≫ s' := fun j => by rw [Category.assoc, h1]
  let g : ∀ j, (U j).toScheme ⟶ (V j).toScheme := fun j => c2 ∣_ V j
  have eg : ∀ j, g j ≫ (V j).ι = (U j).ι ≫ c2 := fun j => morphismRestrict_ι c2 (V j)
  have hg : ∀ j, g j ≫ (V j).ι ≫ s = (U j).ι ≫ s' := fun j => by
    rw [← Category.assoc, eg, Category.assoc, h2]
  have ex1 : ∀ j, ∃ p : (W j).toScheme ⟶ (V j).toScheme,
      p ≫ (V j).ι = (W j).ι ≫ c1 ∧ IsFinite p ∧ Etale p := fun j =>
    UpperTheory.Cb.exists_finite_etale_restrict_clopen Y Z c1 (V j) (W j) (hWcl j)
      inf_le_left inferInstance inferInstance
  have ex2 : ∀ j, ∃ q : (W j).toScheme ⟶ (V j).toScheme,
      q ≫ (V j).ι = (W j).ι ≫ c2 ∧ IsFinite q ∧ Etale q := fun j =>
    UpperTheory.Cb.exists_finite_etale_restrict_clopen Y Z c2 (V j) (W j) (hWcl j)
      inf_le_right f2 t2
  choose p ep fp tp using ex1
  choose q eq fq tq using ex2
  haveI : ∀ j, IsFinite (p j) := fp
  haveI : ∀ j, Etale (p j) := tp
  have hp : ∀ j, p j ≫ (V j).ι ≫ s = (W j).ι ≫ s' := fun j => by
    rw [← Category.assoc, ep, Category.assoc, h1]
  have hq : ∀ j, q j ≫ (V j).ι ≫ s = (W j).ι ≫ s' := fun j => by
    rw [← Category.assoc, eq, Category.assoc, h2]
  have hWU : ∀ j, W j ≤ U j := fun _ => inf_le_right
  let k : ∀ j, (W j).toScheme ⟶ (U j).toScheme := fun j => Y.homOfLE (hWU j)
  have ek : ∀ j, k j ≫ (U j).ι = (W j).ι := fun j => Scheme.homOfLE_ι (hWU j)
  have hk : ∀ j, k j ≫ (U j).ι ≫ s' = (W j).ι ≫ s' := fun j => by
    rw [← Category.assoc, ek]
  have hkg : ∀ j, k j ≫ g j = q j := by
    intro j
    apply (cancel_mono (V j).ι).mp
    rw [Category.assoc, eg, ← Category.assoc, ek, eq]
  have hWpre : ∀ j, (U j).ι ⁻¹ᵁ W j = ((U j).ι ≫ c1) ⁻¹ᵁ V j := by
    intro j
    ext z
    change (c1 ((U j).ι z) ∈ V j ∧ (U j).ι z ∈ U j) ↔ ((U j).ι ≫ c1) z ∈ V j
    rw [Scheme.Hom.comp_apply]
    exact ⟨And.left, fun hz => ⟨hz, z.2⟩⟩
  -- Keep the original integral-target reduction and tangent comparison.
  have hblock : ∀ j, (∀ b, FiniteDimensional ℂ (hodgeH ((V j).ι ≫ s) a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hodgeTrace (hp j) a b ∘ₗ hodgePull (hq j) a b) =
      ∑ y ∈ F with y ∈ Set.range (ptIn (s' := s') (W j)),
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
          (1 - A y).det := by
    intro j
    haveI := hVi j
    exact block_fixed h1 h2 d hproj (V j) (hVcl j) (W j) (p j) (q j)
      (ep j) (eq j) (fq j) (tq j) (hp j) (hq j) F hF A hA a
  have hFD : ∀ b, FiniteDimensional ℂ (hodgeH s a b) := fun b =>
    UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj Z s d hproj a b
  -- Factor the global operator through the individual target cohomology spaces.
  let r (b : ℕ) (j : J) : hodgeH s a b →ₗ[ℂ] hodgeH ((V j).ι ≫ s) a b :=
    hodgePull (f := (V j).ι) rfl a b
  let B (b : ℕ) (j : J) : hodgeH ((V j).ι ≫ s) a b →ₗ[ℂ] hodgeH s a b :=
    hodgeTrace (hf j) a b ∘ₗ hodgePull (hg j) a b
  have hu : ∀ b, hodgeTrace h1 a b ∘ₗ hodgePull h2 a b =
      ∑ j, B b j ∘ₗ r b j := by
    intro b
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply,
      UpperTheory.Cb.hodgeTrace_eq_sum_clopen_decomposition Z Y s s' c1 h1 J U hUd hUc
        hUf hUe a b (hodgePull h2 a b x), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [B, r, LinearMap.comp_apply]
    rw [hodgePull_comp h2 rfl (by rw [Category.assoc, h2]),
      hodgePull_comp rfl (hg j) (by rw [Category.assoc, hg j])]
    exact congrArg (hodgeTrace (hf j) a b)
      (hodgePull_congr (eg j).symm _ _ a b x)
  -- Cyclicity of rectangular traces replaces the entire block-matrix argument.
  have ht : ∀ b, LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
      ∑ j, LinearMap.trace ℂ _ (hodgeTrace (hp j) a b ∘ₗ hodgePull (hq j) a b) := by
    intro b
    haveI := hFD b
    haveI : ∀ j, FiniteDimensional ℂ (hodgeH ((V j).ι ≫ s) a b) := fun j => (hblock j).1 b
    rw [hu b, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.trace_comp_comm' (r b j) (B b j)]
    apply congrArg (LinearMap.trace ℂ (hodgeH ((V j).ι ≫ s) a b))
    refine LinearMap.ext fun x => ?_
    simp only [r, B, LinearMap.comp_apply]
    rw [hodgePull_hodgeTrace_restrict_source c1 (V j) (U j) (W j)
      (hWU j) (hWpre j) (p j) (ep j) (hf j) (hp j) (hk j) a b
      (hodgePull (hg j) a b x)]
    rw [hodgePull_comp (hg j) (hk j) (by rw [Category.assoc, hk j])]
    exact congrArg (hodgeTrace (hp j) a b)
      (hodgePull_congr (hkg j) _ _ a b x)
  refine ⟨hFD, ?_⟩
  exact final_sum (Finset.range (d + 1)) _ _ ht F
    (fun j => Set.range (ptIn (s' := s') (W j)))
    (fun y hy => fixed_part V hVd' hVall y ((hF y).1 hy)) _ (fun j => (hblock j).2)

end RHShrinkTrial

#print axioms RHShrinkTrial.lefschetz_fixedPoint_finite_etale_correspondence
