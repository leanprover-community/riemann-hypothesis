import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) : hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _ using 2
  exact CategoryTheory.Functor.map_id _ _

private theorem appLE_top_top {V X : Scheme.{0}} (a : V ⟶ X) (e : (⊤ : V.Opens) ≤ a ⁻¹ᵁ ⊤) :
    a.appLE ⊤ ⊤ e = a.appTop := by
  change a.app ⊤ ≫ V.presheaf.map (homOfLE e).op = a.app ⊤
  exact (congrArg (a.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)

private theorem exists_hom_of_ring {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U) ⟶ Γ(V, ⊤)) :
    ∃ (y : V ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ U), y.appLE U ⊤ h = f := by
  have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₂ : (⊤ : V.Opens) ≤ (V.toSpecΓ ≫ Spec.map f) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨(V.toSpecΓ ≫ Spec.map f) ≫ hU.fromSpec, ?_, ?_⟩
  · exact e₂.trans (Scheme.Hom.preimage_mono _ e₁)
  · rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂, fromSpec_appLE_top]
    have : (V.toSpecΓ ≫ Spec.map f).appLE ⊤ ⊤ e₂ = (Spec.map f).appTop ≫ (Scheme.ΓSpecIso Γ(V, ⊤)).hom := by
      rw [appLE_top_top, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [this, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private theorem hom_eq_of_appLE {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (a b : V ⟶ X)
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b := by
  have key : ∀ (c : V ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ U), ∃ c' : V ⟶ Spec Γ(X, U), c' ≫ hU.fromSpec = c ∧
      c'.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ c.appLE U ⊤ hc := by
    intro c hc
    have hr : Set.range c ⊆ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact hc (Set.mem_univ x)
    refine ⟨IsOpenImmersion.lift hU.fromSpec c hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have e₂ : (⊤ : V.Opens) ≤ (IsOpenImmersion.lift hU.fromSpec c hr) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have := Scheme.Hom.appLE_comp_appLE (IsOpenImmersion.lift hU.fromSpec c hr) hU.fromSpec U ⊤ ⊤ e₁ e₂
    rw [fromSpec_appLE_top, appLE_top_top] at this
    have h2 : (IsOpenImmersion.lift hU.fromSpec c hr ≫ hU.fromSpec).appLE U ⊤
        (by rw [IsOpenImmersion.lift_fac]; exact hc) = c.appLE U ⊤ hc := by
      simp only [IsOpenImmersion.lift_fac]
    rw [← this.trans h2, Iso.hom_inv_id_assoc]
  obtain ⟨a', ha', ea⟩ := key a ha
  obtain ⟨b', hb', eb⟩ := key b hb
  rw [← ha', ← hb', ext_of_isAffine (f := a') (g := b') (by rw [ea, eb, h])]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartLift :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ (α : B.ι) (k : Fin d) {V : Scheme.{0}} (p : V ⟶ W), ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α → ∀ (w : Fin d → Γ(V, ⊤)), w k = 1 → ∃ (y : V ⟶ T) (h : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.c α).C k), y ≫ r = p ∧ uV B α k (y ≫ j) h = w := by
  intro K _ W Z Y q i π D d B T j r hpb α k V p hp w hk
  have ht : ∀ m, ((p ≫ i).appLE (B.V α) ⊤ hp).hom ((B.c α).t m) = 0 := by
    intro m
    have hm : (B.c α).t m ∈ RingHom.ker (i.app (B.V α)).hom := by
      rw [(B.c α).ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.mem_ker.mp hm, map_zero]
  let ψ := MvPolynomial.eval₂Hom (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).u k)
  let φ : MvPolynomial (Fin d) Γ(Z, B.V α) →+* Γ(V, ⊤) :=
    MvPolynomial.eval₂Hom ((p ≫ i).appLE (B.V α) ⊤ hp).hom w
  have hφC : ∀ a, φ (MvPolynomial.C a) = ((p ≫ i).appLE (B.V α) ⊤ hp).hom a := fun a =>
    MvPolynomial.eval₂_C _ _ _
  have hker : RingHom.ker ψ ≤ RingHom.ker φ := by
    change RingHom.ker (MvPolynomial.eval₂Hom _ _) ≤ _
    rw [(B.c α).rel k, Ideal.span_le]
    rintro x (rfl | ⟨m, rfl⟩)
    · simp [φ, hk]
    · change φ _ = 0
      rw [map_sub, map_mul, hφC, hφC, ht, ht, zero_mul, sub_zero]
  let f : Γ(Y, (B.c α).C k) →+* Γ(V, ⊤) := RingHom.liftOfSurjective ψ ((B.c α).surj k) ⟨φ, hker⟩
  have hf : ∀ x, f (ψ x) = φ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φ, hker⟩ x
  obtain ⟨y₀, h₀, hy₀⟩ := exists_hom_of_ring ((B.c α).C_aff k) (CommRingCat.ofHom f)
  have hπ : ⊤ ≤ (y₀ ≫ π) ⁻¹ᵁ B.V α := h₀.trans (Scheme.Hom.preimage_mono _ ((B.c α).C_le k))
  have hc : y₀ ≫ π = p ≫ i := by
    refine hom_eq_of_appLE (B.c α).affine _ _ hπ hp ?_
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ ((B.c α).C_le k) h₀, hy₀]
    ext a
    have := hf (MvPolynomial.C a)
    simpa [ψ, φ] using this
  have hyj : hpb.lift y₀ p hc ≫ j = y₀ := hpb.lift_fst _ _ _
  refine ⟨hpb.lift y₀ p hc, by rw [hyj]; exact h₀, hpb.lift_snd _ _ _, ?_⟩
  have gen : ∀ (y' : V ⟶ Y) (e : y' = y₀) (h : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), uV B α k y' h = w := by
    intro y' e h
    have hy' : Scheme.Hom.appLE y' _ ⊤ h = CommRingCat.ofHom f := by
      subst e
      exact hy₀
    funext m
    have := hf (MvPolynomial.X m)
    simp only [ψ, φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    unfold uV
    rw [hy']
    exact this
  exact gen _ hyj _
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem exists_basicOpen_of_span {V : Scheme.{0}} {d : ℕ} (v : Fin d → Γ(V, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : V) : ∃ k, x ∈ V.basicOpen (v k) := by
  by_contra hn
  push_neg at hn
  let φ : Γ(V, ⊤) →+* V.presheaf.stalk x := (V.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have := hn k
    rw [Scheme.mem_basicOpen_top] at this
    exact (IsLocalRing.mem_maximalIdeal _).2 this
  rw [h] at hle
  have h1 : (1 : Γ(V, ⊤)) ∈ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := hle trivial
  have h2 : φ 1 ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk x) := h1
  rw [map_one] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 isUnit_one

private theorem isUnit_restrict {V : Scheme.{0}} (s : Γ(V, ⊤)) (U : V.Opens) (hU : U ≤ V.basicOpen s) :
    IsUnit (U.ι.appTop.hom s) := by
  have h0 : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le s)).op).hom s) :=
    RingedSpace.isUnit_res_basicOpen _ _
  have hle : ⊤ ≤ U.ι ⁻¹ᵁ V.basicOpen s := by
    intro z _
    exact hU z.2
  have h1 : U.ι.appTop = V.presheaf.map (homOfLE (V.basicOpen_le s)).op ≫ U.ι.appLE (V.basicOpen s) ⊤ hle := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE U.ι
  rw [h1]
  exact h0.map (U.ι.appLE (V.basicOpen s) ⊤ hle).hom

private theorem uV_congr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
    {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d)
    {V : Scheme.{0}} {f g : V ⟶ Y} (e : f = g) (h : ⊤ ≤ f ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ g ⁻¹ᵁ (B.c α).C k) :
    uV B α k f h = uV B α k g h' := by
  subst e; rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ontoField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a₀ : V ⟶ WP B) (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ TP B j) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧ a ≫ rhoP B j r hsq.w = U.ι ≫ a₀ ∧ a.appTop.hom ∘ v = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a₀ v₀ x
  obtain ⟨U₀, α, a₁, hx₀, ha₁⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a₀ x
  obtain ⟨k, hk⟩ := exists_basicOpen_of_span v₀.1 v₀.2 x
  let U : V.Opens := U₀ ⊓ V.basicOpen (v₀.1 k)
  obtain ⟨e, he⟩ := isUnit_restrict (v₀.1 k) U inf_le_right
  let a₂ : (U : Scheme.{0}) ⟶ (oW B α : Scheme.{0}) := V.homOfLE (inf_le_left : U ≤ U₀) ≫ a₁
  let p : (U : Scheme.{0}) ⟶ W := a₂ ≫ (oW B α).ι
  have hp : ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α := by
    intro z _
    have hz : (a₂ z).1 ∈ oW B α := (a₂ z).2
    exact hz
  let w : Fin d → Γ((U : Scheme.{0}), ⊤) := fun m => (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 m)
  have hwk : w k = 1 := by
    change (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 k) = 1
    rw [← he]; exact e.inv_mul
  obtain ⟨y, hy, hyr, huv⟩ := chartLift B j r hsq α k p hp w hwk
  have hrange : Set.range y ⊆ Set.range (oT B j (α, k)).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : (y ≫ j) z ∈ (B.c α).C k := hy (Set.mem_univ z)
    rw [Scheme.Hom.comp_apply] at hz
    exact hz
  let y₁ : (U : Scheme.{0}) ⟶ (oT B j (α, k) : Scheme.{0}) := IsOpenImmersion.lift (oT B j (α, k)).ι y hrange
  have hy₁ : y₁ ≫ (oT B j (α, k)).ι = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨h', hv', -, hrho⟩ := pieceFacts B j r hsq.w v hv (α, k) y₁
  have hpath : (y₁ ≫ tI B j (α, k)) ≫ eP B j ≫ j = y ≫ j := by
    have : tI B j (α, k) ≫ eP B j = (oT B j (α, k)).ι := by
      simp [tI, eP]
    rw [← hy₁, Category.assoc, reassoc_of% this, Category.assoc]
  have hmap : y₁ ≫ rhoC B j r hsq.w (α, k) = a₂ := by
    rw [← cancel_mono (oW B α).ι]
    have : rhoC B j r hsq.w (α, k) ≫ (oW B α).ι = (oT B j (α, k)).ι ≫ r := IsOpenImmersion.lift_fac _ _ _
    rw [Category.assoc, this, reassoc_of% hy₁, hyr]
  refine ⟨U, y₁ ≫ tI B j (α, k), e⁻¹, ⟨hx₀, hk⟩, ?_, ?_⟩
  · rw [hrho, hmap]
    have hι : U.ι ≫ a₀ = V.homOfLE (inf_le_left : U ≤ U₀) ≫ U₀.ι ≫ a₀ := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hι, ha₁]
    simp only [a₂, Category.assoc]
    rfl
  · rw [hv', uV_congr B α k hpath h' hy, huv]
    rfl
end
