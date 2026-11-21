import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem implocus_open_closed : ∀ (Y : Scheme.{0}) (Z : Over Y) (P Q : ∀ T : Over Y, (T ⟶ Z) → Prop), IsFinite Z.hom → Etale Z.hom → GlobalTheory.LevCover.ClopenCond Z P → GlobalTheory.LevCover.ClopenCond Z Q → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ z : Over.mk x ⟶ Z, P _ z → Q _ z := by
  intro Y Z P Q hfin het hP hQ
  obtain ⟨U, hUc, HU⟩ := hP
  obtain ⟨V, hVc, HV⟩ := hQ
  let B : Set Z.left := (U : Set Z.left) \ V
  have hBo : IsOpen B := U.isOpen.sdiff hVc
  have hBc : IsClosed B := hUc.sdiff V.isOpen
  have c1 : ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ (Z.hom.base '' B)ᶜ ↔
      ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z := by
    intro Tb t
    constructor
    · intro hW T σ hσ z hPz
      rw [HU] at hPz
      rw [HV]
      rintro _ ⟨w, rfl⟩
      by_contra hv
      have hb : z.left.base w ∈ B := ⟨hPz ⟨w, rfl⟩, hv⟩
      apply hW ⟨σ.base w, rfl⟩
      refine ⟨_, hb, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w z, ← hσ, Scheme.Hom.comp_apply]
    · intro H
      rintro _ ⟨τ, rfl⟩ ⟨u, hu, hτ⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback τ u hτ.symm
      let O : (pullback t Z.hom).Opens := (pullback.snd t Z.hom) ⁻¹ᵁ ⟨B, hBo⟩
      let T : Over Y := Over.mk (O.ι ≫ pullback.fst t Z.hom ≫ t)
      let z : T ⟶ Z := Over.homMk (O.ι ≫ pullback.snd t Z.hom) (by simp [T, pullback.condition])
      have hmem : ∀ w, O.ι.base w ∈ (O : Set _) := fun w => by
        rw [← Scheme.Opens.range_ι O]; exact ⟨w, rfl⟩
      have hPz : P T z := by
        rw [HU]
        rintro _ ⟨w, rfl⟩
        exact (hmem w).1
      have hQz := H T (O.ι ≫ pullback.fst t Z.hom) (Category.assoc _ _ _) z hPz
      rw [HV] at hQz
      have hpO : p ∈ Set.range O.ι.base := by
        rw [Scheme.Opens.range_ι O]
        show (pullback.snd t Z.hom).base p ∈ B
        rw [hp2]; exact hu
      obtain ⟨w, hw⟩ := hpO
      apply hu.2
      have := hQz ⟨w, rfl⟩
      simpa [z, Scheme.Hom.comp_apply, hw, hp2] using this
  refine ⟨(Z.hom.base '' B)ᶜ, (Z.hom.isClosedMap _ hBc).isOpen_compl,
    (Z.hom.isOpenMap _ hBo).isClosed_compl, c1, ?_⟩
  intro k _ _ x
  constructor
  · intro hW z hPz
    exact (c1 (Sp k) x).1 hW (Over.mk x) (𝟙 _) (Category.id_comp _) z hPz
  · intro H
    rintro _ ⟨s, rfl⟩ ⟨u, hu, hs⟩
    let Bo : Z.left.Opens := ⟨B, hBo⟩
    haveI : IsClosedImmersion Bo.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hBc)
    have huB : u ∈ Set.range Bo.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := GlobalTheory.LevCover.exists_lift_geom (Bo.ι ≫ Z.hom) x (by
      rintro _ ⟨s', rfl⟩
      refine ⟨v, ?_⟩
      rw [Subsingleton.elim s' s, Scheme.Hom.comp_apply, hv, hs])
    let z : Over.mk x ⟶ Z := Over.homMk (w ≫ Bo.ι) (by simpa using hw)
    have hPz : P _ z := by
      rw [HU]
      rintro _ ⟨y, rfl⟩
      have : (Bo.ι.base (w.base y)) ∈ (Bo : Set Z.left) := by
        rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
      exact this.1
    have hQz := H z hPz
    rw [HV] at hQz
    let y0 : Sp k := (⊥ : PrimeSpectrum k)
    have h1 : (Bo.ι.base (w.base y0)) ∈ (Bo : Set Z.left) := by
      rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
    exact h1.2 (hQz ⟨y0, rfl⟩)

end GlobalTheory.LevCover
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem clopenCond_comp_eq_one {Y : Scheme.{0}} (Zt B : Over Y) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : IsUnit (n : Γ(Y, ⊤))) (g : Zt ⟶ B) (hg : g ^ n = 1) :
    ClopenCond Zt (fun _ z => z ≫ g = 1) := by
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  obtain ⟨u, hu, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n g hg
  obtain ⟨u', hu', -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n (1 : Zt ⟶ B) (one_pow n)
  refine (clopenCond_eq u u').congr fun T z => ⟨fun h => ?_, fun h => ?_⟩
  · have hz : (z ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion B n (z ≫ g) hz).unique ?_ ?_
    · rw [Category.assoc, hu]
    · rw [Category.assoc, hu', MonObj.comp_one, h]
  · rw [← hu, ← Category.assoc, h, Category.assoc, hu', MonObj.comp_one]

theorem kerlocus_open_closed : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  intro Y A _ _ n J _ B _ f B' _ f' hA hB hB' hf hf' hn
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  have hι : torsion.ι A n ^ n = 1 := GlobalTheory.LatticeTorsion.torsionι_pow_eq_one A n
  have hpow : ∀ (C : Over Y) [GrpObj C] (g : A ⟶ C) [IsMonHom g], (torsion.ι A n ≫ g) ^ n = 1 := by
    intro C _ g _
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]
  obtain ⟨W, hWo, hWc, H1, H2⟩ := implocus_open_closed Y (torsion A n)
    (fun _ z => ∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) (fun _ z => z ≫ (torsion.ι A n ≫ f') = 1) hfin het
    (ClopenCond.forall_finite fun i =>
      clopenCond_comp_eq_one _ (B i) (hB i) n hn _ (hpow (B i) (f i)))
    (clopenCond_comp_eq_one _ B' hB' n hn _ (hpow B' f'))
  have key : ∀ T : Over Y, (∀ z : T ⟶ torsion A n, (∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) →
      z ≫ (torsion.ι A n ≫ f') = 1) ↔
      ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
    intro T
    constructor
    · intro H a ha hfa
      obtain ⟨z, hz, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A n a ha
      have h := H z (fun i => by rw [← Category.assoc, hz, hfa i])
      rwa [← Category.assoc, hz] at h
    · intro H z hz
      have h := H (z ≫ torsion.ι A n) (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])
        (fun i => by rw [Category.assoc]; exact hz i)
      rwa [Category.assoc] at h
  refine ⟨W, hWo, hWc, fun Tb t => (H1 Tb t).trans ?_, fun k _ _ x => (H2 k x).trans (key _)⟩
  exact forall_congr' fun T => forall_congr' fun σ => forall_congr' fun _ => key T

end GlobalTheory.LevCover
end
end
