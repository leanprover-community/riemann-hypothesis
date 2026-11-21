import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChangeStatement

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

open GlobalTheory.Cube in

theorem isZero_homology_supp_singleton {ν κ : Type} [LinearOrder ν] [LinearOrder κ] {R : Type}
    [CommRing R] (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R) {Q : Set (Finset ν)} (hQ : Q.OrdConnected)
    (hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1}) (j : κ) (n : ℕ)
    (h : Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q
      {t : Finset κ | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₁))).homology n)) :
    Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology n) := by
  have hsub : ∀ u, u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}} →
      u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1} := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have : part (inrEmb ν κ) u = {j} := hu.2
    simp [this]
  have heq : ∀ {a b : Finset κ}, a ⊆ b → a = {j} → b.card = 1 → b = {j} := by
    rintro a b hab rfl hb
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hb
    rw [Finset.singleton_subset_singleton.1 hab]
  have heq' : ∀ {a b : Finset κ}, a ⊆ b → a.card = 1 → b = {j} → a = {j} := by
    rintro a b hab ha rfl
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 ha
    rw [Finset.singleton_subset_singleton.1 hab]
  let i : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) :=
    suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true
      ⟨ht.1, heq (monotone_part _ hst) hs.2 ht.2⟩ (hsub s hs)
  let r : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) :=
    suppMap (𝟙 A) _ _ fun s t hst hs ht => iff_of_true (hsub t ht)
      ⟨hs.1, heq' (monotone_part _ hst) hs.2 ht.2⟩
  have hir : i ≫ r = 𝟙 _ := by
    ext s x
    refine supp_ext fun hs => ?_
    change suppEquiv A _ hs (suppMapApp (𝟙 A) _ _ s (suppMapApp (𝟙 A) _ _ s x)) =
      suppEquiv A _ hs x
    rw [suppEquiv_suppMapApp _ (hsub s hs) hs, suppEquiv_suppMapApp _ hs (hsub s hs)]
    rfl
  rw [Limits.IsZero.iff_id_eq_zero]
  have hc : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n ≫
      HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map r) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hz : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n = 0 :=
    h.eq_of_tgt _ _
  rw [hz, Limits.zero_comp] at hc
  exact hc.symm

open GlobalTheory.Cube in

theorem cechComplex_sliceFst_singleton_acyclic_of_trunc₂ : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  intro ν κ _ _ _ _ R _ A hA hT j
  have hcompl := isCompl_range_inlEmb_inrEmb ν κ
  have hQ : Set.OrdConnected {s : Finset ν | s.Nonempty} := ordConnected_nonempty
  have hU₂ : IsUpperSet {t : Finset κ | 2 ≤ t.card} :=
    fun _ _ hst ht => le_trans ht (Finset.card_le_card hst)
  have hT₂ := hU₂.ordConnected
  have hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1} := by
    refine ⟨fun a ha b hb c hc => ?_⟩
    have h1 := Finset.card_le_card hc.1
    have h2 := Finset.card_le_card hc.2
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    omega
  have hS := GlobalTheory.cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂)
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ ordConnected_nonempty)
    (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₁)
    (fun u => by
      have hc : (part (inrEmb ν κ) u).Nonempty ↔
          2 ≤ (part (inrEmb ν κ) u).card ∨ (part (inrEmb ν κ) u).card = 1 := by
        rw [← Finset.card_pos]
        omega
      simp only [mem_partsIn, Set.mem_setOf_eq]
      tauto)
    (fun u hu hu' => by
      have h1 : 2 ≤ (part (inrEmb ν κ) u).card := hu.2
      have h2 : (part (inrEmb ν κ) u).card = 1 := hu'.2
      omega)
    (fun _ _ hst hs ht => ⟨ht.1, hU₂ (monotone_part _ hst) hs.2⟩))
  have h₁ : (GlobalTheory.cubeComplex (supp A _ (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂))).Acyclic := by
    rw [supp_partsIn_comm hQ hT₂ A]
    refine GlobalTheory.cubeComplex_supp_partsIn_acyclic hcompl.symm hT₂ hQ A fun t ht => ?_
    refine (GlobalTheory.cubeComplex_trunc₁_acyclic_iff _).2 ?_
    rw [← sliceFst_eq_slice]
    exact hA t ht
  have hzero : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ)
      {s : Finset ν | s.Nonempty} {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology (n + 2)) := fun n => by
    refine isZero_homology_supp_singleton A hQ hT₁ j (n + 2) ?_
    have := GlobalTheory.isIso_homologyMap_g_of_acyclic hS h₁ (n + 2)
    exact (hT n).of_iso (@asIso _ _ _ _ _ this).symm
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine ((hzero n).of_iso
    (GlobalTheory.suppSingletonHomologyIso hcompl hQ j A (n + 1)).symm).of_iso
    (GlobalTheory.cechHomologyMapIso (eqToIso (sliceFst_eq_slice A {j})) n ≪≫
      (GlobalTheory.truncHomologyIso _ n).symm)

end GlobalTheory.CompanionTheory.PointSurjectivity
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_slice_acyclic_of_truncation : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.CoverPoints

theorem exists_affine_cover_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  intro X _ F hF hc
  have hcl : ∀ G : Set X, G ⊆ F → IsClosed G := fun G hG => by
    have h := (hF.subset hG).isClosed_biUnion (fun x hx => hc x (hG hx))
    simpa using h

  have hW : ∀ x : F, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ ∀ y ∈ F, y ∈ W → y = x.1 := by
    intro x
    have hx : x.1 ∈ (F \ {x.1})ᶜ := fun h => h.2 rfl
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx
      (hcl _ Set.diff_subset).isOpen_compl
    refine ⟨W, hW, hxW, fun y hy hyW => ?_⟩
    by_contra hne
    exact hWo hyW ⟨hy, hne⟩
  choose W hWa hWx hWF using hW

  have hC : IsCompact ((⨆ x, W x : X.Opens) : Set X)ᶜ :=
    (⨆ x, W x : X.Opens).isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun U : {U : X.Opens // IsAffineOpen U ∧ ∀ x ∈ F, x ∉ U} => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro y hy
      have hy' : y ∈ Fᶜ := fun h => hy (by
        exact (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, h⟩, hWx ⟨y, h⟩⟩ : y ∈ (⨆ x, W x : X.Opens)))
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy'
        (hcl F subset_rfl).isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨U, hU, fun x hx hxU => hUo hxU hx⟩, hyU⟩)
  haveI : Fintype F := hF.fintype

  let V' : Option (F ⊕ s) → X.Opens := fun a => match a with
    | none => ⊥
    | some (Sum.inl x) => W x
    | some (Sum.inr U) => U.1.1
  have hV'a : ∀ a, IsAffineOpen (V' a) := by
    rintro (_ | x | U)
    · exact isAffineOpen_bot X
    · exact hWa x
    · exact U.1.2.1
  have hV'F : ∀ x (hx : x ∈ F) a, x ∈ V' a → a = some (Sum.inl ⟨x, hx⟩) := by
    rintro x hx (_ | y | U) h
    · exact absurd h (by simp [V'])
    · have : x = y.1 := hWF y x hx h
      subst this
      rfl
    · exact absurd h (U.1.2.2 x hx)
  let e : Option (F ⊕ s) ≃ Fin (Fintype.card (F ⊕ s) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨Fintype.card (F ⊕ s), fun j => V' (e.symm j), fun j => hV'a _, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hy : y ∈ (⨆ x, W x : X.Opens)
    · obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨e (some (Sum.inl x)), by simpa [V'] using hx⟩
    · obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs hy)
      exact ⟨e (some (Sum.inr ⟨U, hU⟩)), by simpa [V'] using hyU⟩
  · intro x hx i j hi hj
    exact e.symm.injective ((hV'F x hx _ hi).trans (hV'F x hx _ hj).symm)

end GlobalTheory.CompanionTheory.CoverPoints
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_separating_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFlat

theorem acyclic_extendScalars_of_bounded_flat : ∀ (R K : Type) [CommRing R] [CommRing K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p)) (hac : C.Acyclic), (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic :=
  fun _ _ _ _ χ C n hn hflat hac => GlobalTheory.AbLaw.acyclic_extendScalars_of_flat χ C n hn hflat hac

end GlobalTheory.CompanionTheory.PointSurjFlat
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_bounded_acyclic_base_change : ∀ (R K : Type) [CommRing R] [CommRing K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p)) (hac : C.Acyclic), (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PointSurjFlat.acyclic_extendScalars_of_bounded_flat
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjFibre

theorem cech_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  intro k _ X T Z a b p q H _ _ G hG R _ t Y π f Hy κ _ _ D hD hc hac s σ hs h₁ h₂
  obtain ⟨χ, rfl⟩ : ∃ χ : R →+* k, Spec.map (CommRingCat.ofHom χ) = s :=
    ⟨(Spec.preimage s).hom, by simp⟩
  have Hx : IsPullback (π ≫ p) f a (t ≫ b) := Hy.paste_horiz H
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) Hx inferInstance
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) Hx inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have Hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  obtain ⟨F, π', g, Hs⟩ : ∃ (F : Scheme.{0}) (π' : F ⟶ Y) (g : F ⟶ Spec (CommRingCat.of k)),
      IsPullback π' g f (Spec.map (CommRingCat.ofHom χ)) := ⟨_, _, _, Hs⟩
  have hext := GlobalTheory.T.flat_bounded_acyclic_base_change R k χ (cechLB f (G.pull π) D) (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hM hI) hac
  have hF : (cechLB g ((G.pull π).pull π') fun i => π' ⁻¹ᵁ D i).Acyclic :=
    fun n => (hext n).of_iso (cechLBBaseChangeIso hM Hs hI)
  have Hu : IsPullback (π' ≫ π ≫ p) g a (Spec.map (CommRingCat.ofHom χ) ≫ t ≫ b) :=
    Hs.paste_horiz Hx
  rw [hs] at Hu
  obtain ⟨u, hu⟩ : ∃ u : F ⟶ X, u = π' ≫ π ≫ p := ⟨_, rfl⟩
  rw [← hu] at Hu
  haveI : IsIso u := Hu.isIso_fst_of_isIso
  have hua : u ≫ a = g := Hu.w.trans (Category.comp_id _)
  have he : u ≫ σ = π' ≫ π := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, Category.comp_id, hu, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, hua, Category.assoc π', Hy.w, ← Category.assoc π',
        Hs.w, Category.assoc]
  refine ⟨fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i,
    fun i => (isAffineOpen_preimage_of_isPullback Hs (hD i)).preimage_of_isIso _, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]
    rfl
  · have hN := LB.isLB_pull hG σ
    obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) F u κ
      (fun i => inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) hN
      (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
    have hD' : (fun i => u ⁻¹ᵁ inv u ⁻¹ᵁ π' ⁻¹ᵁ D i) = fun i => π' ⁻¹ᵁ D i := funext fun i => by
      rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
      rfl
    rw [hua, hD'] at i₁
    obtain ⟨w₁, hw₁⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π π'
    obtain ⟨w₂, hw₂⟩ : ∃ w : LB.Iso ((G.pull σ).pull u) (G.pull (π' ≫ π)), w.IsGen :=
      he ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ u
    have hP := LB.isLB_pull hG (π' ≫ π)
    have i₂ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hM π') hP w₁ hw₁
    have i₃ := cechLBCongr g (fun i => π' ⁻¹ᵁ D i) (LB.isLB_pull hN u) hP w₂ hw₂
    exact fun n => (hF n).of_iso (i₂ ≪≫ i₃.symm ≪≫ i₁)

end GlobalTheory.CompanionTheory.PointSurjFibre
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem exists_acyclic_cechLB_fibre : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG F hF hfib htot y₀ σ₀ hy h₁ h₂
  have hsepa : IsSeparated a := inferInstance
  have hsepb : IsSeparated b := inferInstance
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have hT' : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have hcX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have hcT : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  have hpp : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H.flip inferInstance
  have hcZ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ a)
  have hsepZ : IsSeparated (p ≫ a) := inferInstance
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have huniv : ({q₀} : Set (Sp k)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have hclosed (y : Sp k ⟶ T) (hy : y ≫ b = 𝟙 _) : IsClosed ({y q₀} : Set T) := by
    have : IsClosedImmersion (y ≫ b) := by rw [hy]; infer_instance
    have : IsClosedImmersion y := IsClosedImmersion.of_comp y b
    rw [← Set.image_singleton]
    refine y.isClosedEmbedding.isClosedMap _ ?_
    rw [huniv]
    exact isClosed_univ
  let F₁ : Set T := (fun y : Sp k ⟶ T => y q₀) '' ({y ∈ F | y ≫ b = 𝟙 _} ∪ {y₀})
  have hF₁ : F₁.Finite := (((hF.subset (Set.sep_subset _ _))).union (Set.finite_singleton _)).image _
  have hF₁c : ∀ x ∈ F₁, IsClosed ({x} : Set T) := by
    rintro _ ⟨y, hyF | rfl, rfl⟩
    · exact hclosed y hyF.2
    · exact hclosed _ hy
  obtain ⟨r, V, hV, hVc, hV₁⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points T F₁ hF₁ hF₁c
  obtain ⟨m', B, hB, hBc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points X ∅ Set.finite_empty (by simp)
  obtain ⟨d, D, hD, hDc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points Z ∅ Set.finite_empty (by simp)
  let U : Fin (m' + 1) → Z.Opens := fun i => p ⁻¹ᵁ B i
  let W : Fin (r + 1) → Z.Opens := fun j => q ⁻¹ᵁ V j
  have hT : ∀ n, Limits.IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G _ D _ U _ W hG hsepZ hD hDc
      (by simp only [U]; rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by simp only [W]; rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
      (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
      (fun i j => (GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j) B hB hBc G hG).1 i) n
    have hz := ((htot _ D hD hDc) n).isZero_homology
    have := ModuleCat.subsingleton_of_isZero hz
    have := e.symm.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hA : ∀ t : Finset (Fin (r + 1)), 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)) t)).Acyclic := by
    intro t ht
    have hne : t.Nonempty := Finset.card_pos.1 (by omega)
    have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
      IsAffineOpen.biInf _ t.finite_toSet hne fun j _ => hV j
    obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H hVt B hB hBc G hG
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W t _
      (preimage_biInf V q t)
    obtain ⟨j₁, hj₁, j₂, hj₂, hne'⟩ := Finset.one_lt_card.1 ht
    have hfac := GlobalTheory.T.fibrewise_acyclicity_base_change a b p q H ha G hG Γ(T, ⨅ j ∈ t, V j) hVt.fromSpec Y π f Hy
      (fun s σ hs hσ₁ hσ₂ => hfib (s ≫ hVt.fromSpec) σ (by simpa using hs) hσ₁ hσ₂ (by
        intro hmem
        have hp : hVt.fromSpec (s q₀) ∈ (⨅ j ∈ t, V j : T.Opens) :=
          hVt.range_fromSpec.le ⟨_, rfl⟩
        have hx : (s ≫ hVt.fromSpec) q₀ ∈ F₁ :=
          ⟨_, Or.inl ⟨hmem, by simpa using hs⟩, rfl⟩
        have hp' : (s ≫ hVt.fromSpec) q₀ ∈ (⨅ j ∈ t, V j : T.Opens) := by simpa using hp
        exact hne' (hV₁ _ hx j₁ j₂ (biInf_le V hj₁ hp') (biInf_le V hj₂ hp'))))
    have h := hfac _ E hE hEc
    exact fun n => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h n).of_iso (i₁ ≪≫ i₂)
  obtain ⟨j₀, hj₀⟩ : ∃ j, y₀ q₀ ∈ V j := by
    have : y₀ q₀ ∈ (⨆ j, V j : T.Opens) := hVc ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcol := GlobalTheory.T.cech_slice_acyclic_of_truncation _ hA hT j₀
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j₀) B hB hBc G hG
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W {j₀} (q ⁻¹ᵁ V j₀)
    (by simp [W])
  have hac₁ : (cechLB (f ≫ (hV j₀).fromSpec ≫ b) (G.pull π) E).Acyclic :=
    fun n => (hcol n).of_iso (i₁ ≪≫ i₂).symm
  have hac : (cechLB f (G.pull π) E).Acyclic :=
    GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic _ f _ E hac₁
  have hrange : Set.range y₀ ⊆ Set.range (hV j₀).fromSpec := by
    rw [(hV j₀).range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = q₀ := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hj₀
  let s : Sp k ⟶ Spec Γ(T, V j₀) := IsOpenImmersion.lift (hV j₀).fromSpec y₀ hrange
  have hs : s ≫ (hV j₀).fromSpec = y₀ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨D', hD', hD'c, hD'a⟩ := GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic a b p q H G hG Γ(T, V j₀) (hV j₀).fromSpec Y π f Hy E hE hEc hac
    s σ₀ (by rw [← Category.assoc, hs]; exact hy) h₁ (by rw [hs]; exact h₂)
  exact ⟨m' + 1, D', hD', hD'c, hD'a⟩

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PointSurjectivity.exists_acyclic_cechLB_fibre
end
