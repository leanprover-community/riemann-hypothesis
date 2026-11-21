import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.GrpPull
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.GeoSys
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.CompositeRestrictionPullInjective

section
set_option autoImplicit false

noncomputable section

namespace MainStatements.Hodge.Pf.WedgeProjections

section

variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V)

def theta (g : Fin 2 → Module.Dual K V) : Module.Dual K (⋀[K]^2 W) :=
  exteriorPower.pairingDual K W 2 (exteriorPower.ιMulti K 2 ![g 0 ∘ₗ r₁, g 1 ∘ₗ r₂])

theorem theta_ιMulti (g : Fin 2 → Module.Dual K V) (v : Fin 2 → W) :
    theta r₁ r₂ g (exteriorPower.ιMulti K 2 v) =
      g 0 (r₁ (v 0)) * g 1 (r₂ (v 1)) - g 1 (r₂ (v 0)) * g 0 (r₁ (v 1)) := by
  simp [theta, Matrix.det_fin_two]

end

theorem key_alg {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id) (h12 : r₁ ∘ₗ q = 0)
    (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by
  classical
  have e11 : ∀ x, r₁ (p x) = x := fun x => LinearMap.congr_fun h11 x
  have e12 : ∀ x, r₁ (q x) = 0 := fun x => LinearMap.congr_fun h12 x
  have e21 : ∀ x, r₂ (p x) = 0 := fun x => LinearMap.congr_fun h21 x
  have e22 : ∀ x, r₂ (q x) = x := fun x => LinearMap.congr_fun h22 x
  have hkill : ∀ g : Fin 2 → Module.Dual K V,
      exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 g) t = 0 := by
    intro g
    have hA : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 (p + q) =
        exteriorPower.pairingDual K V 2 (exteriorPower.ιMulti K 2 g) := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e11, e12, e21, e22, Matrix.det_fin_two]
    have hB : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 p = 0 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e21]
    have hC : (theta r₁ r₂ g) ∘ₗ exteriorPower.map 2 q = 0 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [theta_ιMulti, exteriorPower.map_apply_ιMulti, e12]
    have h0 := congrArg (theta r₁ r₂ g) ht
    rw [map_add] at h0
    have h1 := LinearMap.congr_fun hA t
    have h2 := LinearMap.congr_fun hB t
    have h3 := LinearMap.congr_fun hC t
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2 h3
    rw [← h1, h0, h2, h3, add_zero]
  obtain ⟨I, b⟩ := Module.Free.exists_basis K V
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  apply (b.exteriorPower 2).ext_elem
  intro s
  rw [exteriorPower.basis_repr_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact hkill _

end MainStatements.Hodge.Pf.WedgeProjections
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

theorem affInf {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

@[reducible] def pairSL {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (hX : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hX' : ∀ U V : X'.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) :
    SemilatticeInf (Pair φ) :=
  { (inferInstance : PartialOrder (Pair φ)) with
    inf := fun p q ↦ ⟨(⟨p.1.1.1 ⊓ q.1.1.1, hX' _ _ p.1.1.2 q.1.1.2⟩, ⟨p.1.2.1 ⊓ q.1.2.1, hX _ _ p.1.2.2 q.1.2.2⟩),
      by
        show p.1.1.1 ⊓ q.1.1.1 ≤ φ ⁻¹ᵁ (p.1.2.1 ⊓ q.1.2.1)
        rw [Scheme.Hom.preimage_inf]
        exact inf_le_inf p.2 q.2⟩
    inf_le_left := fun p q ↦ ⟨(inf_le_left : p.1.1.1 ⊓ q.1.1.1 ≤ p.1.1.1), (inf_le_left : p.1.2.1 ⊓ q.1.2.1 ≤ p.1.2.1)⟩
    inf_le_right := fun p q ↦ ⟨(inf_le_right : p.1.1.1 ⊓ q.1.1.1 ≤ q.1.1.1), (inf_le_right : p.1.2.1 ⊓ q.1.2.1 ≤ q.1.2.1)⟩
    le_inf := fun a b c hab hac ↦ ⟨(le_inf hab.1 hac.1 : a.1.1.1 ≤ b.1.1.1 ⊓ c.1.1.1),
      (le_inf hab.2 hac.2 : a.1.2.1 ≤ b.1.2.1 ⊓ c.1.2.1)⟩ }

theorem pair_cover {X X' : Scheme.{0}} (φ : X' ⟶ X) : ⨆ p : Pair φ, p.1.1.1 = ⊤ := by
  refine eq_top_iff.2 (fun x _ => ?_)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens)
    (show x ∈ φ ⁻¹ᵁ V from hxV)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩

theorem pairRes_pull2_injective (hD : DescentSt) (hL : LowSt) {R : Type} [CommRing R] {X X' : Scheme.{0}}
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (hs : IsSeparated s) (hs' : IsSeparated s') :
    Function.Injective (pairRes φ s').pull2 := by
  letI : SemilatticeInf (Pair φ) := pairSL φ (affInf s hs) (affInf s' hs')
  let S : Sys X' (Pair φ) := ⟨fun p => p.1.1, fun _ _ => rfl, pair_cover φ⟩
  have hq : AllQIso (pairRes φ s') := hD R X' s' hs' (Pair φ) S
  exact (hL R _ _ _ _ (pairRes φ s') hq).2.1.1

end MainStatements.Hodge.Pf.WedgeProjections
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R]

theorem pullback_wedge_cup_square {Y Z : Over (Sp R)} (f : Y ⟶ Z)
    (eZ : ⋀[R]^2 (HO1 Z.hom) ≃ₗ[R] H2 (OAff Z.hom))
    (hZ : ∀ a b, eZ (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Z.hom) a b)
    (eY : ⋀[R]^2 (HO1 Y.hom) ≃ₗ[R] H2 (OAff Y.hom))
    (hY : ∀ a b, eY (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Y.hom) a b) (t : ⋀[R]^2 (HO1 Z.hom)) :
    IsPullbackH2Structure (wOver f) (eZ t) (eY (exteriorPower.map 2 (AXO.pO f) t)) := by
  unfold IsPullbackH2Structure
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := HO1 Z.hom))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    have hv2 : (⇑(AXO.pO f) ∘ ![v 0, v 1]) = ![AXO.pO f (v 0), AXO.pO f (v 1)] := by
      ext i
      fin_cases i <;> rfl
    have h0 : (pairPull (wOver f)).pull1 (v 0) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 0)) :=
      (AXO.pO_spec f (v 0) _).2 rfl
    have h1 : (pairPull (wOver f)).pull1 (v 1) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 1)) :=
      (AXO.pO_spec f (v 1) _).2 rfl
    rw [hv, exteriorPower.map_apply_ιMulti, hv2, hZ, hY, CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, h0, h1]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    simp only [map_smul, map_smulₛₗ, RingHom.id_apply]
    rw [hx]

end MainStatements.Hodge.Pf.WedgeProjections
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]

theorem pO_one {Y : Over (Sp R)} (x : HO1 A.hom) : AXO.pO (1 : Y ⟶ A) x = 0 := by
  rw [Hom.one_def, AXO.pO_comp, AXO.HO1_base_eq_zero (AXO.pO _ x), map_zero]

theorem pO_mul (hAx : AxOSt) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    AXO.pO (fst A A * snd A A) = AXO.pO (fst A A) + AXO.pO (snd A A) := by
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.one_mul]
  apply LinearMap.ext
  intro x
  rw [LinearMap.add_apply]
  have hc := hAx R A g hA hg
    (AXO.pO (fst A A * snd A A) x - AXO.pO (fst A A) x - AXO.pO (snd A A) x)
    ((AXO.pO_spec (lift (𝟙 A) (1 : A ⟶ A)) _ _).2 ?_) ((AXO.pO_spec (lift (1 : A ⟶ A) (𝟙 A)) _ _).2 ?_)
  · rw [sub_sub, sub_eq_zero] at hc
    exact hc
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e1, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e2, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_zero, sub_self]

theorem r11 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (fst A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, AXO.pO_id]; rfl

theorem r12 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (snd A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, pO_one]; rfl

theorem r21 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (fst A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, pO_one]; rfl

theorem r22 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (snd A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, AXO.pO_id]; rfl

end MainStatements.Hodge.Pf.WedgeProjections
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

theorem eq_zero_of_exteriorPower_map_add {K : Type} [CommRing K] (hK : IsField K) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id)
    (h12 : r₁ ∘ₗ q = 0) (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by
  letI := hK.toField
  exact key_alg p q r₁ r₂ h11 h12 h21 h22 t ht

end MainStatements.Hodge.Pf.WedgeProjections

theorem MainStatements.Hodge.Pf.noprim : DescentSt → LowSt → SteinSt → AxOSt → WedgeFieldSt → NoPrimSt := by
  intro hD hL _ hAx hW R _ A _ g hA hg hR z a b c ha hb hc habc
  obtain ⟨eZ, hZ⟩ := hW R A g hA hg hR
  obtain ⟨eY, hY⟩ := hW R (A ⊗ A) (g + g) (MainStatements.Hodge.Sh.isAbelianScheme_tensor' A A hA hA)
    (MainStatements.Hodge.Sh.smooth_tensor hg hg) hR
  have hsep : IsSeparated A.hom := by have := hA.proper; infer_instance
  have hsep2 : IsSeparated (A ⊗ A).hom := MainStatements.Hodge.Pf.AXO.sep_tensor A
  have inj : ∀ f : A ⊗ A ⟶ A, Function.Injective (pairRes f.left (A ⊗ A).hom).pull2 := fun f ↦
    MainStatements.Hodge.Pf.WedgeProjections.pairRes_pull2_injective hD hL A.hom (A ⊗ A).hom f.left hsep hsep2
  obtain ⟨t, rfl⟩ := eZ.surjective z
  have e : ∀ (f : A ⊗ A ⟶ A) (a' : GlobalTheory.CatCoh.H2 (OAff (A ⊗ A).hom)), IsPullbackH2Structure (wOver f) (eZ t) a' →
      a' = eY (exteriorPower.map 2 (MainStatements.Hodge.Pf.AXO.pO f) t) := fun f a' h' ↦
    inj f (h'.symm.trans (MainStatements.Hodge.Pf.WedgeProjections.pullback_wedge_cup_square f eZ hZ eY hY t))
  rw [e _ _ ha, e _ _ hb, e _ _ hc, ← map_add] at habc
  have ht := eY.injective habc
  rw [MainStatements.Hodge.Pf.WedgeProjections.pO_mul A hAx g hA hg] at ht
  rw [MainStatements.Hodge.Pf.WedgeProjections.eq_zero_of_exteriorPower_map_add hR _ _ _ _ (MainStatements.Hodge.Pf.WedgeProjections.r11 A) (MainStatements.Hodge.Pf.WedgeProjections.r12 A)
    (MainStatements.Hodge.Pf.WedgeProjections.r21 A) (MainStatements.Hodge.Pf.WedgeProjections.r22 A) t ht, map_zero]
end
end
