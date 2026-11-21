import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSymLiftCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

theorem isOpen_component {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have key : (connectedComponent x)ᶜ =
      ⋃₀ {Z | Z ∈ irreducibleComponents X ∧ Disjoint Z (connectedComponent x)} := by
    ext y
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      apply hy
      have hirr : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
      have hsub : irreducibleComponent y ⊆ connectedComponent z :=
        IsPreconnected.subset_connectedComponent (IsPreirreducible.isPreconnected hirr.2) hz
      rw [connectedComponent_eq hzx]
      exact hsub mem_irreducibleComponent
    · rintro ⟨Z, ⟨_, hdisj⟩, hyZ⟩ hyx
      exact Set.disjoint_left.mp hdisj hyZ hyx
  have hcl : IsClosed (connectedComponent x)ᶜ := by
    rw [key, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion (hfin.subset fun Z hZ => hZ.1)
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.mp hcl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} (Xo : Moduli D l)

theorem moduli_noeth : IsLocallyNoetherian Xo.X := by
  obtain ⟨N, i, hi, -, hs⟩ := Xo.qproj
  haveI := hi
  haveI := isProper_str (KA l) N
  haveI : LocallyOfFiniteType Xo.s := by
    rw [← hs]
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem univ_isAb : IsAbelianScheme Xo.univ.t.G :=
  ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩

set_option backward.isDefEq.respectTransparency false in
theorem mulNFin (hM : MulNSt) {N : ℕ} (hN : 1 ≤ N) :
    IsFinite (mulA Xo.univ.t.G N).left ∧ Flat (mulA Xo.univ.t.G N).left ∧ Surjective (mulA Xo.univ.t.G N).left := by
  have := moduli_noeth Xo
  have loc : ∀ y : Xo.univ.t.G.left, ∃ (Y : Scheme.{0}) (φ : Y ⟶ Xo.univ.t.G.left) (m : Y ⟶ Y), IsOpenImmersion φ ∧ (∃ z : Y, φ z = y) ∧
      IsPullback φ m (mulA Xo.univ.t.G N).left φ ∧ IsFinite m ∧ Flat m ∧ Surjective m := fun y => by
    obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤) (x := Xo.univ.t.G.hom y) trivial
    have : IsAffine U := hU
    have : IsNoetherian U.toScheme := {}
    have : NoetherianSpace U.toScheme := inferInstance
    let V : U.toScheme.Opens := ⟨_, isOpen_component (X := U.toScheme) ⟨_, hy⟩⟩
    have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    obtain ⟨t, ⟨m⟩⟩ := exists_sab (V.ι ≫ U.ι) Xo.univ.t
    have := t.semi.smooth
    have := t.semi.geomConnected
    obtain ⟨w, gw', -⟩ := m.lin
    have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 y ⟨⟨_, hy⟩, mem_connectedComponent⟩ rfl
    obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom z
    obtain ⟨-, ws, gs', -⟩ := t.sym
    obtain ⟨a, b, c, -⟩ := hM _
      { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB
        ample := relAmple_pull m.cart.1 Xo.univ.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') U hU (fun y => (V.ι y).2) Xo.univ.ample
        ktriv := kTriv_pull m.cart Xo.univ.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') Xo.univ.ktriv
        isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ‹_›⟩
        rigid := ⟨t.PP.rig, t.PP.rigGen⟩
        sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } N hN
    have sq : m.φ ≫ (mulA Xo.univ.t.G N).left = (mulA t.G N).left ≫ m.φ := by
      have e := congrArg (fun q => q.left) (map_pow (pushHom m.cart t.G) (𝟙 t.G) N)
      have e' := congrArg (fun q => q.left) (MonObj.comp_pow (𝟙 Xo.univ.t.G) N (pushHom m.cart t.G (𝟙 t.G)))
      rw [Category.comp_id] at e'
      exact (congrArg (· ≫ _) (Category.id_comp m.φ).symm).trans (e'.trans e.symm)
    exact ⟨_, m.φ, _, MorphismProperty.of_isPullback (P := @IsOpenImmersion) m.cart.1.flip inferInstance, ⟨z, hz⟩,
      (IsPullback.of_bot (by rw [Over.w, Over.w]; exact m.cart.1) sq m.cart.1), a, b, c⟩
  choose Y φ m o c H a b s using loc
  let 𝒰 : Xo.univ.t.G.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) _ Y φ (fun y => ⟨y, c y⟩) o
  have key : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P], (∀ y, P (m y)) → P (mulA Xo.univ.t.G N).left :=
    fun P _ h => IsZariskiLocalAtTarget.of_openCover (𝒰 := 𝒰) fun y =>
      show P (pullback.snd (mulA Xo.univ.t.G N).left (φ y)) from
        (H y).isoPullback_inv_snd ▸ (P.cancel_left_of_respectsIso (H y).isoPullback.inv (m y)).2 (h y)
  exact ⟨key @IsFinite.{0} a, key @Flat.{0} b, key @Surjective.{0} s⟩




end ReciprocityTheory.ChartRestriction.G.Geo.Tor
