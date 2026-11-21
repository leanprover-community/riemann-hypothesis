import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBTrans

variable {X : Scheme.{0}}

theorem res_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {U : X.Opens} (a b : Γ(X, U)ˣ)
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ res hW a = res hW b) : a = b := by
  let J := {W : X.Opens // ∃ hW : W ≤ U, res hW a = res hW b}
  have hc : U ≤ ⨆ j : J, j.1 := fun x hx => by
    obtain ⟨W, hW, hx', e⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, e⟩, hx'⟩
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun j : J => j.1) U (fun j => homOfLE j.2.1) hc _ _ (fun j => ?_)
  exact congrArg Units.val j.2.2

theorem glue_units {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

variable {C : Type} [Category.{0} C] {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
  {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ}

theorem res_quot (hu : IsCoc V hV u) {T₁ T₂ T T'' : C} (a : T₁ ⟶ T) (b : T₂ ⟶ T) (c : T ⟶ T'') :
    res (hV c) (u T₂ T b * (u T₁ T a)⁻¹) = u T₂ T'' (b ≫ c) * (u T₁ T'' (a ≫ c))⁻¹ := by
  rw [hu b c, hu a c, map_mul, map_inv, mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

theorem transition_units (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [thin : Quiver.IsThin C]
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) :
    IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ,
      ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  intro hB hu T₁ T₂
  have sub : ∀ {T T' : C} (f f' : T ⟶ T'), f = f' := fun f f' => @Subsingleton.elim _ (thin _ _) f f'
  let J := {T : C // Nonempty (T₁ ⟶ T) ∧ Nonempty (T₂ ⟶ T)}
  let W : J → X.Opens := fun j => V j.1
  have hW : ∀ j : J, W j ≤ V T₁ ⊓ V T₂ := fun j => le_inf (hV j.2.1.some) (hV j.2.2.some)
  let w : ∀ j : J, Γ(X, W j)ˣ := fun j => u T₂ j.1 j.2.2.some * (u T₁ j.1 j.2.1.some)⁻¹
  have hw : ∀ (j : J) (a : T₁ ⟶ j.1) (b : T₂ ⟶ j.1), w j = u T₂ j.1 b * (u T₁ j.1 a)⁻¹ :=
    fun j a b => by simp only [w]; rw [sub j.2.2.some b, sub j.2.1.some a]
  have hc : V T₁ ⊓ V T₂ ≤ iSup W := fun x hx => by
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨T, ⟨a⟩, ⟨b⟩⟩, hxT⟩
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (w i) = res inf_le_right (w j) := by
    intro i j
    apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨c⟩, ⟨d⟩, hxT, hle⟩ := hB.2 i.1 j.1 x (W i ⊓ W j) hx hx.1 hx.2
    refine ⟨V T, hle, hxT, ?_⟩
    rw [res_comp, res_comp]
    have e1 := res_quot hu i.2.1.some i.2.2.some c
    have e2 := res_quot hu j.2.1.some j.2.2.some d
    change res (hV c) (w i) = res (hV d) (w j)
    simp only [w]
    rw [e1, e2, sub (i.2.1.some ≫ c) (j.2.1.some ≫ d), sub (i.2.2.some ≫ c) (j.2.2.some ≫ d)]
  obtain ⟨s, hs⟩ := glue_units (V T₁ ⊓ V T₂) W hW hc w hh
  have key : ∀ (g : Γ(X, V T₁ ⊓ V T₂)ˣ) (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T),
      res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b ↔
        res (le_inf (hV a) (hV b)) g = u T₂ T b * (u T₁ T a)⁻¹ :=
    fun g T a b => (eq_mul_inv_iff_mul_eq).symm
  refine ⟨s, fun T a b => (key s T a b).2 ?_, fun g hg => ?_⟩
  · have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this
  · apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    refine ⟨V T, le_inf (hV a) (hV b), hxT, ?_⟩
    rw [(key g T a b).1 (hg T a b)]
    have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this.symm

end GlobalTheory.LBTrans
end
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ, ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  atlas_forward_decl GlobalTheory.LBTrans.transition_units
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThinGlue

variable {X : Scheme.{0}}

theorem res_res {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {W : X.Opens} (x y : Γ(X, W)ˣ)
    (h : ∀ p ∈ W, ∃ (W' : X.Opens) (hW : W' ≤ W), p ∈ W' ∧ res hW x = res hW y) : x = y := by
  choose W' hW hp hxy using h
  ext
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_
  · intro p hpW
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩
  · intro p
    have := congrArg Units.val (hxy p.1 p.2)
    exact this

end GlobalTheory.ThinGlue

namespace GlobalTheory.ThinGlue

theorem exists_lb_frame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  intro X C _ V hV _ u hB hC
  have hE := fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂
  choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists
  have key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂),
      res h (g T₁ T₂) * u T₁ S a = u T₂ S b := fun T₁ T₂ S a b _ => hg T₁ T₂ S a b
  have bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩ := hB.2 i j p W hp (hW hp).1 (hW hp).2
    exact ⟨V S, hSW, hpS, h S a b hSW⟩
  have bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j k W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩ := hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2
    obtain ⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩ := hB.2 S₀ k p W hp hpS₀ (hW hp).2
    exact ⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩
  have gself : ∀ T, g T T = 1 := fun T =>
    (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])
  let L : LB X := ⟨C, V, g⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨t, hp, _⟩ := hB.1 p ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩
  · intro T
    show res _ (g T T) = 1
    rw [gself, map_one]
  · intro i j k
    refine bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_
    show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))
    simp only [map_mul, res_res]
    have e1 := key i j S a b (hS.trans inf_le_left)
    have e2 := key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have e3 := key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    apply mul_right_cancel (b := u i S a)
    rw [e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]
  · refine ⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩
    · intro m m'
      refine bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))
      simp only [map_mul, res_res]
      have e1 := key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
      have e2 := key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have e3 := key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
      apply mul_right_cancel (b := u m S b)
      rw [e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]
    · intro T T' a m
      refine bas2 T' m _ le_rfl _ _ fun S c d hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))
      simp only [map_mul, res_res]
      have e1 := key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))
      have e2 := key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))
      have e3 := hC a c
      apply mul_right_cancel (b := u m S d)
      rw [e1, _root_.mul_assoc, e2, e3]

end GlobalTheory.ThinGlue
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  atlas_forward_decl GlobalTheory.ThinGlue.exists_lb_frame
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBObs

theorem gm_id_res' {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {x : X} (hx : x ∈ V) (a : Γ(X, U)ˣ) :
    gm (𝟙 X) x V (ReciprocityTheory.ChartRestriction.G.Semi.res hle a) = gm (𝟙 X) x U a :=
  gm_res (𝟙 X) x hle hx a

theorem lbIso_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (L L' : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → L.IsLB → L'.IsLB → IsFrame L V hV u → IsFrame L' V hV u → LBIso L L' := by
  intro X C _ V hV _ L L' u hB _ _ hF hF'
  obtain ⟨τ, hτg, hτ⟩ := hF
  obtain ⟨τ', hτ'g, hτ'⟩ := hF'

  have e : ∀ (T T' : C) (a : T ⟶ T') (m : L.ι) (x : X) (hx : x ∈ V T' ⊓ L.U m),
      gm (𝟙 X) x _ (τ T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L.U m)) (hτ T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h
  have e' : ∀ (T T' : C) (a : T ⟶ T') (m : L'.ι) (x : X) (hx : x ∈ V T' ⊓ L'.U m),
      gm (𝟙 X) x _ (τ' T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ' T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L'.U m)) (hτ' T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h

  have key : ∀ (T₁ T₂ : C) (m : L.ι) (m' : L'.ι) (x : X), x ∈ V T₁ → x ∈ V T₂ → x ∈ L.U m → x ∈ L'.U m' →
      gm (𝟙 X) x (V T₁ ⊓ L'.U m') (τ' T₁ m') / gm (𝟙 X) x (V T₁ ⊓ L.U m) (τ T₁ m) =
        gm (𝟙 X) x (V T₂ ⊓ L'.U m') (τ' T₂ m') / gm (𝟙 X) x (V T₂ ⊓ L.U m) (τ T₂ m) := by
    intro T₁ T₂ m m' x h1 h2 hm hm'
    obtain ⟨T₃, ⟨a⟩, ⟨b⟩, h3, -⟩ := hB.2 T₁ T₂ x ⊤ trivial h1 h2
    rw [e T₁ T₃ a m x ⟨h3, hm⟩, e' T₁ T₃ a m' x ⟨h3, hm'⟩, e T₂ T₃ b m x ⟨h3, hm⟩, e' T₂ T₃ b m' x ⟨h3, hm'⟩,
      mul_div_mul_left_eq_div, mul_div_mul_left_eq_div]

  have hglue : ∀ p : L'.ι × L.ι, ∃ s : Γ(X, L'.U p.1 ⊓ L.U p.2)ˣ, ∀ (T : C) (x : X),
      x ∈ V T → x ∈ L'.U p.1 ⊓ L.U p.2 →
        gm (𝟙 X) x _ s = gm (𝟙 X) x (V T ⊓ L'.U p.1) (τ' T p.1) / gm (𝟙 X) x (V T ⊓ L.U p.2) (τ T p.2) := by
    intro p
    obtain ⟨s, hs⟩ := glue_unit (L'.U p.1 ⊓ L.U p.2) (fun T => V T ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun T => inf_le_right)
      (fun x hx => by
        obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨T, hT, hx⟩)
      (fun T => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_left) (τ' T p.1) /
        ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_right) (τ T p.2))
      (fun T₁ T₂ x hx => by
        simp only [map_div]
        rw [gm_id_res' _ hx.1, gm_id_res' _ hx.1, gm_id_res' _ hx.2, gm_id_res' _ hx.2]
        exact key T₁ T₂ p.2 p.1 x hx.1.1 hx.2.1 hx.1.2.2 hx.1.2.1)
    refine ⟨s, fun T x hT hx => ?_⟩
    have h := congrArg (gm (𝟙 X) x (V T ⊓ (L'.U p.1 ⊓ L.U p.2))) (hs T)
    simp only [map_div] at h
    have hTx : x ∈ V T ⊓ (L'.U p.1 ⊓ L.U p.2) := ⟨hT, hx⟩
    rwa [gm_id_res' _ hTx, gm_id_res' _ hTx, gm_id_res' _ hTx] at h
  choose w hw using hglue
  refine ⟨⟨w⟩, fun p q => ?_⟩
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
  intro x hx
  obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
  have hp : x ∈ L'.U p.1 ⊓ L.U p.2 := hx.1
  have hq : x ∈ L'.U q.1 ⊓ L.U q.2 := hx.2

  have g1 := congrArg (gm (𝟙 X) x _) (hτ'g T p.1 q.1)
  have g2 := congrArg (gm (𝟙 X) x _) (hτg T p.2 q.2)
  have hx1 : x ∈ V T ⊓ L'.U p.1 ⊓ L'.U q.1 := ⟨⟨hT, hp.1⟩, hq.1⟩
  have hx2 : x ∈ V T ⊓ L.U p.2 ⊓ L.U q.2 := ⟨⟨hT, hp.2⟩, hq.2⟩
  rw [map_mul, gm_id_res' _ hx1, gm_id_res' _ hx1, gm_id_res' _ hx1] at g1
  rw [map_mul, gm_id_res' _ hx2, gm_id_res' _ hx2, gm_id_res' _ hx2] at g2
  have hwp : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U p) (w p)) =
      gm (𝟙 X) x ((L'.div L).U p) (w p) := gm_id_res' _ hx _
  have hwq : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U q) (w q)) =
      gm (𝟙 X) x ((L'.div L).U q) (w q) := gm_id_res' _ hx _
  have hx' : x ∈ L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2) := hx
  have hg : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q) ((L'.div L).g p q) =
      gm (𝟙 X) x (L'.U p.1 ⊓ L'.U q.1) (L'.g p.1 q.1) * (gm (𝟙 X) x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
    show gm (𝟙 X) x (L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2))
      (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L'.g p.1 q.1) * (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L.g p.2 q.2))⁻¹) = _
    rw [map_mul, map_inv, gm_id_res' _ hx', gm_id_res' _ hx']
  rw [map_mul, hwp, hwq, hg]
  erw [hw p T x hT hp, hw q T x hT hq]
  rw [g1, g2]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end GlobalTheory.LBObs
end
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isBas_of_preimage_eq (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (C : Type)
    [Category.{0} C] (V : C → X.Opens) (V₀ : C → X₀.Opens) (hV : ∀ T, i ⁻¹ᵁ V T = V₀ T) (h : IsBas V₀) :
    IsBas V := by
  have hle : ∀ (t : C) (U : X.Opens), V₀ t ≤ i ⁻¹ᵁ U → V t ≤ U := by
    intro t U htU z hz
    obtain ⟨w, rfl⟩ := i.surjective z
    have hw : w ∈ V₀ t := by rw [← hV t]; exact hz
    exact htU hw
  have hmem : ∀ (t : C) (y : X₀), y ∈ V₀ t → i y ∈ V t := by
    intro t y hy
    rw [← hV t] at hy
    exact hy
  have hmem' : ∀ (t : C) (y : X₀), i y ∈ V t → y ∈ V₀ t := by
    intro t y hy
    rw [← hV t]
    exact hy
  refine ⟨fun x U hx ↦ ?_, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t, hyt, htU⟩ := h.1 y (i ⁻¹ᵁ U) hx
    exact ⟨t, hmem t y hyt, hle t U htU⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t₃, a₁, a₂, hy₃, h₃U⟩ := h.2 t₁ t₂ y (i ⁻¹ᵁ U) hx (hmem' t₁ y h₁) (hmem' t₂ y h₂)
    exact ⟨t₃, a₁, a₂, hmem t₃ y hy₃, hle t₃ U h₃U⟩

end GlobalTheory.LBObs
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_squareZero_presented_scheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  first | exact @GlobalTheory.PresCharts.exists_charts | exact GlobalTheory.PresCharts.exists_charts | (intros; apply GlobalTheory.PresCharts.exists_charts <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

def unitOneSub {B : Type} [CommRing B] (w : B) (h : w * w = 0) : Bˣ where
  val := 1 - w
  inv := 1 + w
  val_inv := by linear_combination (-1 : B) * h
  inv_val := by linear_combination (-1 : B) * h

theorem unitOneSub_val {B : Type} [CommRing B] (w : B) (h : w * w = 0) : (unitOneSub w h : B) = 1 - w := rfl

theorem mul_eq_zero_of_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem lift_of_isObU_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u h
  obtain ⟨v, σ, z, hv, hσ, hz, hzv⟩ := h
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  have hw : ∀ (T T' : C) (a : T ⟶ T'), σ T' (f T T' a) ∈ I.map (algebraMap R (L.B T')) := fun T T' a ↦
    (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  refine ⟨fun T T' a ↦ v T T' a * unitOneSub (σ T' (f T T' a)) (mul_eq_zero_of_mem hI (hw T T' a) (hw T T' a)),
    fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · have h0 : L.p T' (σ T' (f T T' a)) = 0 := (L.ker T' _).2 (hw T T' a)
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one, h0, sub_zero, mul_one, hv]
    exact mul_one _
  · have hnat := (GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    have hs : σ T'' (z.1 T T' T'' a b) = L.ρ b (σ T' (f T T' a)) - σ T'' (f T T'' (a ≫ b)) + σ T'' (f T' T'' b) := by
      rw [← e, d1_apply, map_add, map_sub, hnat]
      rfl
    have hx := hw T T' a
    have hρx : L.ρ b (σ T' (f T T' a)) ∈ I.map (algebraMap R (L.B T'')) := by
      rw [hnat]
      exact (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
        (L.ker T'') (σ T'') (hσ T'')).1 _
    have hW := hw T T'' (a ≫ b)
    have hy := hw T' T'' b
    set x := L.ρ b (σ T' (f T T' a)) with hxdef
    set W := σ T'' (f T T'' (a ≫ b))
    set y := σ T'' (f T' T'' b)
    have hxx := mul_eq_zero_of_mem hI hρx hρx
    have hxy := mul_eq_zero_of_mem hI hρx hy
    have hyy := mul_eq_zero_of_mem hI hy hy
    have hWx := mul_eq_zero_of_mem hI hW hρx
    have hWy := mul_eq_zero_of_mem hI hW hy
    have key : (1 + (x - W + y)) * ((1 - x) * (1 - y)) = 1 - W := by
      linear_combination -hxx - hxy - hyy + hWx + hWy + y * hxx - y * hWx + y * hxy
    have hz' := (hzv T T' T'' a b).2
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one]
    rw [← hxdef]
    linear_combination (-(1 - x) * (1 - y)) * hz' + (-(v T T'' (a ≫ b) : L.B T'') * (1 - x) * (1 - y)) * hs
      - (v T T'' (a ≫ b) : L.B T'') * key

end GlobalTheory.LBLift
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  atlas_forward_decl GlobalTheory.LBLift.lift_of_isObU_zero
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := GlobalTheory.T.exists_charts_squareZero_presented_scheme R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  atlas_forward_decl GlobalTheory.LBObs.exists_lift_of_isObL_zero
end
