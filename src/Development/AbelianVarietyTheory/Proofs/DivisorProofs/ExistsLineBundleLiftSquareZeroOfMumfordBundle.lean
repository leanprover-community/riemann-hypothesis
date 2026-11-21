import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.FrameCoc

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCoc_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  intro X C _ V hV L u hL hF T T' T'' a b
  obtain ⟨τ, -, hτ⟩ := hF
  have key : ∀ m : L.ι, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (res (hV b) (u T T' a) * u T' T'' b) := by
    intro m
    have h1 := hτ T T'' (a ≫ b) m
    have h2 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (hτ T T' a m)
    have h3 := hτ T' T'' b m
    rw [res_res', map_mul, res_res', h3] at h2
    rw [h1] at h2
    apply mul_right_cancel (b := τ T'' m)
    rw [h2, map_mul, res_res', ← _root_.mul_assoc]
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun m => V T'' ⊓ L.U m) (V T'') (fun m => homOfLE inf_le_left) ?_ _ _ ?_
  · rw [← inf_iSup_eq, hL.cover, inf_top_eq]
  · intro m
    exact congrArg Units.val (key m)

end GlobalTheory.LBObs.FrameCoc
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  atlas_forward_decl GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBFrameEx

variable {X : Scheme.{0}}

private theorem res_res' {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem coc {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens} (h₁ : W ≤ L.U i ⊓ L.U j)
    (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have := congrArg (res hW) (hL.cocycle i j k)
  rwa [map_mul, res_res', res_res', res_res'] at this

structure Ch (L : LB X) where
  U : X.affineOpens
  m : L.ι
  le : (U : X.Opens) ≤ L.U m

instance (L : LB X) : Preorder (Ch L) where
  le a b := (b.U : X.Opens) ≤ a.U
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h'.trans h

abbrev opF (L : LB X) : Ch L ⥤ AffOp X where
  obj T := Opposite.op T.U
  map a := (homOfLE (leOfHom a)).op

def unit (L : LB X) (T T' : Ch L) (a : T ⟶ T') : Γ(X, opOf (opF L) T')ˣ :=
  res (le_inf T'.le ((show (T'.U : X.Opens) ≤ T.U from leOfHom a).trans T.le) : (T'.U : X.Opens) ≤ L.U T'.m ⊓ L.U T.m) (L.g T'.m T.m)

def gen (L : LB X) (T : Ch L) (m : L.ι) : Γ(X, opOf (opF L) T ⊓ L.U m)ˣ :=
  res (le_inf inf_le_right (inf_le_left.trans T.le) : (T.U : X.Opens) ⊓ L.U m ≤ L.U m ⊓ L.U T.m) (L.g m T.m)

theorem isBas (L : LB X) (hL : L.IsLB) : IsBas (opOf (opF L)) := by
  have hch : ∀ x : X, ∃ m, x ∈ L.U m := fun x => by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  refine ⟨fun x U hx => ?_, fun t₁ t₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨m, hm⟩ := hch x
    obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ L.U m from ⟨hx, hm⟩)
    exact ⟨⟨⟨V, hV⟩, m, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩
  · obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ (opOf (opF L) t₁ ⊓ opOf (opF L) t₂) from ⟨hx, h₁, h₂⟩)
    refine ⟨⟨⟨V, hV⟩, t₁.m, (hVU.trans inf_le_right).trans (inf_le_left.trans t₁.le)⟩,
      ⟨homOfLE ?_⟩, ⟨homOfLE ?_⟩, hxV, hVU.trans inf_le_left⟩
    · exact (hVU.trans inf_le_right).trans inf_le_left
    · exact (hVU.trans inf_le_right).trans inf_le_right

theorem isFrame (L : LB X) (hL : L.IsLB) : IsFrame L (opOf (opF L)) (opOf_le (opF L)) (unit L) := by
  refine ⟨gen L, fun T m m' => ?_, fun T T' a m => ?_⟩
  · simp only [gen]
    rw [res_res', res_res']
    exact (coc hL m m' T.m _ _ _).symm
  · simp only [gen, unit]
    rw [res_res', res_res']
    rw [mul_comm]
    exact (coc hL m T'.m T.m _ _ _).symm

theorem exists_frame : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C)
    (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ),
    IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u :=
  fun X L hL => ⟨Ch L, inferInstance, fun _ _ => inferInstance, opF L, unit L, isBas L hL, isFrame L hL⟩

end GlobalTheory.LBFrameEx
end
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C) (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ), IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u := by
  atlas_forward_decl GlobalTheory.LBFrameEx.exists_frame
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem exists_isObU : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u hL hu
  have hmul : ∀ T (x y : L.B T), x ∈ I.map (algebraMap R (L.B T)) → y ∈ I.map (algebraMap R (L.B T)) →
      x * y = 0 := by
    intro T x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    rw [← pow_two, ← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
    exact (Ideal.mem_bot).1 h
  have hv : ∀ (T T' : C) (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' (v : L.B T') = (u T T' a : F.obj T') := by
    intro T T' a
    obtain ⟨x, hx⟩ := L.surj T' (u T T' a : F.obj T')
    obtain ⟨y, hy⟩ := L.surj T' (↑(u T T' a)⁻¹ : F.obj T')
    have hn : x * y - 1 ∈ I.map (algebraMap R (L.B T')) := by
      rw [← L.ker T', map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
    have hn2 := hmul T' _ _ hn hn
    exact ⟨⟨x, y * (1 - (x * y - 1)), by linear_combination (-1 : L.B T') * hn2,
      by linear_combination (-1 : L.B T') * hn2⟩, hx⟩
  choose v hvp using hv
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hbas := fun T ↦ sig_basic R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
    (L.ker T) (σ T) (hσ T)
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * ↑(v T T'' (a ≫ b))⁻¹ - 1 := by
    intro T T' T'' a b
    refine (hbas T'').2.2.2 _ ?_
    have hpinv : L.p T'' ↑(v T T'' (a ≫ b))⁻¹ = ↑(u T T'' (a ≫ b))⁻¹ :=
      Units.eq_inv_of_mul_eq_one_left (by rw [← hvp, ← map_mul, Units.mul_inv, map_one])
    rw [← L.ker T'', map_sub, map_mul, map_mul, map_one, L.nat, hvp, hvp, hpinv, ← hu a b, Units.mul_inv, sub_self]
  choose z hzK hzσ using hz
  have heq : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''),
      L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'') := by
    intro T T' T'' a b
    rw [hzσ, add_sub_cancel, mul_assoc _ _ (v T T'' (a ≫ b) : L.B T''), Units.inv_mul, _root_.mul_one]
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]
    · have m1 : L.ρ c (σ T'' (z T T' T'' a b)) ∈ I.map (algebraMap R (L.B T''')) := by
        rw [nat.1]; exact (hbas T''').1 _
      have m2 := (hbas T''').1 (z T T'' T''' (a ≫ b) c)
      have m3 := (hbas T''').1 (z T T' T''' a (b ≫ c))
      have m4 := (hbas T''').1 (z T' T'' T''' b c)
      have h12 := hmul T''' _ _ m1 m2
      have h43 := hmul T''' _ _ m4 m3
      have hA := congrArg (L.ρ c) (heq T T' T'' a b)
      rw [map_mul, map_mul, map_add, map_one] at hA
      have hB := heq T T'' T''' (a ≫ b) c
      have hC := heq T T' T''' a (b ≫ c)
      have hD := heq T' T'' T''' b c
      have hF := hL b c (v T T' a : L.B T')
      rw [Category.assoc] at hB
      rw [em, map_sub, map_add, map_add, ← nat.1]
      set E1 := L.ρ c (σ T'' (z T T' T'' a b))
      set E2 := σ T''' (z T T'' T''' (a ≫ b) c)
      set E3 := σ T''' (z T T' T''' a (b ≫ c))
      set E4 := σ T''' (z T' T'' T''' b c)
      set V := v T T''' (a ≫ b ≫ c)
      have hVW : (V : L.B T''') * ↑V⁻¹ = 1 := Units.mul_inv V
      have key1 : (1 + E1) * (1 + E2) * (V : L.B T''') = (1 + E4) * (1 + E3) * (V : L.B T''') := by
        linear_combination (-(1 + E1)) * hB - (v T'' T''' c : L.B T''') * hA + (1 + E4) * hC
          + L.ρ (b ≫ c) (v T T' a : L.B T') * hD
          - L.ρ c (v T' T'' b : L.B T'') * (v T'' T''' c : L.B T''') * hF
      have key2 : (1 + E1) * (1 + E2) = (1 + E4) * (1 + E3) := by
        linear_combination (↑V⁻¹ : L.B T''') * key1 - ((1 + E1) * (1 + E2) - (1 + E4) * (1 + E3)) * hVW
      linear_combination key2 - h12 + h43
  refine ⟨H2.mk _ ⟨_, hZ⟩, v, σ, ⟨_, hZ⟩, hvp, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, heq T T' T'' a b⟩⟩

end GlobalTheory.LBObs
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCocycleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  atlas_forward_decl GlobalTheory.LBObs.exists_isObU
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.ObEx

theorem exists_isObL : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L hL
  obtain ⟨C, _, _, G, u, hB, hF⟩ := GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis X₀ L hL
  have hc := GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis X₀ C (opOf G) (opOf_le G) L u hL hF
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_unitCocycleLiftObstruction R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u
    ((ofSys_isFun S).restrict G) (fun T T' T'' a b ↦ congrArg Units.val (hc a b))
  obtain ⟨c, rfl⟩ := (GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X₀ s₀ C G hB.1 hB.2).2.2 d
  exact ⟨c, C, inferInstance, inferInstance, G, hB, u, hF, hd⟩

end GlobalTheory.LBObs.ObEx
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  atlas_forward_decl GlobalTheory.LBObs.ObEx.exists_isObL
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

structure CommonRef {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C']
    (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X) : Type where

  t : C

  t' : C'

  W : X.affineOpens
  le : W.1 ≤ opOf G t
  le' : W.1 ≤ opOf G' t'

namespace CommonRef

variable {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C']
  {G : C ⥤ AffOp X} {G' : C' ⥤ AffOp X}

instance : Category.{0} (CommonRef G G') where
  Hom a b := (a.t ⟶ b.t) × (a.t' ⟶ b.t') × PLift (b.W.1 ≤ a.W.1)
  id a := (𝟙 _, 𝟙 _, ⟨le_rfl⟩)
  comp f g := (f.1 ≫ g.1, f.2.1 ≫ g.2.1, ⟨g.2.2.down.trans f.2.2.down⟩)
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance : Quiver.IsThin (CommonRef G G') := fun a b =>
  ⟨fun f g => Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

variable (G G')

def fst : CommonRef G G' ⥤ C where
  obj d := d.t
  map f := f.1

def snd : CommonRef G G' ⥤ C' where
  obj d := d.t'
  map f := f.2.1

def opn : CommonRef G G' ⥤ AffOp X where
  obj d := Opposite.op d.W
  map f := (homOfLE f.2.2.down).op

def toFst : fst G G' ⋙ G ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G.obj d.t).unop from d.le)).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def toSnd : snd G G' ⋙ G' ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G'.obj d.t').unop from d.le')).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem isBas (hG : IsBas (opOf G)) (hG' : IsBas (opOf G')) : IsBas (opOf (opn G G')) := by
  refine ⟨fun x U hx => ?_, fun d₁ d₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨t, hxt, htU⟩ := hG.1 x U hx
    obtain ⟨t', hxt', ht'⟩ := hG'.1 x (opOf G t ⊓ U) ⟨hxt, hx⟩
    exact ⟨⟨t, t', (G'.obj t').unop, ht'.trans inf_le_left, le_rfl⟩, hxt', ht'.trans inf_le_right⟩
  · have hx₃ : x ∈ U ⊓ d₁.W.1 ⊓ d₂.W.1 := ⟨⟨hx, h₁⟩, h₂⟩
    obtain ⟨t, a₁, a₂, hxt, htU⟩ := hG.2 d₁.t d₂.t x _ hx₃ (d₁.le h₁) (d₂.le h₂)
    obtain ⟨t', b₁, b₂, hxt', ht'⟩ := hG'.2 d₁.t' d₂.t' x (opOf G t) hxt (d₁.le' h₁) (d₂.le' h₂)
    refine ⟨⟨t, t', (G'.obj t').unop, ht', le_rfl⟩, ⟨(a₁.some, b₁.some, ⟨?_⟩)⟩, ⟨(a₂.some, b₂.some, ⟨?_⟩)⟩, hxt', ?_⟩
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_right))
    · exact ht'.trans (htU.trans inf_le_right)
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_left))

end CommonRef

theorem common_refinement : ∀ (X : Scheme.{0}) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ AffOp X) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K) ∧ Nonempty (H' ⋙ G' ⟶ K) ∧ IsBas (opOf K) :=
  fun X C C' _ _ _ _ G G' hG hG' =>
    ⟨CommonRef G G', inferInstance, inferInstance, CommonRef.opn G G', CommonRef.fst G G', CommonRef.snd G G',
      ⟨CommonRef.toFst G G'⟩, ⟨CommonRef.toSnd G G'⟩, CommonRef.isBas G G' hG hG'⟩

end GlobalTheory.LBObs
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  atlas_forward_decl GlobalTheory.LBObs.isFrame_tens
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

section Additive

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
  [Algebra R₀ R₁]

theorem sig_mem_map (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (y : R₁ ⊗[R₀] B₀) :
    σ y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sig_one_add_mul (hI : I ^ 2 = 0) (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (z z' : R₁ ⊗[R₀] B₀) : (1 + σ z) * (1 + σ z') = 1 + σ (z + z') := by
  have h0 : σ z * σ z' = 0 := by
    have hm := Ideal.mul_mem_mul (sig_mem_map α p hp σ hσ z) (sig_mem_map α p hp σ hσ z')
    rw [← Ideal.map_mul, ← sq, hI, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (Submodule.mem_bot _).1 hm
  rw [map_add]
  linear_combination h0

end Additive

theorem isObU_mul : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u' c' → IsObU L α (fun T T' a ↦ u T T' a * u' T T' a) (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  refine ⟨fun T T' a ↦ v T T' a * v' T T' a, σ, z + z', fun T T' a ↦ ?_, hσ, (map_add _ _ _).symm,
    fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · simp only [Units.val_mul, map_mul, hv, hv']
  · have h1 := (hz T T' T'' a b).1
    have h2 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at h1 h2 ⊢
    change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (z.1 T T' T'' a b + z'.1 T T' T'' a b) = 0
    rw [map_add, h1, h2, add_zero]
  · have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    have hs : σ' T'' (z'.1 T T' T'' a b) = σ T'' (z'.1 T T' T'' a b) :=
      sig_unique α (L.p T'') (L.surj T'') _ _ (hσ' T'') (hσ T'') _
    rw [hs] at e'
    change _ = (1 + σ T'' (z.1 T T' T'' a b + z'.1 T T' T'' a b)) * _
    rw [← sig_one_add_mul hI α (L.p T'') (L.surj T'') (σ T'') (hσ T'')]
    simp only [Units.val_mul, map_mul]
    calc L.ρ b (v T T' a : L.B T') * L.ρ b (v' T T' a : L.B T') * ((v T' T'' b : L.B T'') * (v' T' T'' b : L.B T''))
        = (L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'')) *
            (L.ρ b (v' T T' a : L.B T') * (v' T' T'' b : L.B T'')) := by ring
      _ = _ := by rw [e, e']; ring

end GlobalTheory.LBObs
end
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_tensor_additive : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  atlas_forward_decl GlobalTheory.LBObs.isObL_tens
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_any_ring : PrimitiveExtendedDegTwoVanish := by
  apply GlobalTheory.T.primitive_degree_two_extension
  apply GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish
  intro R _ A _ g hA hs
  obtain ⟨⟨hfin, hproj, hrk⟩, hw, -, -⟩ := GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs
  exact ⟨⟨hfin, hproj, hrk⟩, hw⟩

end GlobalTheory.Obs
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  atlas_forward_decl GlobalTheory.Obs.primE2_any_ring
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_group_scheme_pullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  atlas_forward_decl GlobalTheory.SqPull.sq_of_grpPullback
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_lam_iso_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ _ π hπ hI B _ B₀ _ _ i i₂ hB hgp hsq P L₀ hP hL₀ hΛ
  have hab : IsAbelianScheme B₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hgp
  obtain ⟨g, hdim⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ B₀ hab
  have hsm : Smooth B.hom := hB.smooth
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ (RingHom.ker π) hI π hπ rfl
  have hpb : IsPullback i B₀.hom B.hom (spMap π) := hgp.1
  obtain ⟨S, ⟨Pr⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl B₀.left B₀.hom B.left B.hom i hpb hsm
  obtain ⟨k, hkp, hkμ, hkf, hks⟩ := GlobalTheory.T.exists_square_group_scheme_pullback (Sp R) (Sp R₀) (spMap π) B B₀ i hgp
  have hki : i₂ = k := (GlobalTheory.SqPull.tensor_isPullback B B).hom_ext (hsq.1.trans hkf.symm) (hsq.2.trans hks.symm)
  subst hki
  have hsm2 : Smooth (B ⊗ B).hom := inferInstanceAs (Smooth (Limits.pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨S₂, ⟨P₂⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom (B ⊗ B).left
    (B ⊗ B).hom i₂ hkp hsm2
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S L₀ hL₀
  have h1 : (L₀.pull (fst B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h2 : (L₀.pull (snd B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h3 : (P.pull i₂).IsLB := pull_isLB hP _
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h1
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h2
  have hc₃ : IsObL S₂ α (P.pull i₂) 0 :=
    GlobalTheory.T.lineBundle_obstruction_zero_of_restriction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ (B ⊗ B).left (B ⊗ B).hom i₂ P₂ P hkp hP
  have hc₁₂ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ c₁ c₂ hc₁ hc₂
  have hc₁₂₃ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ _ _ hc₁₂ hc₃
  rw [add_zero] at hc₁₂₃

  have hz : GlobalTheory.CechPic.pull (1 : B₀ ⊗ B₀ ⟶ B₀).left (cls L₀ hL₀) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp]
    have h0 : cls (L₀.pull (η[B₀]).left) (pull_isLB hL₀ _) = 0 :=
      (cls_eq_zero_iff _).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₀) (pull_isLB hL₀ _))
    rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), h0, map_zero]
  have hmul : (fst B₀ B₀ * snd B₀ B₀ : B₀ ⊗ B₀ ⟶ B₀) = μ[B₀] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hLam : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hcube : cls (abelian₂ B₀ L₀) hLam = lam (cls L₀ hL₀) (fst B₀ B₀) (snd B₀ B₀) :=
    GlobalTheory.CechPic.cls_cube_two hL₀ (fst B₀ B₀) (snd B₀ B₀) hLam
  have hΛc : cls _ hLam = cls _ h3 := (cls_eq_iff hLam h3).2 hΛ
  have hiso : LBIso (tens (tens (L₀.pull (fst B₀ B₀).left) (L₀.pull (snd B₀ B₀).left)) (P.pull i₂))
      (L₀.pull (μ[B₀]).left) := by
    refine (cls_eq_iff (isLB_tens (isLB_tens h1 h2) h3) (pull_isLB hL₀ _)).1 ?_
    rw [cls_tens (isLB_tens h1 h2) h3, cls_tens h1 h2, ← hΛc, hcube, lam, hmul, hz, cls_pull hL₀, cls_pull hL₀,
      cls_pull hL₀]
    abel
  have hpb2 : IsPullback i₂ (B₀ ⊗ B₀).hom (B ⊗ B).hom (spMap π) := hkp
  have nat : ∀ (f₀ : (B₀ ⊗ B₀) ⟶ B₀) (f : (B ⊗ B) ⟶ B), i₂ ≫ f.left = f₀.left ≫ i →
      ∀ (L' : LB (B₀ ⊗ B₀).left) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff (B₀ ⊗ B₀).hom))), L'.IsLB →
        LBIso L' (L₀.pull f₀.left) → IsObL S₂ α L' c' → IsExtendedPullbackDegTwo R₁ (overW f₀) c c' := by
    intro f₀ f hf L' c' hL' hiso hob
    obtain ⟨l, hl, hn⟩ := GlobalTheory.Obs.exists_chart_lifts R R₀ _ hI π hπ rfl B₀.left (B₀ ⊗ B₀).left B.left (B ⊗ B).left
      B₀.hom (B₀ ⊗ B₀).hom B.hom (B ⊗ B).hom i i₂ hpb hkp S S₂ Pr P₂ f₀.left (overW f₀) f.left (Over.w f) hf
    exact GlobalTheory.T.lineBundleLiftObstruction_natural R R₀ _ hI π hπ rfl R₁ α B₀.left (B₀ ⊗ B₀).left B₀.hom (B₀ ⊗ B₀).hom S S₂ f₀.left (overW f₀)
      l hl hn L₀ L' c c' hL₀ hL' hiso hc hob
  have eμ := nat μ[B₀] μ[B] hkμ _ (c₁ + c₂) (isLB_tens (isLB_tens h1 h2) h3) hiso hc₁₂₃
  have e1 := nat (fst B₀ B₀) (fst B B) hkf _ c₁ h1 (GlobalTheory.PolBaseChange.lbIso_refl h1) hc₁
  have e2 := nat (snd B₀ B₀) (snd B B) hks _ c₂ h2 (GlobalTheory.PolBaseChange.lbIso_refl h2) hc₂
  have h0 : c = 0 := GlobalTheory.T.primitive_degree_two_any_ring R₀ R₁ α.q α.sq B₀ g hab hdim c c₁ c₂ eμ e1 e2
  subst h0
  exact GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S B.left B.hom i Pr L₀ hpb hL₀ hc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  atlas_forward_decl GlobalTheory.LBObs.exists_lift_of_lam_iso_pull
end
