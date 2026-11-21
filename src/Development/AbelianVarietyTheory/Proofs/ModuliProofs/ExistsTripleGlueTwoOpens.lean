import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GroupGlue

theorem exists_scheme {X : Scheme.{0}} {U V : X.Opens} {G₁ : Over U.toScheme} {G₂ : Over V.toScheme}
    {G₀ : Over (U ⊓ V).toScheme} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom (X.homOfLE inf_le_left))
    (h₂ : IsPullback φ₂ G₀.hom G₂.hom (X.homOfLE inf_le_right)) :
    ∃ (G : Over X) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom U.ι ∧
      IsPullback ψ₂ G₂.hom G.hom V.ι ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ X := pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by
    rw [h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · have hy' : y.1 = (G₂.hom x).1 := hy.trans (e2 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · have hy' : y.1 = (G₁.hom x).1 := hy.trans (e1 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_inf {X S : Scheme.{0}} {U V : X.Opens} (u : S ⟶ U) (v : S ⟶ V) (h : u ≫ U.ι = v ≫ V.ι) :
    ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
  have hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨(u z).2, ?_⟩
    rw [h]
    exact (v z).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]

theorem exists_glue_two : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (U V : X.Opens) (G₁ : Over U.toScheme) [GrpObj G₁] (G₂ : Over V.toScheme) [GrpObj G₂] (G₀ : Over (U ⊓ V).toScheme) [GrpObj G₀] (a₁ : OAct O G₁) (a₂ : OAct O G₂) (a₀ : OAct O G₀) (φ₁ : G₀.left ⟶ G₁.left) (φ₂ : G₀.left ⟶ G₂.left), U ⊔ V = ⊤ → IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsGrpPullback G₀ G₁ (X.homOfLE inf_le_left) φ₁ → IsGrpPullback G₀ G₂ (X.homOfLE inf_le_right) φ₂ → (∀ x, (a₀.act x).left ≫ φ₁ = φ₁ ≫ (a₁.act x).left ∧ (a₀.act x).left ≫ φ₂ = φ₂ ≫ (a₂.act x).left) → ∃ (G : Over X) (_ : GrpObj G) (a : OAct O G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G₁ G U.ι ψ₁ ∧ IsGrpPullback G₂ G V.ι ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ ∧ ∀ x, (a₁.act x).left ≫ ψ₁ = ψ₁ ≫ (a.act x).left ∧ (a₂.act x).left ≫ ψ₂ = ψ₂ ≫ (a.act x).left := by
  intro O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme h₁.1 h₂.1
  have m₁ : Mono ψ₁ := by
    have : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance
    infer_instance
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ →
      ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    refine exists_inf u v ?_
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens))
      (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  have ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂ := by
    intro x S u v a b h
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    rw [Over.comp_left, Over.comp_left, c₁, c₂]
    simp only [Category.assoc]
    rw [← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · exact ⟨true, ⟨x, hx⟩, rfl⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  let α : ∀ i : 𝒰.I₀, OAct O (H i) := fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  obtain ⟨A, hA⟩ := exists_oAct hG α (by
    have d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i := by
      intro x i S u v a b h
      obtain rfl := same i a b h
      rw [pt_ext hψ h]
    rintro x (_ | _) (_ | _) S u v a b h
    · exact d x _ S u v a b h
    · exact ca x a b h
    · exact (ca x b a h.symm).symm
    · exact d x _ S u v a b h)
  exact ⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ,
    fun x => ⟨hA x false, hA x true⟩⟩

end GlobalTheory.GroupGlue
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GlueTwoLB

variable {X Y Z : Scheme.{0}}

def stU (f : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (f z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (f.stalkMap z).hom.toMonoidHom

theorem stU_gm (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    stU f z (gm g (f z) U a) = gm (f ≫ g) z U a := by
  rw [← gm_pull f g z U h]
  apply Units.ext
  rw [gm_val f z (g ⁻¹ᵁ U) h]
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [gm_val g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f _ z h _

theorem stU_injective (f : Z ⟶ Y) [IsOpenImmersion f] (z : Z) : Function.Injective (stU f z) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1

theorem stU_gm_id (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    stU f z (gm (𝟙 Y) (f z) U a) = gm f z U a := by
  rw [stU_gm f (𝟙 Y) z U h, Category.comp_id]

theorem exists_push (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W : Z.Opens) (V : Y.Opens)
    (h : ∀ y ∈ V, ∃ z ∈ W, ψ z = y) (a : Γ(Z, W)ˣ) :
    ∃ b : Γ(Y, V)ˣ, ∀ z : Z, ψ z ∈ V → gm ψ z V b = gm (𝟙 Z) z W a := by
  have hle : V ≤ ψ ''ᵁ W := fun y hy => h y hy
  refine ⟨res hle (Units.map (ψ.appIso W).inv.hom.toMonoidHom a), fun z hz => ?_⟩
  have hW : z ∈ W := by
    obtain ⟨z', hz', e⟩ := h _ hz
    rwa [← ψ.isOpenEmbedding.injective e]
  rw [gm_res ψ z hle hz]
  apply Units.ext
  rw [gm_val ψ z _ (hle hz), gm_val (𝟙 Z) z W hW]
  have e := congrArg (fun q => q.hom a.val) (ψ.appIso_inv_app W)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Z.presheaf.germ (ψ ⁻¹ᵁ ψ ''ᵁ W) z (hle hz)).hom e).trans
    (TopCat.Presheaf.germ_res_apply Z.presheaf _ z (hle hz) _)

theorem iso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem isLB_of_stalk {L : LB X} (hc : ∀ x, ∃ i, x ∈ L.U i)
    (h : ∀ x i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact h y i j k hy.1.1 hy.1.2 hy.2

theorem cocycle_descend {L : LB Y} (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (z : Z) {i j k : L.ι}
    (hi : ψ z ∈ L.U i) (hj : ψ z ∈ L.U j) (hk : ψ z ∈ L.U k)
    (h : gm ψ z _ (L.g i j) * gm ψ z _ (L.g j k) = gm ψ z _ (L.g i k)) :
    gm (𝟙 Y) (ψ z) _ (L.g i j) * gm (𝟙 Y) (ψ z) _ (L.g j k) = gm (𝟙 Y) (ψ z) _ (L.g i k) := by
  apply stU_injective ψ z
  rw [map_mul, stU_gm_id ψ z (L.U i ⊓ L.U j) ⟨hi, hj⟩, stU_gm_id ψ z (L.U j ⊓ L.U k) ⟨hj, hk⟩,
    stU_gm_id ψ z (L.U i ⊓ L.U k) ⟨hi, hk⟩, h]

theorem mem_of_mem_image (ψ : Z ⟶ Y) [IsOpenImmersion ψ] {W : Z.Opens} {z : Z} (h : ψ z ∈ ψ ''ᵁ W) : z ∈ W := by
  obtain ⟨z', hz', e⟩ := h
  rwa [← ψ.isOpenEmbedding.injective e]

theorem exists_push_inf (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W W' : Z.Opens) (a : Γ(Z, W ⊓ W')ˣ) :
    ∃ b : Γ(Y, ψ ''ᵁ W ⊓ ψ ''ᵁ W')ˣ, ∀ z : Z, z ∈ W → z ∈ W' →
      gm ψ z (ψ ''ᵁ W ⊓ ψ ''ᵁ W') b = gm (𝟙 Z) z (W ⊓ W') a := by
  obtain ⟨b, hb⟩ := exists_push ψ (W ⊓ W') (ψ ''ᵁ W ⊓ ψ ''ᵁ W') (by
    rintro y ⟨⟨z, hz, rfl⟩, h'⟩
    exact ⟨z, ⟨hz, mem_of_mem_image ψ h'⟩, rfl⟩) a
  exact ⟨b, fun z h h' => hb z ⟨⟨z, h, rfl⟩, ⟨z, h', rfl⟩⟩⟩

theorem gen_stalk {Y₀ Y₁ Y₂ : Scheme.{0}} {φ₁ : Y₀ ⟶ Y₁} {φ₂ : Y₀ ⟶ Y₂} {L₁ : LB Y₁} {L₂ : LB Y₂}
    {w : LB.Iso (L₁.pull φ₁) (L₂.pull φ₂)} (hw : w.IsGen) (y : Y₀) {i i' : L₁.ι} {k k' : L₂.ι}
    (hi : φ₁ y ∈ L₁.U i) (hi' : φ₁ y ∈ L₁.U i') (hk : φ₂ y ∈ L₂.U k) (hk' : φ₂ y ∈ L₂.U k') :
    gw w (𝟙 Y₀) y k (fun _ => i) = gm φ₂ y _ (L₂.g k k') * (gm φ₁ y _ (L₁.g i i'))⁻¹ *
      gw w (𝟙 Y₀) y k' (fun _ => i') := by
  have := (isGen_iff w).1 hw Y₀ (𝟙 Y₀) y k k' (fun _ => i) (fun _ => i') hk hk' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ φ₁ (𝟙 Y₀) y _ _ (mem_pull.2 hi) (mem_pull.2 hi'), Category.id_comp, Category.id_comp] at this
  exact this

def pullChart (L : LB X) (F : Y ⟶ X) : ChartPull (L.pull F) L F where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hj hj' := (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

theorem glue : ∀ (Y Y₀ Y₁ Y₂ : Scheme.{0}) (ψ₁ : Y₁ ⟶ Y) (ψ₂ : Y₂ ⟶ Y) (φ₁ : Y₀ ⟶ Y₁) (φ₂ : Y₀ ⟶ Y₂) (L₁ : LB Y₁) (L₂ : LB Y₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ → L₁.IsLB → L₂.IsLB → LBIso (L₁.pull φ₁) (L₂.pull φ₂) → ∃ L : LB Y, L.IsLB ∧ LBIso L₁ (L.pull ψ₁) ∧ LBIso L₂ (L.pull ψ₂) := by
  intro Y Y₀ Y₁ Y₂ ψ₁ ψ₂ φ₁ φ₂ L₁ L₂ o₁ o₂ hp hcov h₁ h₂ ⟨w, hw⟩
  have p₁ : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback hp.flip o₂
  have hpt : ∀ y, ψ₁ (φ₁ y) = ψ₂ (φ₂ y) := fun y => congrArg (fun g => g y) hp.w
  have lift : ∀ y₁ y₂, ψ₁ y₁ = ψ₂ y₂ → ∃ y, φ₁ y = y₁ ∧ φ₂ y = y₂ := fun y₁ y₂ e =>
    Scheme.exists_preimage_of_isPullback hp y₁ y₂ e
  have hsq := hp.w
  choose g₁ hg₁ using fun i j => exists_push_inf ψ₁ _ _ (L₁.g i j)
  choose g₂ hg₂ using fun i j => exists_push_inf ψ₂ _ _ (L₂.g i j)
  have hm : ∀ (k : L₂.ι) (i : L₁.ι), ∃ b : Γ(Y, ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i)ˣ, ∀ y : Y₀,
      φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ b = gw w (𝟙 Y₀) y k (fun _ => i) := by
    intro k i
    obtain ⟨b, hb⟩ := exists_push (φ₁ ≫ ψ₁) ((L₂.pull φ₂).U (fun _ => k) ⊓ (L₁.pull φ₁).U (fun _ => i))
      (ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i) (by
        rintro y ⟨⟨y₂, h₂, rfl⟩, ⟨y₁, h₁, e⟩⟩
        obtain ⟨z, rfl, rfl⟩ := lift y₁ y₂ e
        exact ⟨z, ⟨mem_pull.2 h₂, mem_pull.2 h₁⟩, e⟩) (w.s (fun _ => k, fun _ => i))
    exact ⟨b, fun y hk hi => hb y ⟨⟨_, hk, (hpt y).symm⟩, ⟨_, hi, rfl⟩⟩⟩
  choose m hm using hm
  let L : LB Y :=
    { «ι» := L₁.ι ⊕ L₂.ι
      U := Sum.elim (fun i => ψ₁ ''ᵁ L₁.U i) (fun k => ψ₂ ''ᵁ L₂.U k)
      g := fun p q => match p, q with
        | .inl i, .inl j => g₁ i j
        | .inr k, .inr l => g₂ k l
        | .inr k, .inl i => m k i
        | .inl i, .inr k => (res (le_inf inf_le_right inf_le_left) (m k i))⁻¹ }

  have key : ∀ y : Y₀, ∃ t : L.ι → (Y₀.presheaf.stalk y)ˣ, ∀ p q, ψ₁ (φ₁ y) ∈ L.U p → ψ₁ (φ₁ y) ∈ L.U q →
      gm (φ₁ ≫ ψ₁) y _ (L.g p q) = t p * (t q)⁻¹ := by
    intro y
    obtain ⟨i₀, hi₀⟩ := exists_chart h₁ (φ₁ y)
    have ml : ∀ i, ψ₁ (φ₁ y) ∈ L.U (.inl i) → φ₁ y ∈ L₁.U i := fun i h => mem_of_mem_image ψ₁ h
    have mr : ∀ k, ψ₁ (φ₁ y) ∈ L.U (.inr k) → φ₂ y ∈ L₂.U k := fun k h => mem_of_mem_image ψ₂ (hpt y ▸ h)
    have mix : ∀ k i, φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ (m k i) =
        gw w (𝟙 Y₀) y k (fun _ => i₀) * (gm φ₁ y _ (L₁.g i i₀))⁻¹ := fun k i hk hi => by
      rw [hm k i y hk hi, gen_stalk hw y hi hi₀ hk hk, gm_self h₂ φ₂ y hk, _root_.one_mul, mul_comm]
    refine ⟨Sum.elim (fun i => gm φ₁ y _ (L₁.g i i₀)) (fun k => gw w (𝟙 Y₀) y k (fun _ => i₀)), ?_⟩
    rintro (i | k) (j | l) hp hq
    · have e := congrArg (stU φ₁ y) (hg₁ i j _ (ml i hp) (ml j hq))
      rw [stU_gm φ₁ ψ₁ y (ψ₁ ''ᵁ L₁.U i ⊓ ψ₁ ''ᵁ L₁.U j) ⟨hp, hq⟩, stU_gm_id φ₁ y (L₁.U i ⊓ L₁.U j) ⟨ml i hp, ml j hq⟩] at e
      refine e.trans ?_
      exact eq_mul_inv_of_mul_eq (gm_cocycle h₁ φ₁ y (ml i hp) (ml j hq) hi₀)
    · refine ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (φ₁ ≫ ψ₁) y _
        (show (φ₁ ≫ ψ₁) y ∈ ψ₁ ''ᵁ L₁.U i ⊓ ψ₂ ''ᵁ L₂.U l from ⟨hp, hq⟩) _).trans
        (mix l i (mr l hq) (ml i hp))))).trans ?_
      rw [mul_inv_rev, inv_inv]; rfl
    · exact mix k j (mr k hp) (ml j hq)
    · have e := congrArg (stU φ₂ y) (hg₂ k l _ (mr k hp) (mr l hq))
      rw [stU_gm φ₂ ψ₂ y (ψ₂ ''ᵁ L₂.U k ⊓ ψ₂ ''ᵁ L₂.U l) ⟨⟨_, mr k hp, rfl⟩, ⟨_, mr l hq, rfl⟩⟩,
        stU_gm_id φ₂ y (L₂.U k ⊓ L₂.U l) ⟨mr k hp, mr l hq⟩, ← hsq] at e
      refine e.trans (eq_mul_inv_of_mul_eq ?_)
      have := gen_stalk hw y hi₀ hi₀ (mr k hp) (mr l hq)
      rw [gm_self h₁ φ₁ y hi₀, inv_one, _root_.mul_one] at this
      exact this.symm
  have hL : L.IsLB := by
    refine isLB_of_stalk (fun x => ?_) ?_
    · rcases (hcov.symm ▸ Set.mem_univ x : x ∈ Set.range ψ₁ ∪ Set.range ψ₂) with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₁ y
        exact ⟨.inl i, y, hi, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₂ y
        exact ⟨.inr i, y, hi, rfl⟩
    have ov : ∀ x p q r (i : L₁.ι) (k : L₂.ι), x ∈ L.U (.inl i) → x ∈ L.U (.inr k) →
        x ∈ L.U p → x ∈ L.U q → x ∈ L.U r →
        gm (𝟙 Y) x _ (L.g p q) * gm (𝟙 Y) x _ (L.g q r) = gm (𝟙 Y) x _ (L.g p r) := by
      rintro x p q r i k ⟨y₁, -, rfl⟩ ⟨y₂, -, e⟩ hp hq hr
      obtain ⟨y, rfl, rfl⟩ := lift y₁ y₂ e.symm
      obtain ⟨t, ht⟩ := key y
      refine cocycle_descend (φ₁ ≫ ψ₁) y hp hq hr ?_
      rw [ht p q hp hq, ht q r hq hr, ht p r hp hr, _root_.mul_assoc, inv_mul_cancel_left]
    rintro x (i | i) (j | j) (k | k) hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₁ hj
      have hk' := mem_of_mem_image ψ₁ hk
      refine cocycle_descend ψ₁ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₁ i j y hy hj') (hg₁ j k y hj' hk')).trans
        ((gm_cocycle h₁ (𝟙 _) y hy hj' hk').trans (hg₁ i k y hy hk').symm)
    · exact ov x _ _ _ i k hi hk hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ k i hk hi hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₂ hj
      have hk' := mem_of_mem_image ψ₂ hk
      refine cocycle_descend ψ₂ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₂ i j y hy hj') (hg₂ j k y hj' hk')).trans
        ((gm_cocycle h₂ (𝟙 _) y hy hj' hk').trans (hg₂ i k y hy hk').symm)
  let c₁ : ChartPull L₁ L ψ₁ := ⟨Sum.inl, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₁ i j y hi hj).symm⟩
  let c₂ : ChartPull L₂ L ψ₂ := ⟨Sum.inr, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₂ i j y hi hj).symm⟩
  exact ⟨L, hL, LBIso.chartPull c₁ (pullChart L ψ₁) (iso_self hL),
    LBIso.chartPull c₂ (pullChart L ψ₂) (iso_self hL)⟩

end GlobalTheory.GlueTwoLB
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cub {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB)
    (h : (cubeLB G x L).IsLB) : cls (cubeLB G x L) h = cub x (cls L hL) :=
  cls_linComb hL _ _ h

theorem isLB_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    (cubeLB G x L).IsLB := LB.isLB_linComb hL _ _

theorem pull_cub {T T' : Over S} {n : ℕ} (U : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull U.left (cub x c) = cub (fun i => U ≫ x i) c := by
  unfold cub
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • pull z.left c) (psum_hom (preHom U) x I.down)

theorem pull_cub_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (c : Pic G.left) : pull U.left (cub x c) = cub x' (pull φ c) := by
  unfold cub
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← psum_push h x' x U hx, pull_comp]

theorem pull_one {T : Over S} {c : Pic G.left} (hc : pull (eSec G) c = 0) : pull (1 : T ⟶ G).left c = 0 := by
  have : (1 : T ⟶ G).left = (toUnit T).left ≫ eSec G := rfl
  rw [this, pull_comp, hc, map_zero]

theorem cub_one {T : Over S} {n : ℕ} {x : Fin n → (T ⟶ G)} (hx : ∀ i, x i = 1) {c : Pic G.left}
    (hc : pull (eSec G) c = 0) : cub x c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : psum G x I.down = 1 := by
    have := psum_hom (1 : (T ⟶ G) →* (T ⟶ G)) x I.down
    rw [MonoidHom.one_apply] at this
    exact (congrArg (fun z => psum G z I.down) (funext hx)).trans this.symm
  rw [e, pull_one hc, smul_zero]

end Cube

theorem eq_zero_of_cover {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) {U V : X.Opens}
    (hUV : U ⊔ V = ⊤) (c : Pic P.left) (h₀ : pull e.left c = 0) (hU : pull (P.hom ⁻¹ᵁ U).ι c = 0)
    (hV : pull (P.hom ⁻¹ᵁ V).ι c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  refine (cls_eq_zero_iff hN).2 (GlobalTheory.RigidTriv.exists_gen_of_rigid X P e.left N he
    (GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) fun x => ?_)
  have hx : x ∈ U ⊔ V := hUV ▸ trivial
  rcases hx with hx | hx
  · exact ⟨U, hx, (cls_eq_zero_iff (pull_isLB hN _)).1 hU⟩
  · exact ⟨V, hx, (cls_eq_zero_iff (pull_isLB hN _)).1 hV⟩

abbrev part {X : Scheme.{0}} (P : Over X) (W : X.Opens) : Over W.toScheme := Over.mk (P.hom ∣_ W)

def partι {X : Scheme.{0}} (P : Over X) (W : X.Opens) : Over.mk ((part P W).hom ≫ W.ι) ⟶ P :=
  Over.homMk (P.hom ⁻¹ᵁ W).ι (morphismRestrict_ι P.hom W).symm

theorem exists_lift {X : Scheme.{0}} {W : X.Opens} {G : Over X} {G' : Over W.toScheme} {ψ : G'.left ⟶ G.left}
    (h : IsPullback ψ G'.hom G.hom W.ι) {P : Over X} (x : P ⟶ G) :
    ∃ x' : part P W ⟶ G', pushPt h.w x' = partι P W ≫ x :=
  ⟨Over.homMk (h.lift (partι P W ≫ x).left (part P W).hom (Over.w _)) (h.lift_snd _ _ _),
    Over.OverMorphism.ext (h.lift_fst _ _ _)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem local_identities {X : Scheme.{0}} {W : X.Opens} {G : Over X} [GrpObj G] [IsCommMonObj G]
    (a : OAct (𝓞 E) G) (c : Pic G.left) (t : SAB H W.toScheme) {ψ : t.G.left ⟶ G.left}
    (gp : IsGrpPullback t.G G W.ι ψ) (ha : ∀ x, (t.act.act x).left ≫ ψ = ψ ≫ (a.act x).left)
    (hc : pull ψ c = cls t.PP.L t.PP.isLB) :
    pull ((G3 G).hom ⁻¹ᵁ W).ι (cub (x3 G) c) = 0 ∧
    pull (G.hom ⁻¹ᵁ W).ι (c - pull (GrpObj.inv (X := G)).left c) = 0 ∧
    (∀ b, pull ((G ⊗ G).hom ⁻¹ᵁ W).ι
      (cub ![fst G G ≫ a.act b, snd G G] c - cub ![fst G G, snd G G ≫ a.act (H.bar b)] c) = 0) ∧
    pull (G.hom ⁻¹ᵁ W).ι (c - cub ![𝟙 G, a.act H.w0] c) = 0 := by
  have pa : ∀ {T : Over W.toScheme} (x : T ⟶ t.G) b,
      pushPt gp.1.w (x ≫ t.act.act b) = pushPt gp.1.w x ≫ a.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  obtain ⟨u, hu⟩ := exists_lift gp.1 (𝟙 G)
  have hu' : u.left ≫ ψ = (G.hom ⁻¹ᵁ W).ι := (congrArg (fun z => z.left) hu).trans (Category.comp_id _)
  have hp : pull (G.hom ⁻¹ᵁ W).ι c = pull u.left (cls t.PP.L t.PP.isLB) := by rw [← hu', pull_comp, hc]
  refine ⟨?_, ?_, fun b => ?_, ?_⟩
  · choose x' hx' using fun i => exists_lift gp.1 (x3 G i)
    have e₁ := pull_cub_push gp x' _ _ hx' c
    have e₂ := pull_cub (lift (x' 0) (lift (x' 1) (x' 2))) (x3 t.G) (cls t.PP.L t.PP.isLB)
    have e₃ : cub (x3 t.G) (cls t.PP.L t.PP.isLB) = 0 :=
      (cls_cubeLB _ _ (isLB_cubeLB _ t.PP.isLB)).symm.trans ((cls_eq_zero_iff _).2 ⟨t.cub.t, t.cub.isGen⟩)
    have e₄ : (fun i => lift (x' 0) (lift (x' 1) (x' 2)) ≫ x3 t.G i) = x' := by
      funext i
      fin_cases i <;> simp [x3]
    rw [e₃, map_zero, e₄, ← hc] at e₂
    exact e₁.trans e₂.symm
  · obtain ⟨_, w, hw, -⟩ := t.sym
    have e₁ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have e₂ : (GrpObj.inv (X := t.G)).left ≫ ψ = ψ ≫ (GrpObj.inv (X := G)).left := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      simpa [pushHom, pushPt, Hom.inv_def] using e
    rw [map_sub, ← pull_comp, ← hu', Category.assoc, ← e₂, pull_comp, pull_comp, pull_comp, hc, ← e₁, sub_self]
  · obtain ⟨x, hx⟩ := exists_lift gp.1 (fst G G)
    obtain ⟨y, hy⟩ := exists_lift gp.1 (snd G G)
    have e₁ := pull_cub_push gp ![x ≫ t.act.act b, y] ![fst G G ≫ a.act b, snd G G] (partι _ W) (fun i => by
      fin_cases i
      · exact (pa _ _).trans (by rw [hx]; exact Category.assoc _ _ _)
      · exact hy) c
    have e₂ := pull_cub_push gp ![x, y ≫ t.act.act (H.bar b)] ![fst G G, snd G G ≫ a.act (H.bar b)] (partι _ W)
      (fun i => by
        fin_cases i
        · exact hx
        · exact (pa _ _).trans (by rw [hy]; exact Category.assoc _ _ _)) c
    have e₃ := congrArg (pull (lift x y).left) ((cls_cubeLB _ t.PP.isLB _).symm.trans
      (((cls_eq_iff (isLB_cubeLB _ t.PP.isLB) (isLB_cubeLB _ t.PP.isLB)).2 (t.adj b)).trans
        (cls_cubeLB _ t.PP.isLB _)))
    have f₁ : (fun i => lift x y ≫ ![fst t.G t.G ≫ t.act.act b, snd t.G t.G] i) = ![x ≫ t.act.act b, y] := by
      funext i
      fin_cases i <;> simp
    have f₂ : (fun i => lift x y ≫ ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar b)] i) =
        ![x, y ≫ t.act.act (H.bar b)] := by
      funext i
      fin_cases i <;> simp
    rw [pull_cub, pull_cub, f₁, f₂, ← hc] at e₃
    rw [map_sub, sub_eq_zero]
    exact e₁.trans (e₃.trans e₂.symm)
  · have e₁ := pull_cub_push gp ![u, u ≫ t.act.act H.w0] ![𝟙 G, a.act H.w0] (partι _ W) (fun i => by
      fin_cases i
      · exact hu
      · exact (pa _ _).trans (by rw [hu]; simp)) c
    have e₃ := congrArg (pull u.left)
      (((cls_eq_iff t.PP.isLB (isLB_cubeLB _ t.PP.isLB)).2 t.prim).trans (cls_cubeLB _ t.PP.isLB _))
    have f₁ : (fun i => u ≫ ![𝟙 t.G, t.act.act H.w0] i) = ![u, u ≫ t.act.act H.w0] := by
      funext i
      fin_cases i <;> simp
    rw [pull_cub, f₁] at e₃
    rw [hc] at e₁
    rw [map_sub, sub_eq_zero, hp]
    exact e₃.trans e₁.symm

theorem isReduced_of_cover {X : Scheme.{0}} {U V : X.Opens} (hUV : U ⊔ V = ⊤) [IsReduced U.toScheme]
    [IsReduced V.toScheme] : IsReduced X := by
  have key : ∀ (W : X.Opens) [IsReduced W.toScheme] (x : X), x ∈ W → _root_.IsReduced (X.presheaf.stalk x) := by
    intro W _ x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
    exact isReduced_of_injective (W.ι.stalkMap y).hom (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact key U x hx
    · exact key V x hx
  exact isReduced_of_isReduced_stalk X

theorem mem_genericPoints_open {X : Scheme.{0}} (W : X.Opens) (x : W.toScheme) (hx : W.ι x ∈ genericPoints X) :
    x ∈ genericPoints W.toScheme := by
  have h := preimage_mem_irreducibleComponents (t := closure {W.ι x}) hx W.ι.isOpenEmbedding
    ⟨W.ι x, subset_closure rfl, x, rfl⟩
  change closure _ ∈ irreducibleComponents W.toScheme
  rw [W.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  exact h

theorem pull_eSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    pull (eSec G) (cls L.L L.isLB) = 0 :=
  (cls_eq_zero_iff (pull_isLB L.isLB _)).2 ⟨L.rig, L.rigGen⟩

theorem pull_rigidify {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f ψ) (c : Pic G.left)
    (L : RigLB G') (h : cls L.L L.isLB = pull ψ c) :
    pull ψ (c - pull ((toUnit G).left ≫ eSec G) c) = cls L.L L.isLB := by
  have e : ψ ≫ (toUnit G).left ≫ eSec G = (toUnit G').left ≫ eSec G' ≫ ψ := by
    have e₁ : eSec G' ≫ ψ = f ≫ eSec G := (cubeMapOf gp).e_comm
    have e₂ : ψ ≫ G.hom = G'.hom ≫ f := gp.1.w
    rw [e₁, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ eSec G) e₂
  rw [map_sub, ← pull_comp, e, pull_comp, pull_comp, ← h, pull_eSec, map_zero, sub_zero]

theorem exists_sab_glue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  intro E _ _ _ H X U V t₁ t₂ t₀ m₁ m₂ hUV h₁ h₂
  obtain ⟨G, _, a, ψ₁, ψ₂, hG, gp₁, gp₂, hφ, ha⟩ := GlobalTheory.GroupGlue.exists_glue_two (𝓞 E) X U V t₁.G t₂.G t₀.G t₁.act t₂.act t₀.act
    m₁.φ m₂.φ hUV t₁.semi t₂.semi m₁.cart m₂.cart fun x => ⟨m₁.act x, m₂.act x⟩
  have := hG.comm
  have o₁ : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback gp₁.1.flip inferInstance
  have o₂ : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback gp₂.1.flip inferInstance
  have sq : IsPullback m₁.φ m₂.φ ψ₁ ψ₂ := by
    have big := m₁.cart.1.paste_vert (isPullback_opens_inf U V)
    rw [← m₂.cart.1.w, ← gp₁.1.w] at big
    exact big.of_bot hφ gp₂.1
  have cov : Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    have hx : G.hom g ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback gp₁.1 g ⟨_, hx⟩ rfl
      exact .inl ⟨z, hz⟩
    · obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback gp₂.1 g ⟨_, hx⟩ rfl
      exact .inr ⟨z, hz⟩
  obtain ⟨w₁, hw₁, -⟩ := m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := m₂.lin
  obtain ⟨L, hL, i₁, i₂⟩ := GlobalTheory.GlueTwoLB.glue G.left t₀.G.left t₁.G.left t₂.G.left ψ₁ ψ₂ m₁.φ m₂.φ t₁.PP.L t₂.PP.L o₁ o₂
    sq cov t₁.PP.isLB t₂.PP.isLB (LBIso.trans (pull_isLB t₁.PP.isLB _) t₀.PP.isLB (pull_isLB t₂.PP.isLB _)
      (LBIso.symm ⟨w₁, hw₁⟩) ⟨w₂, hw₂⟩)
  obtain ⟨M, hM, hc⟩ := cls_surj (cls L hL - pull ((toUnit G).left ≫ eSec G) (cls L hL))
  have c₁ : pull ψ₁ (cls M hM) = cls t₁.PP.L t₁.PP.isLB :=
    hc ▸ pull_rigidify gp₁ _ t₁.PP ((cls_eq_iff _ (pull_isLB hL _)).2 i₁)
  have c₂ : pull ψ₂ (cls M hM) = cls t₂.PP.L t₂.PP.isLB :=
    hc ▸ pull_rigidify gp₂ _ t₂.PP ((cls_eq_iff _ (pull_isLB hL _)).2 i₂)
  have c₀ : pull (eSec G) (cls M hM) = 0 := by
    have e : eSec G ≫ (toUnit G).left = 𝟙 _ := Over.w η[G]
    rw [hc, map_sub, ← pull_comp, ← Category.assoc, e, Category.id_comp, sub_self]
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM _)).1 c₀
  let PP : RigLB G := ⟨M, ρ, hM, hρ⟩
  have hr : IsReduced X := by
    have := h₁.1
    have := h₂.1
    exact isReduced_of_cover hUV
  have hab : genericPoints X ⊆ abLocus G := fun x hx => by
    have hx' : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx' with hx' | hx'
    · exact (abLocus_pullback abLocusOne hG gp₁.1 ⟨x, hx'⟩).2 (h₁.2 (mem_genericPoints_open U ⟨x, hx'⟩ hx))
    · exact (abLocus_pullback abLocusOne hG gp₂.1 ⟨x, hx'⟩).2 (h₂.2 (mem_genericPoints_open V ⟨x, hx'⟩ hx))
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  obtain ⟨a₂, b₂, d₂⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G a₁ a₁ b₁ b₁
  have g₂ := (Set.subset_inter hab hab).trans d₂
  obtain ⟨a₃, b₃, d₃⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G _ a₁ a₂ b₁ b₂
  have g₃ := (Set.subset_inter hab g₂).trans d₃
  obtain ⟨p₁, q₁, r₁, s₁⟩ := local_identities a (cls M hM) t₁ gp₁ (fun x => (ha x).1) c₁
  obtain ⟨p₂, q₂, r₂, s₂⟩ := local_identities a (cls M hM) t₂ gp₂ (fun x => (ha x).2) c₂
  have one_act : ∀ b, (1 : 𝟙_ (Over X) ⟶ G) ≫ a.act b = 1 := fun b => by
    have := a.hom b
    exact MonObj.one_comp _
  have z₀ : pull (1 : 𝟙_ (Over X) ⟶ G).left (cls M hM) = 0 := pull_one c₀
  have p := eq_zero_of_cover (G3 G) (lift 1 (lift 1 1)) a₃ b₃ hr g₃ hUV _
    ((pull_cub _ _ _).trans (cub_one (fun i => by fin_cases i <;> simp [x3]) c₀)) p₁ p₂
  have q := eq_zero_of_cover G 1 a₁ b₁ hr hab hUV _ (by
    have e : (1 : 𝟙_ (Over X) ⟶ G) ≫ GrpObj.inv (X := G) = 1 := (Hom.inv_def _).symm.trans inv_one
    rw [map_sub, ← pull_comp, ← Over.comp_left, e, sub_self]) q₁ q₂
  have r := fun b => eq_zero_of_cover (G ⊗ G) (lift 1 1) a₂ b₂ hr g₂ hUV _ (by
    rw [map_sub, pull_cub, pull_cub, cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀,
      cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀, sub_self]) (r₁ b) (r₂ b)
  have s := eq_zero_of_cover G 1 a₁ b₁ hr hab hUV _ (by
    rw [map_sub, pull_cub, cub_one (fun i => by fin_cases i <;> simp [one_act]) c₀, z₀, sub_self]) s₁ s₂
  obtain ⟨k₁, k₂⟩ := GlobalTheory.CubeGen.cubical_and_symmetric X G PP hG ⟨hr, hab⟩
  obtain ⟨cb⟩ := k₁ ((cls_eq_zero_iff (isLB_cubeLB _ hM)).1 ((cls_cubeLB _ hM _).trans p))
  let t : SAB H X :=
    { G := G, semi := hG, act := a, PP := PP, cub := cb
      sym := k₂ ((cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 q))
      adj := fun b => (cls_eq_iff (isLB_cubeLB _ hM) (isLB_cubeLB _ hM)).1
        ((cls_cubeLB _ hM _).trans ((sub_eq_zero.1 (r b)).trans (cls_cubeLB _ hM _).symm))
      prim := (cls_eq_iff hM (isLB_cubeLB _ hM)).1 ((sub_eq_zero.1 s).trans (cls_cubeLB _ hM _).symm) }
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X U t t₁ U.ι ψ₁ h₁ gp₁ (fun x => (ha x).1)
    ((cls_eq_iff t₁.PP.isLB (pull_isLB hM _)).1 c₁.symm)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X V t t₂ V.ι ψ₂ h₂ gp₂ (fun x => (ha x).2)
    ((cls_eq_iff t₂.PP.isLB (pull_isLB hM _)).1 c₂.symm)
  exact ⟨t, n₁, n₂, by rw [hn₁, hn₂]; exact hφ⟩

end GlobalTheory.TripleGlue
end
end
