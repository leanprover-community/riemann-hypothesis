import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c → ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  first | (exact @GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (exact GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (intros; apply GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_schemeTheoreticallyDominant_isUnit_natCast (T : Scheme.{0}) (c : ℕ)
    (hc : ∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) :
    ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  refine ⟨(T.basicOpen (c : Γ(T, ⊤))).toScheme, (T.basicOpen (c : Γ(T, ⊤))).ι, ?_, ?_⟩
  · refine isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine T T (𝟙 T) _ ?_
    intro U V hU _ _ b hb
    have key : ∀ (n : ℕ) (b : Γ(T, U)), (c : Γ(T, U)) ^ n * b = 0 → b = 0 := by
      intro n
      induction n with
      | zero => intro b h; simpa using h
      | succ n ih =>
        intro b h
        exact hc U b (ih _ (by rw [← _root_.mul_assoc, ← pow_succ]; exact h))
    have hD : T.basicOpen (c : Γ(T, U)) = U ⊓ T.basicOpen (c : Γ(T, ⊤)) := by
      rw [← T.basicOpen_res (c : Γ(T, ⊤)) (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]
    have h0 : T.presheaf.map (homOfLE (T.basicOpen_le (c : Γ(T, U)))).op b = 0 := by
      refine TopCat.Presheaf.section_ext T.sheaf _ _ 0 (fun x hx => ?_)
      show T.presheaf.germ _ x hx (T.presheaf.map _ b) = T.presheaf.germ _ x hx 0
      rw [TopCat.Presheaf.germ_res_apply, map_zero]
      exact hb x _ (hD ▸ hx).2
    letI := hU.isLocalization_basicOpen (c : Γ(T, U))
    obtain ⟨⟨m, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (c : Γ(T, U)))
        Γ(T, T.basicOpen (c : Γ(T, U))) b).mp h0
    exact key n b hm
  · have := (T.toRingedSpace.isUnit_res_basicOpen (c : Γ(T, ⊤))).map
      (T.basicOpen (c : Γ(T, ⊤))).topIso.inv.hom
    exact (congrArg IsUnit ((congrArg _ (map_natCast _ c)).trans (map_natCast _ c))).mp this

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor : ∀ (T : Scheme.{0}) (c : ℕ), (∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) → ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  first | (exact @GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (exact GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (intros; apply GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_fiber_eq_card_sections_mul_length : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k), IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) → ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  first | (exact @GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (exact GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (intros; apply GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteGroupSchemeLength

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective
  let l : R ≃ₗ[R] S :=
    { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
      map_add' := e.map_add,
      map_smul' := fun r x => by
        simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  rw [l.length_eq, h1]

theorem isClosed_singleton_of_isFinite {k : Type} [Field k] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of k)) [IsFinite f] (z : H) : IsClosed ({z} : Set H) := by
  have hz : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k}) :=
    (IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

theorem length_stalk_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  intro k _ _ G _ hf x x'
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y := by
    intro y
    have hy := isClosed_singleton_of_isFinite G.hom y
    exact ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
      pointOfClosedPoint_apply G.hom y hy _⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨a', rfl⟩ := hsurj x'
  let φ := GrpObj.mulRight (a⁻¹ * a')
  have h : a ≫ φ.hom = a' := by
    have : a ≫ φ.hom = a * (a⁻¹ * a') := by
      simp [φ, comp_lift_assoc, Hom.mul_def]
    rw [this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hx : φ.hom.left (a.left pt) = a'.left pt := by
    rw [← h]; rfl
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have hi : IsIso (φ.hom.left.stalkMap (a.left pt)) :=
    ((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _
  let e := (asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv
  rw [← length_self_eq_of_ringEquiv e]
  congr 1 <;> rw [hx]

end GlobalTheory.FiniteGroupSchemeLength
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_stalk_length_constant : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  first | (exact @GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (exact GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (intros; apply GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.OrdCount

open GlobalTheory.IwLevel GlobalTheory.IwLevel.KerGrp in

theorem exists_idem_kernel : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') (f : A ⟶ A), IsMonHom ψ → IsMonHom f → IsFinite ψ.left → Flat ψ.left → (∀ (T : Over S) (z : T ⟶ A), z ≫ ψ = 1 → (z ≫ f) ≫ ψ = 1 ∧ (z ≫ f) ≫ f = z ≫ f) → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (z : T ⟶ A), GlobalTheory.IwLevel.InSub i z ↔ (z ≫ ψ = 1 ∧ z ≫ f = 1) := by
  intro S A A' _ _ _ _ ψ fx _ _ hfin hfl hyp
  letI gH : GrpObj (IwLevel.ker ψ) := grp ψ
  haveI : IsMonHom (pullback.fst ψ η[A']) := isMonHom_fst ψ
  have hPB := (IsPullback.of_hasPullback ψ η[A']).map (Over.forget S)
  have hHfin : IsFinite (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : IsFinite (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfin
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : Flat (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @Flat) hPB hfl
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))
  set jH := pullback.fst ψ η[A'] with hjH
  have hj : jH ≫ ψ = 1 := fst_comp ψ
  let g : IwLevel.ker ψ ⟶ IwLevel.ker ψ := KerGrp.lift ψ (jH ≫ fx) (hyp _ jH hj).1
  have hg : g ≫ jH = jH ≫ fx := KerGrp.lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by rw [← Category.assoc]; exact (hyp _ jH hj).2
  letI gK : GrpObj (IwLevel.ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (IwLevel.ker ψ) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : IwLevel.ker ψ ⟶ IwLevel.ker (jH ≫ fx) := KerGrp.lift (jH ≫ fx) (𝟙 (IwLevel.ker ψ) / g) hrk
  have hr : r ≫ iK = 𝟙 (IwLevel.ker ψ) / g := KerGrp.lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := KerGrp.hom_ext ψ (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := KerGrp.hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hKfin : IsFinite (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (IwLevel.ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact HTTorsionFF.flat_of_retract _ iK.left r.left hirl
  refine ⟨IwLevel.ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hj, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨KerGrp.lift (jH ≫ fx) (KerGrp.lift ψ z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

def subEquiv {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) [Mono i] (P : (T ⟶ A) → Prop)
    (h : ∀ x, GlobalTheory.IwLevel.InSub i x ↔ P x) : (T ⟶ K) ≃ {x : T ⟶ A // P x} :=
  Equiv.ofBijective (fun g => ⟨g ≫ i, (h _).1 ⟨g, rfl⟩⟩)
    ⟨fun g g' hgg => (cancel_mono i).1 (congrArg Subtype.val hgg),
     fun x => let ⟨g, hg⟩ := (h x.1).2 x.2; ⟨g, Subtype.ext hg⟩⟩

def fibreEquiv {S T : Scheme.{0}} (K : Over S) (y : T ⟶ S) :
    (Over.mk y ⟶ K) ≃ {s : T ⟶ pullback K.hom y // s ≫ pullback.snd K.hom y = 𝟙 _} where
  toFun g := ⟨pullback.lift g.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
  invFun s := Over.homMk (s.1 ≫ pullback.fst K.hom y) (by
    change (s.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp])
  left_inv g := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  right_inv s := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans s.2.symm))

theorem eq_one_of_reg {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {T : Over S} (x : T ⟶ A) (c : ℕ)
    (hc : ∀ (U : T.left.Opens) (f : Γ(T.left, U)), (c : Γ(T.left, U)) * f = 0 → f = 0) (hx : x ^ c = 1)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) :
    x = 1 := by
  obtain ⟨U, j, hj, hu⟩ := GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor T.left c hc
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j
  have h1 : j' ≫ x = 1 := GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric S A hA _ (j' ≫ x) c hu (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (fun k _ _ hk z g => by rw [← Category.assoc]; exact h k hk z _)
  have h2 : j' ≫ x = j' ≫ 1 := by rw [h1, MonObj.comp_one]
  have := hA.proper
  exact Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isSchemeTheoreticallyDominant j A.hom
    (congrArg CommaMorphism.left h2) (by rw [Over.w, Over.w]))

end GlobalTheory.UPel.HT.ES.OrdCount
end
end
