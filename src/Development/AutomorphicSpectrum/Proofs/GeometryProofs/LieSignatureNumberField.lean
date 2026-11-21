import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ShimuraDatumTateIsomorphism
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralPointExtendsModel
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TrivialTypeGoodReduction
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionFieldOfDefinition
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ModelObjectSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem datum_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :=
  @PositivityTheory.Xgn.shimura_datum_tate_isomorphism

end GlobalTheory.CompanionTheory.Ar.SabModel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_datum_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SabModel.datum_tate
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem model_point_extends_to_integers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j :=
  @PositivityTheory.Xgn.integral_point_extends_model

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_point_integral_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TrivialModel

theorem exists_model_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) :=
  @PositivityTheory.Xgn.trivial_type_good_reduction

end GlobalTheory.CompanionTheory.Ar.TrivialModel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_good_reduction_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsion_defined_over_numberField : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left :=
  @PositivityTheory.Xgn.torsion_field_of_definition

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_number_field : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem obj_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t :=
  @PositivityTheory.Xgn.model_object_sections

end GlobalTheory.CompanionTheory.Ar.SabModel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_lie_multiplicity_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SabModel.obj_of_sections
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_obj_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → l.A = 1 → ∀ (ρ : L) (σ : L →+* ℂ),
    σ ρ = H.rt0 →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ D.q)) →
    TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)) →
    ∀ (F₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ F₀ → ∀ hK : KA l ≤ F₀,
    ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (hF : F₀ ≤ F) (e : L →+* F)
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion (hK.trans hF)).toRingHom)),
      (∀ x, ((e x : F) : ℂ) = σ x) ∧ Nonempty (SABMap o.t t (spMap e)) := by
  intro E _ _ _ H D l L _ _ t ht hA ρ σ hσ hs I F₀ hF₀ hK
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨F₁, hF₁, e₁, he₁, hT⟩ := GlobalTheory.T.torsion_points_number_field L σ (pol t ht) l.M hM
  have hfin : FiniteDimensional ℚ ↥(F₀ ⊔ F₁) := inferInstance
  let i₁ : F₁ →+* ↥(F₀ ⊔ F₁) := (IntermediateField.inclusion le_sup_right).toRingHom
  let e : L →+* ↥(F₀ ⊔ F₁) := i₁.comp e₁
  have he : ∀ x, ((e x : ↥(F₀ ⊔ F₁)) : ℂ) = σ x := he₁
  obtain ⟨t₂, ⟨m⟩⟩ := exists_sab (spMap e) t
  obtain ⟨w, gw, -⟩ := m.lin
  have hL₂ : LBIso t₂.PP.L (t.PP.L.pull m.cm.F) := ⟨w, gw⟩
  have ht₂ : IsPrincipal t₂ :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 ht.1,
      relAmple_pull m.cart.1 t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ht.2.1,
      kTriv_pull m.cart t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ht.2.2⟩
  let x₂ : Sp ℂ ⟶ Sp ↥(F₀ ⊔ F₁) := spMap (algebraMap ↥(F₀ ⊔ F₁) ℂ)
  have hx : x₂ ≫ spMap e = spMap σ := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext he)
  obtain ⟨Φ, hΦ, hW⟩ : ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk (spMap σ) ⟶ t.G),
      (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
        Out.WeilIs t₂.G t₂.PP.L k x y c := by
    have key : ∀ y : Sp ℂ ⟶ Sp L, x₂ ≫ spMap e = y → ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk y ⟶ t.G),
        (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
          Out.WeilIs t₂.G t₂.PP.L k x y c := by
      rintro _ rfl
      exact ⟨GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x₂), fun _ => rfl, fun k x y c h =>
        GlobalTheory.Relabel.weilIs_push t.PP.isLB t₂.PP.isLB m.cart hL₂ (Over.mk x₂) _ rfl k x y _ _ c rfl rfl h⟩
    exact key _ hx
  let I₂ : TateIso D ℂ (Over.mk x₂ ⟶ t₂.G) (fun a g => g ≫ t₂.act.act a)
      (fun n g g' c => Out.WeilIs t₂.G t₂.PP.L n g g' (unitOn c)) :=
    GlobalTheory.ObjPull.tateMove Φ (fun c x => Over.OverMorphism.ext (by
      show (Φ _).left = (Φ x ≫ _).left
      rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
      exact congrArg _ (m.act c))) (fun n x y c h => hW n x y _ h) I
  have hsec : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp ↥(F₀ ⊔ F₁))) ⟶ t₂.G, toUnit _ ≫ s = I₂.ev l.M a := fun a => by
    obtain ⟨y₁, hy₁, hy₂⟩ : ∃ y : Sp F₁ ⟶ t.G.left, y ≫ t.G.hom = spMap e₁ ∧
        spMap (algebraMap F₁ ℂ) ≫ y = (I.ev l.M a).left := hT (I.ev l.M a) ((I.onto l.M hM _).2 ⟨a, rfl⟩)
    have hw₁ : (spMap i₁ ≫ y₁) ≫ t.G.hom = 𝟙 _ ≫ spMap e := by
      rw [Category.assoc]
      refine (congrArg (spMap i₁ ≫ ·) hy₁).trans ?_
      rw [Category.id_comp]
      exact (spMap_comp _ _).symm
    refine ⟨Over.homMk (m.cart.1.lift _ _ hw₁) (m.cart.1.lift_snd _ _ _), ?_⟩
    apply Φ.injective
    show Φ _ = Φ (Φ.symm _)
    rw [MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [hΦ, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    show (x₂ ≫ m.cart.1.lift _ _ hw₁) ≫ m.φ = _
    rw [Category.assoc]
    refine (congrArg (x₂ ≫ ·) (m.cart.1.lift_fst _ _ hw₁)).trans ?_
    rw [← hy₂, ← Category.assoc]
    exact congrArg (· ≫ y₁) (spMap_comp _ _).symm
  have hK₂ : KA l ≤ F₀ ⊔ F₁ := hK.trans le_sup_left
  have hρ : IntermediateField.inclusion hK₂ (baseKA l).ρ = e ρ := Subtype.ext (by
    refine Eq.trans ?_ (he ρ).symm
    rw [hσ]
    rfl)
  obtain ⟨o, ho⟩ := GlobalTheory.T.principal_lie_multiplicity_type E H D l (F₀ ⊔ F₁) hK₂ t₂ ht₂ hA (fun k _ _ g τ => by
    have hp : ∀ n, LieMult t₂.act (spMap g) τ n ↔ LieMult t.act (spMap (g.comp e)) τ n := fun n =>
      (GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ _ t.act t₂.act m.cart m.act k (spMap g) τ n).trans
        (iff_of_eq (congrArg (fun x => LieMult t.act x τ n) (spMap_comp _ _).symm))
    have h := hs k (g.comp e) τ
    rw [hρ, hp, hp]
    exact h) I₂ hsec
  refine ⟨F₀ ⊔ F₁, hfin, le_sup_left, e, o, he, ?_⟩
  rw [ho]
  exact ⟨m⟩

theorem exists_embedding_rt0 {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {L : Type} [Field L]
    [NumberField L] (ρ : L) (hρ : ρ ^ 2 = -(H.d : L)) : ∃ σ : L →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have h : (σ₀ ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ₀, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ₀, ?_⟩
    have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
      have hre : H.rt0.re = 0 := by
        have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
          have := congrArg Complex.im H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_im] using this
        have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
          have := congrArg Complex.re H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_re] using this
        have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
        rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
        · exact h3
        · rw [h3] at h2
          nlinarith [mul_self_nonneg H.rt0.re]
      apply Complex.ext <;> simp [hre]
    show starRingEnd ℂ (σ₀ ρ) = _
    rw [h, map_neg, hc, neg_neg]

theorem exists_sab_model : N1ab → PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q')) → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (t' : SAB H (Sp (𝓞 L'))) (tK : SAB H (Sp L')), Nonempty (SABMap tK t' (spMap (algebraMap (𝓞 L') L'))) ∧ Nonempty (SABMap tK t (spMap e)) := by
  intro hN hP E _ _ _ H L _ _ t ht ⟨ρ, p', q', hρ, hs⟩
  by_cases h0 : p' + q' = 0
  · obtain ⟨rfl, rfl⟩ : p' = 0 ∧ q' = 0 := by omega
    obtain ⟨t', ⟨m⟩⟩ := GlobalTheory.T.principal_good_reduction_extends E H L t ht fun σ τ => by
      by_cases h : τ H.rt = σ ρ
      · exact (hs ℂ σ τ).1 h
      · exact (hs ℂ σ τ).2 h
    exact ⟨L, inferInstance, inferInstance, RingHom.id L, t', t, ⟨m⟩,
      ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast (GlobalTheory.ObjComp.sabMapId t) (Spec.map_id _).symm⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_embedding_rt0 H ρ hρ
    obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := GlobalTheory.T.tate_iso_datum_exists E H L t ht σ p' q' fun τ => by
      have := hs ℂ σ τ
      rwa [hσ] at this
    have hD : 1 ≤ D.p + D.q := by omega
    let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l hD).some
    obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
    obtain ⟨c⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
    haveI := c.fin
    obtain ⟨Yl, -, h6⟩ := hP.2 E H D hD Xo
    obtain ⟨Y, -, -⟩ := h6 l c hg hA
    obtain ⟨F, hfin, hF, e, o, -, ⟨m⟩⟩ := exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
    haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
    obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
    let bF : c.F →+* F := (IntermediateField.inclusion hF).toRingHom
    let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
      rw [hf, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl))
    have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
    have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
    obtain ⟨yt, hyt⟩ := GlobalTheory.T.number_field_point_integral_lift E H D l (Xo l) c c.fin Y F bF y hy2
    obtain ⟨t', ⟨m'⟩⟩ := exists_sab yt Y.t
    rw [← hy1] at mf
    obtain ⟨m₁, -⟩ := ObjComp.objMap_cancel Y.m0 mf
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m₁.toSABMap
    have n' : SABMap o.t Y.t (spMap (algebraMap (𝓞 F) F) ≫ yt) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n (by
      rw [hyt]; rfl)
    obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m' n'
    exact ⟨F, inferInstance, inferInstance, e, t', o.t, ⟨k⟩, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end
