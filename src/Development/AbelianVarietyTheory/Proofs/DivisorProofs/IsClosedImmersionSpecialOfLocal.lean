import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtension

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory.TorusFieldCrit

theorem exists_prime_hom_of_not_surjective {X : Type} [AddCommGroup X] {r : ℕ}
    (M : X →+ (Fin r → ℤ)) (hM : ¬ Function.Surjective M) :
    ∃ p : ℕ, p.Prime ∧ ∃ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 ∧ φ.comp M = 0 := by
  obtain ⟨y, hy⟩ := not_forall.1 hM
  have hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range) :=
    ⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩
  haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance
  obtain ⟨n, κ, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)
  suffices h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by
    obtain ⟨q, hq, ψ, hψ⟩ := h
    haveI := Fact.mk hq
    refine ⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hψ 1
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective M.range x
      have := DFunLike.congr_fun h z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
      rw [this] at hx
      exact zero_ne_one hx
    · ext x
      simp [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]
  by_cases hn : 0 < n
  · refine ⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp
        ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩
    simp
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      apply not_subsingleton ((Fin r → ℤ) ⧸ M.range)
      refine ⟨fun a b => f.injective ?_⟩
      have key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0 := fun x => by
        refine Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)
        haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [key (f a), key (f b)]
    classical
    haveI := Fact.mk (hp i)
    refine ⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp
      ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
      DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_intCast (dvd_pow_self (p i) hi) k

theorem isClosedImmersion_of_torusExtension (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω)))
    [GrpObj H] (E : TorusExtension H) (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H)
    (hv : IsMonHom v)
    (hker : ∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 →
      GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) :
    IsClosedImmersion v.left := by
  letI := E.addCommGroup; letI := E.grpB
  haveI := E.free; haveI := E.finite
  haveI := E.i_hom; haveI := E.q_hom; haveI := E.isAbelian.proper
  haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω
  have h1 : v ≫ E.q = toUnit _ ≫ η[E.B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance
  let w := E.isKernel.lift v (toUnit _) h1
  have hw : w ≫ E.i = v := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := ⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩
  haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by
    rw [← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw,
      MonObj.mul_comp]
  obtain ⟨M, hM⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap w
  by_cases hs : Function.Surjective M
  · have hdiag : w = GlobalTheory.Diag.diagMap _ M := by
      rw [hM]; symm
      exact (GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b
    have hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])
    have hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      E.isKernel.map (Over.forget _)
    have hi : IsClosedImmersion E.i.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
    have hw' : IsClosedImmersion w.left := hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs
    rw [← hw, Over.comp_left]
    infer_instance
  · exfalso
    obtain ⟨p, hp, φ, hφ, hφM⟩ := exists_prime_hom_of_not_surjective M hs
    apply hker p hp φ hφ
    rw [← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero,
      MonObj.one_comp]

end GlobalTheory.TorusFieldCrit
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension : ∀ (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω))) [GrpObj H], TorusExtension H → ∀ (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H), IsMonHom v → (∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 → GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) → IsClosedImmersion v.left := by
  atlas_forward_decl GlobalTheory.TorusFieldCrit.isClosedImmersion_of_torusExtension
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_of_baseChange_field_ext : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  first | exact @GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | exact GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | (intros; apply GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine GlobalTheory.T.closedImmersion_of_baseChange_field_ext R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
end
end
