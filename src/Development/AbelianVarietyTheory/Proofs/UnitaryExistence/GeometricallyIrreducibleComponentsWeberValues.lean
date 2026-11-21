import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodSpacesFixedByCmCurveTorsionFixingAutomorph
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodSpaces_fixed_by_cmCurveTorsionFixingAutomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → FixesCurve H τ l.M' → ConjugationPermutesPeriods F τ id := by
  first | exact @GlobalTheory.CompRat.AnyLevel.permutes_id_of_fixesCurve | exact GlobalTheory.CompRat.AnyLevel.permutes_id_of_fixesCurve | (intros; apply GlobalTheory.CompRat.AnyLevel.permutes_id_of_fixesCurve <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConstLevel

open Polynomial GlobalTheory.CompRat.FixedConst

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed Xo c := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, (RingHom.ext hA : σ = algebraMap (KA l) ℂ), ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F h1 hσ hty c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConstLevel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed Xo c := by
  atlas_forward_decl GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M' → FnAlgClosed Xo c := by
  intro E _ _ _ H D l Xo c hD hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) c fun τ hτ => ?_
  exact GlobalTheory.T.periodSpaces_fixed_by_cmCurveTorsionFixingAutomorphism E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) hsig τ (fun x => hτ _ (c.le x.2)) (hC τ hτ)

end GlobalTheory.CompRat
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat

namespace GlobalTheory.FinalJoin.FieldAlg

theorem fnAlgClosed_of_weberIn : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed Xo' c' := by
  intro D Q hP j hj l' Xo' c' n hn hM hW
  obtain ⟨⟨ι, hι⟩, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := GlobalTheory.RankOneDatum.exists_datum_rank_one D Q.H (Q.Dw j) (D.sp.W j) ι hι (by omega)
  have h0 : Q.H.rt0 ∈ c'.F := c'.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hC := GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ Q.H c'.F n hn
  have hc : CurveOver Q.H c'.F l'.M' := hC.2 _ hM (hW.elim (hC.1 h0) id)
  exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver_lcm _ Q.H (Q.Dw j) l' Xo' c' (by omega)
    (Or.inr (Or.inr ⟨by omega, h1⟩)) hc

end GlobalTheory.FinalJoin.FieldAlg
end
