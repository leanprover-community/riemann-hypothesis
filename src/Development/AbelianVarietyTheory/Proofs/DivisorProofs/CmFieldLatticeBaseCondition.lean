import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationNonarchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImaginaryGeneratorCmType
import BuildAid.ForwardExisting

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_ring_over_prime : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ R : Subring ℂ, IsPlaceOver l lam k R := by
  first | exact @GlobalTheory.PlaceRingExists.exists_isPlaceOver | exact GlobalTheory.PlaceRingExists.exists_isPlaceOver | (intros; apply GlobalTheory.PlaceRingExists.exists_isPlaceOver <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem norm_ratCast_padicComplex_le_one (l : ℕ) [Fact l.Prime] (q : ℚ) (hq : 0 ≤ padicValRat l q) :
    ‖(q : ℂ_[l])‖ ≤ 1 := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by
    exact map_ratCast (algebraMap ℚ_[l] ℂ_[l]) q
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]
  by_cases h0 : q = 0
  · subst h0; simp
  · rw [padicNorm.eq_zpow_of_nonzero h0]
    have hl : (1 : ℚ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
    exact_mod_cast zpow_le_one_of_nonpos₀ hl (by omega)

theorem eventually_isPlaceRing (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) : Eventually l lam (IsPlaceRing E l lam) := by
  classical
  let t : (E →+* ℂ) → IntermediateField ℚ ℂ := fun σ ↦ σ.toRatAlgHom.fieldRange
  haveI : ∀ σ, FiniteDimensional ℚ (t σ) := fun σ ↦
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ.toRatAlgHom).toLinearEquiv
  refine ⟨⨆ σ, t σ, IntermediateField.finiteDimensional_iSup_of_finite, fun R hR ↦ ?_⟩
  obtain ⟨hdvr, hsz, hmem⟩ := hR
  refine ⟨hdvr, hsz, fun q hq ↦ ?_, fun σ x ↦ ?_⟩
  · have hk : (q : ℂ) ∈ ⨆ σ, t σ := by
      simpa using IntermediateField.algebraMap_mem (⨆ σ, t σ) q
    have hqa : (q : ℂ) ∈ algebraicClosure ℚ ℂ := by
      simpa using (algebraicClosure ℚ ℂ).algebraMap_mem q
    refine hmem _ hk ⟨hqa, ?_⟩
    have e : (⟨(q : ℂ), hqa⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
      ext; simp
    rw [e, map_ratCast, Real.rpow_zero]
    exact norm_ratCast_padicComplex_le_one l q hq
  · have hk : σ x ∈ ⨆ σ, t σ :=
      (le_iSup t σ) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have ha : σ x ∈ algebraicClosure ℚ ℂ :=
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
    by_cases hn : ‖lam ⟨σ x, ha⟩‖ ≤ 1
    · refine ⟨σ x, hmem _ hk ⟨ha, by rwa [Real.rpow_zero]⟩, 1, R.one_mem, one_ne_zero, mul_one _⟩
    · push_neg at hn
      have h0 : σ x ≠ 0 := by
        intro h
        have : (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ) = 0 := Subtype.ext h
        rw [this, map_zero, norm_zero] at hn
        linarith
      have hia : (σ x)⁻¹ ∈ algebraicClosure ℚ ℂ := inv_mem ha
      have hik : (σ x)⁻¹ ∈ ⨆ σ, t σ := inv_mem hk
      have e : (⟨(σ x)⁻¹, hia⟩ : algebraicClosure ℚ ℂ) = (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ)⁻¹ := by
        ext; simp
      have hs : Sz l lam 0 (σ x)⁻¹ := by
        refine ⟨hia, ?_⟩
        rw [e, map_inv₀, norm_inv, Real.rpow_zero]
        exact inv_le_one_of_one_le₀ hn.le
      exact ⟨1, R.one_mem, (σ x)⁻¹, hmem _ hik hs, inv_ne_zero h0, mul_inv_cancel₀ h0⟩

end GlobalTheory.LatModel

example : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    GlobalTheory.LatModel.Eventually l lam (GlobalTheory.LatModel.IsPlaceRing E l lam) := GlobalTheory.LatModel.eventually_isPlaceRing
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_place_ring : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    Eventually l lam (IsPlaceRing E l lam) := by
  atlas_forward_decl GlobalTheory.LatModel.eventually_isPlaceRing
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatTorusAct

open scoped IntermediateField

theorem finrank_adjoin_sqrt_neg {E : Type} [Field E] [CharZero E] (d : ℕ) (hd : 0 < d) (w : E) (hw : w ^ 2 = -(d : E)) :
    Module.finrank ℚ ℚ⟮w⟯ = 2 := by
  have hint : IsIntegral ℚ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hw]
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly ℚ w ∣ Polynomial.X ^ 2 + Polynomial.C (d : ℚ) := minpoly.dvd _ _ (by simp [hw])
  have hle : (minpoly ℚ w).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_add_C (d : ℚ) (by norm_num)).ne_zero
    rwa [Polynomial.natDegree_X_pow_add_C] at this
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ w).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := (minpoly.natDegree_eq_one_iff).1 h1
    have h2 : ((q ^ 2 : ℚ) : E) = ((-(d : ℚ) : ℚ) : E) := by
      rw [Rat.cast_pow]; push_cast
      have : (algebraMap ℚ E q) = (q : E) := rfl
      rw [← this, hq, hw]
    have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
    have h4 : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg q]
  omega

theorem ringHom_ext_adjoin {E R : Type} [Field E] [CharZero E] [Field R] [CharZero R] (w : E)
    (f g : ℚ⟮w⟯ →+* R) (h : f (IntermediateField.AdjoinSimple.gen ℚ w) = g (IntermediateField.AdjoinSimple.gen ℚ w)) : f = g := by
  have : f.toRatAlgHom = g.toRatAlgHom := by
    refine IntermediateField.adjoin_algHom_ext ℚ ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h
  ext x
  exact DFunLike.congr_fun this x

theorem exists_unif_act_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α := by
  intro E _ _ _ I _ d φ hF c y hc
  obtain ⟨hdp, -, -, -, -, hcard, hcm, w, hw, hφw⟩ := hF
  have hd : 0 < d := hdp.pos
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  let δ : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hδ : δ ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [δ] using hw)
  have hagree : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) = (φ i₀).comp (algebraMap ℚ⟮w⟯ E) := fun i ↦
    ringHom_ext_adjoin w _ _ (by
      show φ i w = φ i₀ w
      rw [hφw, hφw])
  obtain ⟨𝔠, X, U, -⟩ := GlobalTheory.T.cm_abelian_variety_uniformization_exists ℚ⟮w⟯ d δ ((φ i₀).comp (algebraMap ℚ⟮w⟯ E))
    (finrank_adjoin_sqrt_neg d hd w hw) hd hδ E I φ hcm hagree c y hc
  refine ⟨𝔠, X, U, fun a ↦ ?_⟩
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v j ↦ φ (U.e j) (a : E) * v j
      map_add' := fun v v' ↦ by ext j; simp [mul_add]
      map_smul' := fun s v ↦ by ext j; simp; ring }
  have hT : ∀ v ∈ U.u.Λ, T v ∈ U.u.Λ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (U.lat v).1 hv
    refine (U.lat _).2 ⟨(a : E) * x, mul_mem_lattice a.2 hx, ?_⟩
    ext j
    simp [T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice (FR E) 𝔠 X _ _ U.u T hT
  exact ⟨α, hα, hαe⟩

end GlobalTheory.LatTorusAct
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_uniformization_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α := by
  atlas_forward_decl GlobalTheory.LatTorusAct.exists_unif_act_orderC
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem finite_int_orderC : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), Module.Finite ℤ (orderC c) := by
  intro E _ _ c
  have hint : ∀ x : orderC c, IsIntegral ℤ (x : E) := by
    intro x
    obtain ⟨a, b, -, h⟩ := mem_orderC.1 x.2
    have h2 : (x : E) = ((algebraMap (OF E) (𝓞 E) a + b : 𝓞 E) : E) := by
      rw [h]; first | rfl | (push_cast; rfl)
    rw [h2]
    exact RingOfIntegers.isIntegral_coe _
  let f : orderC c →ₗ[ℤ] 𝓞 E :=
    { toFun := fun x => ⟨x, hint x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f ?_
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : 𝓞 E => (z : E)) hxy)

end GlobalTheory.LatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_order_finite_integers : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), Module.Finite ℤ (orderC c) := by
  atlas_forward_decl GlobalTheory.LatModel.finite_int_orderC
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

section ModelOver

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

namespace GlobalTheory.CMModel

theorem exists_obj_of_isGrpPullback_over (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) {S₀ : Scheme.{0}} (G₀ : Over S₀) [GrpObj G₀]
    (b : Sp Qb ⟶ S₀) (g : A₀.left ⟶ G₀.left) (hg : IsGrpPullback A₀ G₀ b g) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p' : X.A.left ⟶ X₀.A.left) (g' : X₀.A.left ⟶ G₀.left),
      X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p' ∧ IsGrpPullback X₀.A G₀ b g' ∧ p' ≫ g' = p ≫ g := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
    obtain ⟨b₁, b₂⟩ := additive_ev q₀.isLB q₀.additive q₀'.additive x₀
    refine ⟨_, pull_isLB q₀.isLB _, b₁, b₂, ?_⟩
    rw [cls_ev q₀.isLB, ex]
    exact pull_evc_eq l₁ l₂ m₁ m₂ q₀.isLB q.isLB e₀.symm
  choose P₀ hP₀ a₁ a₂ eP using hx
  have inj : ∀ {P P' : LB (A₀ ⊗ A₀).left} (hP : P.IsLB) (hP' : P'.IsLB), IsAdditive P → IsAdditive P' →
      CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP') → LBIso P P' := fun hP hP' a a' e ↦
    (cls_eq_iff hP hP').1 (cls_eq_of_pull hp.1 hd l₁ l₂ m₁ m₂ q₀ q hP hP' a a' e)
  have iso : ∀ c, LBIso ((P₀ c).pull l) (X.P c) := fun c ↦
    (cls_eq_iff (pull_isLB (hP₀ c) _) (X.isLB c)).1 (by rw [cls_pull (hP₀ c)]; exact eP c)

  have val : ∀ (c : 𝔠.elt) {Y₀ : Over (Sp Qb)} {Y : Over (Sp ℂ)} (r : Y.left ⟶ Y₀.left) (a₀ t₀ : Y₀ ⟶ A₀)
      (a t : Y ⟶ X.A), a.left ≫ p = r ≫ a₀.left → t.left ≫ p = r ≫ t₀.left →
      CechPic.pull r (evc (hP₀ c) a₀ t₀) = evc (X.isLB c) a t := fun c Y₀ Y r a₀ t₀ a t ha ht ↦ by
    rw [evc, evc, ← eP, ← pull_comp, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₁, lift_left_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₂, lift_left_snd_assoc, ht]
  refine ⟨{ A := A₀
            ab := hA₀
            dim := gA₀
            rm := rm
            P := P₀
            isLB := hP₀
            rig₁ := fun c ↦ triv_left (hP₀ c) (a₁ c)
            rig₂ := fun c ↦ triv_right (hP₀ c) (a₂ c)
            symm := fun c ↦ ?_
            add := fun c c' ↦ ?_
            smul := fun a c ↦ ?_
            pos := fun c hc ↦ ?_
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, g, ⟨hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩, hg, rfl⟩
  · refine inj (hP₀ c) (pull_isLB (hP₀ c) _) (a₁ c) (a₂ c) ?_
    rw [eP, cls_ev (hP₀ c), val c l _ _ _ _ l₂.symm l₁.symm]
    exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.symm c)
  · have hq := LB.isLB_div (hP₀ (c + c')) (hP₀ c)
    have ev' : ∀ (Y : Over (Sp Qb)) (a t : Y ⟶ A₀), evc hq a t = evc (hP₀ (c + c')) a t - evc (hP₀ c) a t :=
      fun Y a t ↦ by rw [evc, cls_div (hP₀ (c + c')) (hP₀ c), map_sub]; rfl
    refine inj (hP₀ c') hq (a₁ c') ((isAdditive_iff hq).2 fun Y a a' t ↦ ?_) ?_
    · rw [ev', ev', ev', (isAdditive_iff (hP₀ _)).1 (a₁ _), (isAdditive_iff (hP₀ _)).1 (a₁ _)]
      abel
    · rw [cls_div (hP₀ (c + c')) (hP₀ c), map_sub, eP, eP, eP, ← cls_div (X.isLB (c + c')) (X.isLB c)
        (LB.isLB_div (X.isLB (c + c')) (X.isLB c))]
      exact (cls_eq_iff _ _).2 (X.add c c')
  · have hq : (ev (P₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).IsLB := pull_isLB (hP₀ c) _
    refine inj (hP₀ _) hq (a₁ _) ((isAdditive_iff hq).2 fun Y u u' t ↦ ?_) ?_
    · simp only [evc_ev (hP₀ c), lift_fst, lift_snd_assoc]
      exact (isAdditive_iff (hP₀ c)).1 (a₁ c) _ _ _ _
    · rw [eP, cls_ev (hP₀ c), val c l _ _ (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) l₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hrm, ← Category.assoc, ← Category.assoc, l₂])]
      exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  · refine AmpleDescent.relAmple_of_fieldExtension Qb ℂ _ A₀ X.A p _ _ hA₀ hp (pull_isLB (hP₀ c) _)
      (pull_isLB (X.isLB c) _) ((cls_eq_iff (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (hP₀ c) _) _)).1 ?_)
      (X.pos c hc)
    rw [cls_pull (pull_isLB (hP₀ c) _), cls_ev (hP₀ c), cls_ev (X.isLB c)]
    exact (val c p _ _ _ _ (by simp) (by simp)).symm
  · let T : Over (Sp ℂ) := (Over.pullback (spMap (algebraMap Qb ℂ))).obj T₀
    let r : T.left ⟶ T₀.left := Limits.pullback.fst _ _
    have hr : IsPullback r T.hom T₀.hom (spMap (algebraMap Qb ℂ)) := IsPullback.of_hasPullback _ _
    have w : (r ≫ x.left) ≫ A₀.hom = T.hom ≫ spMap (algebraMap Qb ℂ) := by rw [Category.assoc, Over.w x, hr.w]
    let x' : T ⟶ X.A := liftPt hp T.hom _ w
    have ex : x'.left ≫ p = r ≫ x.left := liftPt_left hp _ _ w
    let u : Over.mk ((X.A ⊗ T).hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk ((snd X.A T).left ≫ r) (by
      change ((snd X.A T).left ≫ r) ≫ T₀.hom = _
      rw [Category.assoc, hr.w, ← Category.assoc, Over.w]
      rfl)
    let s : (X.A ⊗ T).left ⟶ (A₀ ⊗ T₀).left := (lift (pushP hp (s := (X.A ⊗ T).hom) rfl (fst X.A T)) u).left
    have s₁ : s ≫ (fst A₀ T₀).left = (fst X.A T).left ≫ p := lift_left_fst _ _
    have s₂ : s ≫ (snd A₀ T₀).left = (snd X.A T).left ≫ r := lift_left_snd _ _
    have z : evc (X.isLB c) (fst X.A T) (snd X.A T ≫ x') = 0 := by
      rw [← val c s (fst A₀ T₀) (snd A₀ T₀ ≫ x) _ _ s₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, ex, ← Category.assoc, ← Category.assoc, s₂]),
        (triv_ev_iff (hP₀ c) _ _).1 hx, map_zero]
    have k := X.ker c T x' ((triv_ev_iff (X.isLB c) _ _).2 z) a ha
    refine ActDescent.over_hom_ext hr ?_
    rw [Over.comp_left, ← Category.assoc, ← ex, Category.assoc, ← hrm, ← Category.assoc, ← Over.comp_left, k]
    refine (one_left_comp hp (s := T.hom) rfl).trans ?_
    let r' : Over.mk (T.hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk r hr.w
    exact congrArg (fun y ↦ y.left) (MonObj.comp_one (M := A₀) r').symm
  · exact (cls_eq_iff (X.isLB c) (pull_isLB (hP₀ c) _)).1 (by rw [cls_pull (hP₀ c)]; exact (eP c).symm)

end GlobalTheory.CMModel

end ModelOver

namespace GlobalTheory.CMModel

open GlobalTheory.ComplexPoints
open scoped CategoryTheory.Obj

theorem exists_qbModel_of_subring : GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (L : Set E) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (R₀ : Subring ℂ) (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left), IsAbelianScheme G₀ →
      IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ →
    ∃ (XQ : Obj (FR E) 𝔠 (Sp Qb)) (pQ : X.A.left ⟶ XQ.A.left) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct (orderC c) XQ.A),
      X.IsPullBy XQ (spMap (algebraMap Qb ℂ)) pQ ∧ IsGrpPullback XQ.A G₀ (spMap σ) gQ ∧ pQ ≫ gQ = p₀ ∧
      (∀ a : OF E, cmQ.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = XQ.rm.act a) ∧
      ∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
        (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ pQ = pQ ≫ (cmQ.act a).left := by
  intro HD E _ _ _ I _ φ c L 𝔠 X U hα R₀ σ hσ G₀ _ p₀ _ hpb

  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  have hring : R₀.subtype = (algebraMap Qb ℂ).comp σ := RingHom.ext fun x ↦ (hσ x).symm
  have hcomp : spMap R₀.subtype = spMap (algebraMap Qb ℂ) ≫ spMap σ := by
    rw [hring]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let A₀ : Over (Sp Qb) := (Over.pullback (spMap σ)).obj G₀
  letI : GrpObj A₀ := inferInstanceAs (GrpObj ((Over.pullback (spMap σ)).obj G₀))
  have hA₀G : IsGrpPullback A₀ G₀ (spMap σ) (pullback.fst G₀.hom (spMap σ)) := isGrpPullback_pullback G₀ (spMap σ)
  let p : X.A.left ⟶ A₀.left := pullback.lift p₀ (X.A.hom ≫ spMap (algebraMap Qb ℂ)) (by
    rw [Category.assoc, ← hcomp]; exact hpb.1.w)
  have hp₁ : p ≫ pullback.fst G₀.hom (spMap σ) = p₀ := pullback.lift_fst _ _ _
  have hp₂ : p ≫ A₀.hom = X.A.hom ≫ spMap (algebraMap Qb ℂ) := pullback.lift_snd _ _ _
  have hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p :=
    IsGrpPullback.cancel hA₀G (by rw [hp₁, ← hcomp]; exact hpb) hp₂
  obtain ⟨hA₀, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend Qb ℂ (algebraMap Qb ℂ) A₀ X.A p hp X.ab

  obtain ⟨XQ, pQ, gQ, hXQ, hgQ, hpg⟩ := exists_obj_of_isGrpPullback_over HD.1 X U.c U.pos A₀ p hA₀ (hdim _ X.dim) hp
    G₀ (spMap σ) _ hA₀G

  let ρ : orderC c →+* Module.End ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    (Algebra.lmul ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ)).toRingHom.comp
      ((Pi.ringHom fun j ↦ φ (U.e j)).comp (orderC c).subtype)
  have hρ : ∀ a w, ρ a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ rfl
  have hlat : ∀ a, ∀ z ∈ U.u.Λ, ρ a z ∈ U.u.Λ := fun a z hz ↦ by
    obtain ⟨α, hαm, hαe⟩ := hα a
    haveI := hαm
    rw [← U.u.ker] at hz ⊢
    rw [hρ, hαe, hz, MonObj.one_comp]
  obtain ⟨act, hact⟩ := GlobalTheory.TorusAction.exists_oAct_of_map_lattice _ X.A X.ab _ U.u (orderC c) ρ hlat
  haveI := X.ab.smooth
  haveI := X.ab.proper
  haveI : IsReduced X.A.left := isReduced_of_smooth_complex _ X.A.hom X.ab.smooth
  have hext : ∀ f f' : X.A ⟶ X.A, (∀ z, U.u.ex z ≫ f = U.u.ex z ≫ f') → f = f' := fun f f' h ↦
    over_hom_ext_of_complexPoints fun x ↦ by
      obtain ⟨z, rfl⟩ := U.u.ex_onto x
      exact h z
  have huniq : ∀ (a : orderC c) (α : X.A ⟶ X.A),
      (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α = act.act a := fun a α h ↦
    hext _ _ fun z ↦ by rw [← h, ← hact, hρ]

  obtain ⟨cmQ, hcm⟩ := GlobalTheory.ActDescent.exists_oAct hXQ.grp act fun a ↦ by
    haveI := act.hom a
    obtain ⟨β, -, hβ⟩ := GlobalTheory.RealMult.Obj.exists_end_descend_algebraic _ _ XQ X pQ hXQ (act.act a)
    exact ⟨β, hβ⟩
  refine ⟨XQ, pQ, gQ, cmQ, hXQ, hgQ, by rw [hpg, hp₁], fun a ↦ ?_, fun a α _ h ↦ ?_⟩
  · refine GlobalTheory.ActDescent.over_hom_ext hXQ.grp.1 ?_
    rw [← hcm, ← hXQ.act a]
    congr 2
    exact (huniq _ _ (U.act a)).symm
  · rw [huniq a α h]
    exact hcm a

end GlobalTheory.CMModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_uniformization_algebraic_model : GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (L : Set E) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (R₀ : Subring ℂ) (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left), IsAbelianScheme G₀ →
      IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ →
    ∃ (XQ : Obj (FR E) 𝔠 (Sp Qb)) (pQ : X.A.left ⟶ XQ.A.left) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct (orderC c) XQ.A),
      X.IsPullBy XQ (spMap (algebraMap Qb ℂ)) pQ ∧ IsGrpPullback XQ.A G₀ (spMap σ) gQ ∧ pQ ≫ gQ = p₀ ∧
      (∀ a : OF E, cmQ.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = XQ.rm.act a) ∧
      ∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
        (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ pQ = pQ ≫ (cmQ.act a).left := by
  atlas_forward_decl GlobalTheory.CMModel.exists_qbModel_of_subring
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_endomorphism_place_integral : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (O : Type) [CommRing O] (ofO : 𝓞 F → O) (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), Module.Finite ℤ O →
    FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ → (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left → Flat Ψ₀.left → Surjective Ψ₀.left →
    ∀ (XQ : Obj F 𝔠 (Sp Qb)) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct O XQ.A), IsGrpPullback XQ.A G₀ (spMap σ) gQ →
      (∀ a, cmQ.act (ofO a) = XQ.rm.act a) →
      Eventually l lam fun R ↦ ∀ (ic : R₀ →+* R) (j : R →+* Qb), (∀ x, ((ic x : R) : ℂ) = x) → (∀ x, ((j x : Qb) : ℂ) = x) →
        ∃ (X₀ : Obj F 𝔠 (Sp R)) (pj : XQ.A.left ⟶ X₀.A.left) (g : X₀.A.left ⟶ G₀.left) (cm : OAct O X₀.A),
          XQ.IsPullBy X₀ (spMap j) pj ∧ IsGrpPullback X₀.A G₀ (spMap ic) g ∧ pj ≫ g = gQ ∧
          (∀ a, cm.act (ofO a) = X₀.rm.act a) ∧ ∀ a, (cmQ.act a).left ≫ pj = pj ≫ (cm.act a).left := by
  first | exact @GlobalTheory.PlaceModel.exists_obj_eventually | exact GlobalTheory.PlaceModel.exists_obj_eventually | (intros; apply GlobalTheory.PlaceModel.exists_obj_eventually <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TangentBaseChange

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_tangent_baseChange : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  intro R₀ R ic hic G₀ _ G _ A _ g p hg hp v₀ v' hv₀ hv'
  have hw : (spMap (Chart.dualMapR ic) ≫ v₀.left) ≫ G₀.hom =
      spMap (algebraMap R (DualNumber R)) ≫ spMap ic := by
    rw [Category.assoc, Over.w v₀]
    show spMap (Chart.dualMapR ic) ≫ spMap (algebraMap R₀ (DualNumber R₀)) = _
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext x
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let vl : (epsR R).left ⟶ G.left := hg.1.lift _ _ hw
  have hvg : vl ≫ g = spMap (Chart.dualMapR ic) ≫ v₀.left := hg.1.lift_fst _ _ hw
  have hvG : vl ≫ G.hom = spMap (algebraMap R (DualNumber R)) := hg.1.lift_snd _ _ hw
  refine ⟨Over.homMk vl hvG, ?_, ?_⟩
  · show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vl = η[G].left
    apply hg.1.hom_ext
    · have e : η[G].left ≫ g = spMap ic ≫ η[G₀].left := GlobalTheory.PolBaseChange.eSec_comm hg
      have t : spMap (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom ≫ v₀.left = η[G₀].left := hv₀
      have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (Chart.dualMapR ic) =
          ic.comp (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom := by
        refine RingHom.ext fun x => ?_
        simp [Chart.dualMapR]
      rw [Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr, ← spMap_comp_ring,
        Category.assoc, t, e]
    · have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) =
          RingHom.id R := by
        refine RingHom.ext fun x => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [Category.assoc, hvG, spMap_comp_ring, hr, Over.w η[G]]
      simp
  · apply hg.1.hom_ext
    · have hr : (Chart.dualMapR R.subtype).comp (Chart.dualMapR ic) = Chart.dualMapR R₀.subtype := by
        refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
        · simp [Chart.dualMapR, hic]
        · simp [Chart.dualMapR, hic]
      show (v'.left ≫ p) ≫ g = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ g
      rw [Category.assoc, hv', Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr]
    · show (v'.left ≫ p) ≫ G.hom = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ G.hom
      rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w v', Category.assoc, hvG]
      show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap R.subtype =
        spMap (Chart.dualMapR R.subtype) ≫ spMap (algebraMap R (DualNumber R))
      rw [spMap_comp_ring, spMap_comp_ring]
      congr 1
      ext x
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.TangentBaseChange
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_chain_compat : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  atlas_forward_decl GlobalTheory.TangentBaseChange.exists_tangent_baseChange
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_obj_of_isogenous_model : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ →
    (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left →
      Flat Ψ₀.left → Surjective Ψ₀.left →
      Eventually l lam fun R ↦ ∃ (X₀ : Obj (FR E) 𝔠 (Sp R)) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
        X.IsPullBy X₀ (spMap R.subtype) p ∧
        (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
        (∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
          (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ p = p ≫ (cm.act a).left) ∧
        ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie), IsTangent v₀ →
          v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left → ∃ v : X₀.Lie, Obj.LieCorr R.subtype p v v' := by
  intro HD HR E _ _ _ I _ φ hφ c y hc l _ lam 𝔠 X U hα k₀ R₀ hk₀ hR₀ hR₀k G₀ _ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ hfin hfl hsurj
  let σ : R₀ →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR₀.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨XQ, pQ, gQ, cmQ, hQ, hgQ, epQ, hrmQ, hαQ⟩ :=
    GlobalTheory.T.cm_uniformization_algebraic_model HD E I φ c (lattice c y) 𝔠 X U hα R₀ σ (fun _ ↦ rfl) G₀ p₀ hG₀ hp₀
  obtain ⟨k, hk, H⟩ := GlobalTheory.T.cm_endomorphism_place_integral HD HR (FR E) 𝔠 (orderC c) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c) l lam k₀ R₀ (GlobalTheory.T.conductor_order_finite_integers E c) hk₀ hR₀
    hR₀k σ (fun _ ↦ rfl) G₀ P₀ Ψ₀ hG₀ hΨ hfin hfl hsurj XQ gQ cmQ hgQ hrmQ
  refine ⟨k ⊔ k₀, inferInstance, fun R hR ↦ ?_⟩
  have hle : R₀ ≤ R := fun x hx ↦ (hR.mono le_sup_right).2.2 x (hR₀k x hx) (hR₀.2.1 x hx)
  let j : R →+* Qb :=
    { toFun := fun x ↦ ⟨x, (hR.2.1 x x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  obtain ⟨X₀, pj, g, cm, hj, hg, epj, hrm, hcm⟩ :=
    H R (hR.mono le_sup_left) (Subring.inclusion hle) j (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hspec : spMap (algebraMap Qb ℂ) ≫ spMap j = spMap R.subtype := by
    rw [GlobalTheory.HomDescent.spMap_comp]; rfl
  have hX : X.IsPullBy X₀ (spMap R.subtype) (pQ ≫ pj) := hspec ▸ Obj.IsPullBy.trans hQ hj
  refine ⟨X₀, pQ ≫ pj, cm, hX, hrm, fun a α hα' hu ↦ ?_, fun v₀ v' hv₀ hv' ↦ ?_⟩
  · rw [← Category.assoc, hαQ a α hα' hu, Category.assoc, hcm, Category.assoc]
  · obtain ⟨v, hv, ev⟩ := GlobalTheory.T.tangent_pullback_chain_compat R₀ R (Subring.inclusion hle) (fun _ ↦ rfl) G₀ X₀.A X.A g (pQ ≫ pj) hg hX.grp v₀ v'.hom
      hv₀ (by rw [Category.assoc, epj, epQ]; exact hv')
    exact ⟨Serre.Lie.mk _ v hv, ev⟩

end GlobalTheory.LatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_l_adic_endomorphism_integral : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ →
    (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left →
      Flat Ψ₀.left → Surjective Ψ₀.left →
      Eventually l lam fun R ↦ ∃ (X₀ : Obj (FR E) 𝔠 (Sp R)) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
        X.IsPullBy X₀ (spMap R.subtype) p ∧
        (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
        (∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
          (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ p = p ≫ (cm.act a).left) ∧
        ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie), IsTangent v₀ →
          v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left → ∃ v : X₀.Lie, Obj.LieCorr R.subtype p v v' := by
  atlas_forward_decl GlobalTheory.LatModel.exists_obj_of_isogenous_model
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_model_periods : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
      (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A),
      X.IsPullBy X₀ (spMap R.subtype) p ∧
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) ∧
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
      ∀ (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ), IsPeriodGen X₀ U p i e a → a ≠ 0 → Sz l lam (a0 𝔣 l) (a / Ω) := by
  intro hPer hST hDR hDC hPol E _ _ _ _ I _ d φ hF 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    refine mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact h𝔣.1) (Finset.prod_ne_zero_iff.2 fun q _ ↦ ?_)
    rw [Ideal.zero_eq_bot]; exact q.ne_bot
  obtain ⟨𝔠, X, U, hend⟩ := GlobalTheory.T.cm_order_uniformization_exists E I d φ hF (condQ 𝔣 Q) y hc
  obtain ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, _, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ₀, hΨf, hΨfl, hΨs, htan⟩ :=
    GlobalTheory.T.integral_lattice_l_adic_congruence hST hDC E I d φ hF 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ 𝔠 X U
  obtain ⟨k, hk, H⟩ := (GlobalTheory.T.cm_order_l_adic_endomorphism_integral hDC hDR E I φ hF.2.2.2.2.2.2.1 (condQ 𝔣 Q) y hc l lam 𝔠 X U hend k₀ R₀ hk₀ hR₀ hR₀k
    G₀ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ₀ hΨf hΨfl hΨs).and (GlobalTheory.T.eventually_place_ring E l lam)
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_place_ring_over_prime l lam k hk
  obtain ⟨⟨X₀, p, cm, hpb, hrm, hcm, hlie⟩, hplace⟩ := H R hR
  refine ⟨𝔠, R, hplace, X₀, X, U, p, cm, hpb, hrm, fun a ↦ ?_, fun i e a he _ ↦ ?_⟩
  · obtain ⟨α, hα, hα'⟩ := hend a
    exact ⟨α, hα, hcm a α hα hα', hα'⟩
  · obtain ⟨v₀, v', W, htv, hvv, hW, hW0, hsz⟩ := htan i
    obtain ⟨v, hv⟩ := hlie v₀ v' htv hvv
    exact sz_period_of_tangent hplace he hv hW hW0 hsz

end GlobalTheory.LatModel
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_field_lattice_integrality : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
      (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A),
      X.IsPullBy X₀ (spMap R.subtype) p ∧
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) ∧
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
      ∀ (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ), IsPeriodGen X₀ U p i e a → a ≠ 0 → Sz l lam (a0 𝔣 l) (a / Ω) := by
  atlas_forward_decl GlobalTheory.LatModel.exists_model_periods
end

section
section
namespace GlobalTheory

theorem exists_diagonal_operator_killing (R : Subring ℂ) {g : ℕ} {V : Type} [AddCommGroup V]
    [Module R V] (ψ : V →ₗ[R] (Fin g → ℂ)) {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) (s : Finset (Fin g))
    (hi : i ∉ s) :
    ∃ (P : V →ₗ[R] V) (C : Fin g → ℂ), C i ≠ 0 ∧ (∀ k ∈ s, C k = 0) ∧
      ∀ v k, ψ (P v) k = C k * ψ v k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, fun _ => 1, one_ne_zero, by simp, by simp⟩
  | insert j s hj ih =>
    rw [Finset.mem_insert, not_or] at hi
    obtain ⟨P, C, hC, hCs, hP⟩ := ih hi.2
    obtain ⟨a, ha⟩ := hsep i j hi.1
    obtain ⟨x, hx, y, hy, hy0, hxy⟩ := hK a j
    refine ⟨((⟨y, hy⟩ : R) • T a - (⟨x, hx⟩ : R) • LinearMap.id) ∘ₗ P,
      fun k => y * (lam a k - lam a j) * C k, ?_, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero hy0 (sub_ne_zero.mpr ha)) hC
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp
      · simp [hCs k hk]
    · intro v k
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub,
        map_smul, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, hT, hP, Subring.smul_def,
        smul_eq_mul]
      rw [← hxy]; ring

theorem exists_generator_eigenform (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type}
    [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ))
    (hli : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  classical
  obtain ⟨P, C, hC, hCs, hP⟩ :=
    exists_diagonal_operator_killing R ψ T lam hT hsep hK i (Finset.univ.erase i) (by simp)

  obtain ⟨w, hw⟩ : ∃ w, ψ w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hspan : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    have hle : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) ≤
        LinearMap.ker (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simpa using hcon (b k)
    rw [hspan] at hle
    have := hle (Submodule.mem_top (x := fun _ => (1 : ℂ)))
    simp at this
  have hexp : ∀ v, ψ v = ∑ k, ((b.repr v k : R) : ℂ) • ψ (b k) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Subring.smul_def]
  have hprop : ∀ v, ψ (P v) = (ψ v i / ψ w i) • ψ (P w) := by
    intro v
    funext k
    simp only [Pi.smul_apply, hP, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; field_simp
    · rw [hCs k (by simp [hk])]; simp
  have hcoord : ∀ v k, ((b.repr (P v) k : R) : ℂ) = (ψ v i / ψ w i) * ((b.repr (P w) k : R) : ℂ) := by
    intro v k
    have h := hprop v
    rw [hexp (P v), hexp (P w), Finset.smul_sum] at h
    simp only [smul_smul] at h
    exact (Fintype.linearIndependent_iffₛ.mp hli _ _ h) k
  obtain ⟨k₀, hk₀⟩ : ∃ k, ((b.repr (P w) k : R) : ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := congrFun (hexp (P w)) i
    simp only [hcon, zero_smul, Finset.sum_const_zero, hP, Pi.zero_apply] at h
    exact mul_ne_zero hC hw h
  set e₀ : V →ₗ[R] R := b.coord k₀ ∘ₗ P with he₀
  set c₀ : ℂ := ((b.repr (P w) k₀ : R) : ℂ) / ψ w i with hc₀
  have hc₀0 : c₀ ≠ 0 := div_ne_zero hk₀ hw
  have he₀v : ∀ v, ((e₀ v : R) : ℂ) = c₀ * ψ v i := by
    intro v
    have := hcoord v k₀
    simp only [he₀, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [this, hc₀]; ring
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range e₀ : Ideal R)).principal
  have hdmem : d ∈ LinearMap.range e₀ := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨v₁, hv₁⟩ := hdmem
  have hq : ∀ v, ∃ q : R, q • d = e₀ v := by
    intro v
    have : e₀ v ∈ LinearMap.range e₀ := ⟨v, rfl⟩
    rw [hd] at this
    exact Submodule.mem_span_singleton.mp this
  choose q hq using hq
  have hd0 : (d : ℂ) ≠ 0 := by
    intro h0
    have h1 := he₀v w
    rw [← hq w, smul_eq_mul, Subring.coe_mul, h0, mul_zero] at h1
    exact mul_ne_zero hc₀0 hw h1.symm
  set e : V →ₗ[R] R := b.constr R fun k => q (b k) with he
  have hde : d • e = e₀ := by
    refine b.ext fun k => ?_
    rw [LinearMap.smul_apply, he, Module.Basis.constr_basis, ← hq (b k), smul_eq_mul, smul_eq_mul,
      mul_comm]
  have hev : ∀ v, ((e v : R) : ℂ) = c₀ / d * ψ v i := by
    intro v
    have h1 := he₀v v
    rw [← hde, LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul] at h1
    field_simp
    linear_combination h1
  have hv₁' : c₀ * ψ v₁ i = d := by rw [← he₀v, hv₁]
  refine ⟨e, c₀ / d, div_ne_zero hc₀0 hd0, hev, fun e' c' he' => ⟨e' v₁, ?_⟩⟩
  ext v
  rw [LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul, he', he', hev]
  field_simp
  linear_combination (-(c' * ψ v i)) * hv₁'

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simultaneous_eigenbasis_integral : ∀ (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)), (LinearIndependent ℂ fun k ↦ ψ (b k)) →
    ∀ {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ), (∀ a v j, ψ (T a v) j = lam a j * ψ v j) →
    (∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k) → (∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) → ∀ i : Fin g,
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  atlas_forward_decl GlobalTheory.exists_generator_eigenform
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.EigenForm

theorem exists_eigenForm (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)) (hψ : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ) (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e :=
  GlobalTheory.T.simultaneous_eigenbasis_integral R b ψ hψ T lam hT hsep hK i

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem exists_diffEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) {L : LB X.A.left}
    (u : HolUnif X.A L (Module.finrank ℚ F)) :
    ∃ D : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = D v := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  choose Df hDf using fun v : X.Lie ↦ (h1 v.hom v.isTangent).exists
  have huq : ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = Df v := fun v W ↦
    ⟨fun h ↦ (h1 v.hom v.isTangent).unique h (hDf v), fun h ↦ h ▸ hDf v⟩
  let Dl : X.Lie →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := Df
      map_add' := fun v w ↦ by
        refine ((huq (v + w) _).1 ?_).symm
        rw [Serre.Lie.hom_add]
        exact GlobalTheory.UnifLieBasis.isDiff_add u ((isTan_iff _).2 v.isTangent) ((isTan_iff _).2 w.isTangent) (hDf v) (hDf w)
      map_smul' := fun c v ↦ by
        have hs : u.IsDiff (c • Df v) (c • v).hom := by
          have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 v.isTangent) (hDf v) c
          convert this using 1
          rfl
        rw [RingHom.id_apply]
        exact ((huq (c • v) _).1 hs).symm }
  have hinj : Function.Injective Dl := by
    intro v w hvw
    have e0 : Dl v = Df v := rfl
    have e1 : u.IsDiff (Df v) w.hom := (huq w (Df v)).2 (hvw.symm.trans rfl).symm
    have e2 : v.hom = w.hom := (h2 (Df v)).unique (y₁ := v.hom) (y₂ := w.hom) ⟨v.isTangent, hDf v⟩ ⟨w.isTangent, e1⟩
    exact Serre.Lie.ext e2
  have hsurj : Function.Surjective Dl := by
    intro W
    obtain ⟨v₀, ⟨ht, hd⟩, -⟩ := h2 W
    refine ⟨Serre.Lie.mk X.rm v₀ ht, ?_⟩
    have hd' : u.IsDiff W (Serre.Lie.mk X.rm v₀ ht).hom := hd
    exact ((huq _ W).1 hd').symm
  exact ⟨LinearEquiv.ofBijective Dl ⟨hinj, hsurj⟩, fun v W ↦ huq v W⟩

theorem isDiff_act {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)} (U : Unif φ L z X) (a : 𝓞 (FR E)) (v : X.Lie)
    (W : Fin (Module.finrank ℚ (FR E)) → ℂ) (h : U.u.IsDiff W v.hom) :
    U.u.IsDiff (fun j ↦ φ (U.e j) ((a : FR E) : E) * W j) (a • v).hom := by
  haveI := X.rm.hom a
  let Fm : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) ((a : FR E) : E) • ContinuousLinearMap.proj j
  have hF : ∀ w, Fm w = fun j ↦ φ (U.e j) ((a : FR E) : E) * w j := fun w ↦ by
    ext j; simp [Fm]
  have := GlobalTheory.UnifLieBasis.isDiff_comp U.u (X.rm.act a) Fm (fun w ↦ by rw [hF]; exact U.act a w) v.isTangent h
  rw [hF] at this
  exact this

theorem lieCorr_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} (σ : R →+* R') {b : Sp R' ⟶ Sp R} {p : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X b p) (a : 𝓞 F) {v : X.Lie} {v' : X'.Lie} (h : Obj.LieCorr σ p v v') :
    Obj.LieCorr σ p (a • v) (a • v') := by
  unfold Obj.LieCorr at h ⊢
  change (v'.hom ≫ X'.rm.act a).left ≫ p = _ ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, hp.act a, ← Category.assoc, h, Category.assoc]

end GlobalTheory.LatModel.EigenForm

namespace GlobalTheory.LatModel.EigenForm

theorem exists_periodGen : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  intro _ E _ _ _ I _ φ hφ l _ lam 𝔠 R hR X₀ X L U p hp i
  classical
  obtain ⟨hdvr, -, -, hKR⟩ := hR
  haveI := hdvr
  obtain ⟨eq, hcorr⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := ℂ) (X := X₀) (X' := X) (φ := p) hp
  obtain ⟨D, hD⟩ := exists_diffEquiv X U.u
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X₀
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R X₀.Lie := Module.free_of_flat_of_isLocalRing
  have hdim : Module.finrank R X₀.Lie = Module.finrank ℚ (FR E) := by
    have := hrk (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let b : Module.Basis (Fin (Module.finrank ℚ (FR E))) R X₀.Lie :=
    (Module.finBasis R X₀.Lie).reindex (finCongr hdim)
  let ψ : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v ↦ D (eq (1 ⊗ₜ v))
      map_add' := fun v w ↦ by simp [TensorProduct.tmul_add]
      map_smul' := fun r v ↦ by
        have e1 : (1 : ℂ) ⊗ₜ[R] (r • v) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[R] v) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
          rfl
        simp only [e1, map_smul, RingHom.id_apply]
        rfl }
  have hψ : ∀ v, ψ v = D (eq (1 ⊗ₜ v)) := fun v ↦ rfl
  let T : 𝓞 (FR E) → X₀.Lie →ₗ[R] X₀.Lie := fun a ↦
    { toFun := fun v ↦ a • v
      map_add' := smul_add a
      map_smul' := fun r v ↦ smul_comm a r v }
  let lamv : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (U.e j) ((a : FR E) : E)
  have hT : ∀ a v j, ψ (T a v) j = lamv a j * ψ v j := by
    intro a v j
    have c0 : Obj.LieCorr R.subtype p v (eq (1 ⊗ₜ v)) := (hcorr v _).2 rfl
    have c1 := lieCorr_act R.subtype hp a c0
    have e1 : a • eq (1 ⊗ₜ v) = eq (1 ⊗ₜ (a • v)) := (hcorr _ _).1 c1
    have d0 : U.u.IsDiff (D (eq (1 ⊗ₜ v))) (eq (1 ⊗ₜ v)).hom := (hD _ _).2 rfl
    have d1 := isDiff_act U a _ _ d0
    have e2 := (hD _ _).1 d1
    change D (eq (1 ⊗ₜ (a • v))) j = _
    rw [← e1, ← e2]
    rfl
  have hsep : ∀ j k, j ≠ k → ∃ a, lamv a j ≠ lamv a k := by
    intro j k hjk
    by_contra hc
    push_neg at hc
    exact hjk (U.e.injective (GlobalTheory.SignGen.cm_restrict_inj E I φ hφ (U.e j) (U.e k) fun a ↦ hc a))
  have hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lamv a j * y = x := fun a j ↦ hKR (φ (U.e j)) _
  have hli : LinearIndependent ℂ fun k ↦ ψ (b k) := by
    convert ((b.baseChange ℂ).map (eq.trans D)).linearIndependent using 1
    ext k : 1
    simp [hψ, Module.Basis.baseChange_apply]
  obtain ⟨e, c, hc, he, huniq⟩ := exists_eigenForm R b ψ hli T lamv hT hsep hK (U.e.symm i)
  refine ⟨e, c, hc, ?_, ?_⟩
  · intro v v' W hvv hW
    rw [(hcorr v v').1 hvv] at hW
    rw [(hD _ W).1 hW, he v]
    rfl
  · intro e' c' h'
    exact huniq e' c' fun v ↦ h' v (eq (1 ⊗ₜ v)) (ψ v) ((hcorr _ _).2 rfl) ((hD _ _).2 rfl)

end GlobalTheory.LatModel.EigenForm
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_ring_model_pullback : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  atlas_forward_decl GlobalTheory.LatModel.EigenForm.exists_periodGen
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LatModel

theorem hasLatModel : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω := by
  intro h1 h2 h3 h4 h5 E _ _ _ _ I _ d φ hfd 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ
  obtain ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hα, hb⟩ :=
    GlobalTheory.T.cm_field_lattice_integrality h1 h2 h3 h4 h5 E I d φ hfd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ
  have hcm : IsCMType φ := hfd.2.2.2.2.2.2.1
  refine ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hα, fun i ↦ ?_⟩
  obtain ⟨e, a, ha, hg, hgen⟩ := GlobalTheory.T.place_ring_model_pullback h3 E I φ hcm l lam 𝔠 R hR X₀ X _ U p hp i
  exact ⟨e, a, ha, hb i e a hg ha, hg, hgen⟩

end GlobalTheory.LatModel
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_field_lattice_base_condition : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω := by
  atlas_forward_decl GlobalTheory.LatModel.hasLatModel
end
