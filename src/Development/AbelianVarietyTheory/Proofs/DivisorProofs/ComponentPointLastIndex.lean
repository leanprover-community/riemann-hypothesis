import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationCaseFiniteComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHost
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.W0EqOfRtEq
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddRightComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingSmulRightConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImages
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LawsCore

theorem laws_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → FnAlgClosed (T.Q.Xo j) T.Q.c →
    Laws (T.U j) (xiR D) := by
  intro D T hT j hj hF
  have hg : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  exact (GlobalTheory.LevLaws.laws_of_level D j _ _ _ (T.Q.Xo j) T.Q.c (T.U j) _
    (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1 hF hg).1

end GlobalTheory.LawsCore
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  atlas_forward_decl GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem exists_isGram_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, h⟩ := GlobalTheory.FlatCM.GramExists.exists_isGram E H K ρ σ₁ p 0 X
  exact ⟨gP, gQ, h, (GlobalTheory.GramAt.gram_det X h).1⟩

end GlobalTheory.FlatCM.HomLat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.exists_isGram_det_ne_zero
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

theorem lat_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, hG, hdet⟩ := GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite E H hH K ρ σ₁ p X
  set N : 𝓞 E := H.bar.symm gP.det with hNdef
  have hN0 : N ≠ 0 := fun h => hdet (by simpa [hNdef] using congrArg H.bar h)
  have hN : (N : E) ≠ 0 := by exact_mod_cast hN0
  have key : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ b, ∃ z : 𝓞 E, (z : E) = (N : E) * c b := by
    rintro c ⟨n, hn, x, hx, f, hf, hfx⟩ b
    choose y hy using GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow E H hH K ρ σ₁ p 0 X gP gQ hG n x f hn hf hfx
    have hmv : gP.mulVec (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * y a := by
      funext a; simp [Matrix.mulVec, dotProduct, hy]
    have hadj : gP.det • (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * gP.adjugate.mulVec y a := by
      have := congrArg gP.adjugate.mulVec hmv
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [this]; funext a; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    have hb := congrArg H.bar.symm (congrFun hadj b)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, map_natCast] at hb
    refine ⟨H.bar.symm (gP.adjugate.mulVec y b), ?_⟩
    have hnE : ((n : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hnE
    have h2 : ((N : 𝓞 E) : E) * ((x b : 𝓞 E) : E) =
        (n : E) * ((H.bar.symm (gP.adjugate.mulVec y b) : 𝓞 E) : E) := by
      rw [hNdef]; exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hb
    push_cast
    rw [← h2, hx b]; ring
  let incl : (Fin p → 𝓞 E) →ₗ[𝓞 E] (Fin p → E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)
  let scal : (Fin p → E) →ₗ[𝓞 E] (Fin p → E) := N • LinearMap.id
  have hscal : Function.Injective scal := by
    intro v w h
    funext i
    have := congrFun h i
    simp only [scal, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hN this
  apply Submodule.fg_of_fg_map_injective scal hscal
  refine Submodule.FG.of_le (T := LinearMap.range incl) ?_ ?_
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map incl
  · rw [GlobalTheory.FlatCM.HomLat.lat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    choose z hz using key c hc
    refine ⟨z, ?_⟩
    funext b
    simp [incl, scal, hz, Algebra.smul_def]

end GlobalTheory.FlatCM.HomLat

end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLinearHomCoordinateLattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.lat_fg
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.WeilAddLeft

theorem pow_comp_hom {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul (Units.map _) u v

theorem weilEq_mul_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm
  haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm
  have tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1) := fun f hf => by
    rw [← pow_comp_hom, hx, one_comp]
  have tory : (y ≫ g) ^ n = 1 := by rw [← pow_comp_hom, hy, one_comp]
  obtain ⟨c₁, hc₁⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory
  obtain ⟨c₂, hc₂⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory
  have a₁ := (h₁ n x y c₁ hn hx hy).1 hc₁
  have a₂ := (h₂ n x y c₂ hn hx hy).1 hc₂
  have hB := weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂
  have hA := weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂
  rw [← MonObj.comp_mul] at hB hA
  rw [← A.t.act.add] at hA
  rw [← unitOn_mul] at hB hA
  constructor
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory.CM.WeilAddLeft
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_add_first_position_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  atlas_forward_decl GlobalTheory.CM.WeilAddLeft.weilEq_mul_left
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.GramInt

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

theorem weilEq_act_left {A B : PAT H (Sp (𝓞 K))} {f g : A.t.G ⟶ B.t.G} {r : 𝓞 E} {k : Type} [Field k]
    {t : Sp k ⟶ Sp (𝓞 K)} (s : 𝓞 E) (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) t) :
    WeilEq B.t.PP.L (A.t.act.act s ≫ f) g A.t.PP.L (A.t.act.act (s * r)) (𝟙 _) t := by
  intro n x y c hn hx hy
  haveI := A.t.act.hom s
  have hx' : (x ≫ A.t.act.act s) ^ n = 1 := by rw [← pow_comp, hx]; simp
  have := h n (x ≫ A.t.act.act s) y c hn hx' hy
  simpa only [Category.assoc, A.t.act.mul] using this
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem isLinearHom_finprod {I₀ : Type} (S : Finset I₀) (F : I₀ → (A.t.G ⟶ B.t.G))
    (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i)) :
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ S, F i) :=
  Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
    (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hF i

theorem weilEq_prod_right {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf.isMonHom (hG a).isMonHom
      (isLinearHom_finprod s G hG).isMonHom _ _ (h a) ih

theorem weilEq_prod_prod {I₀ J₀ : Type} (F : I₀ → (A.t.G ⟶ B.t.G)) (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i))
    (G : J₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ j, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G j)) (r : I₀ → J₀ → 𝓞 E)
    (h : ∀ i j, WeilEq B.t.PP.L (F i) (G j) A.t.PP.L (A.t.act.act (r i j)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {S : Finset I₀} (hS : S.Nonempty) {T : Finset J₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L (∏ i ∈ S, F i) (∏ j ∈ T, G j) A.t.PP.L (A.t.act.act (∑ i ∈ S, ∑ j ∈ T, r i j)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simpa using weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_first_position_complex E H K σ₁ A B (F a) _ _ (hF a).isMonHom (isLinearHom_finprod s F hF).isMonHom
      (isLinearHom_finprod T G hG).isMonHom _ _ (weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT) ih

theorem weilEq_pow_pow (f g : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (hg : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act g) (r : 𝓞 E)
    (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    WeilEq B.t.PP.L (f ^ n) (g ^ m) A.t.PP.L (A.t.act.act ((n * m : ℕ) * r)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have e1 : f ^ n = ∏ _i ∈ Finset.range n, f := by simp
  have e2 : g ^ m = ∏ _j ∈ Finset.range m, g := by simp
  have e3 : ((n * m : ℕ) : 𝓞 E) * r = ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range m, r := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [e1, e2, e3]
  exact weilEq_prod_prod (fun _ => f) (fun _ => hf) (fun _ => g) (fun _ => hg) (fun _ _ => r) (fun _ _ => h)
    (Finset.nonempty_range_iff.2 hn.ne') (Finset.nonempty_range_iff.2 hm.ne')
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p : ℕ}

theorem weilEq_combo (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (hp : 0 < p) (x y : Fin p → 𝓞 E) :
    WeilEq X.B.t.PP.L (∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a))
      (∏ b, ((X.A true).t.act.act (y b) ≫ GlobalTheory.FlatCM.phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hp⟩⟩
  have hlin : ∀ (z : Fin p → 𝓞 E) a, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act
      ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) := fun z a =>
    (GlobalTheory.Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))
  refine weilEq_prod_prod _ (hlin x) _ (hlin y) _ (fun a b => ?_) hne hne
  have h1 := weilEq_act_left (x a) (hG.1 a b)
  exact GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hlin x a).isMonHom (X.lin (Sum.inl b)).isMonHom _ (y b) h1

theorem integral_of_coords (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (barE : E →+* E)
    (hbar : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) {c d : Fin p → E}
    (hc : c ∈ GlobalTheory.FlatCM.HomLat.coords X) (hd : d ∈ GlobalTheory.FlatCM.HomLat.coords X) :
    ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn, x, hx, f, hf, hfx⟩ := hc
  obtain ⟨m, hm, y, hy, g, hg, hgy⟩ := hd
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    f g hf hg
  have h1 := weilEq_pow_pow f g hf hg r hr hn hm
  rw [hfx, hgy] at h1
  have h2 := weilEq_combo X gP gQ hG hp x y
  have h3 : WeilEq (X.A true).t.PP.L ((X.A true).t.act.act ((n * m : ℕ) * r)) (𝟙 _) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)
  have h4 := GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ h3
  refine ⟨r, ?_⟩
  have h5 := congrArg (fun z : 𝓞 E => (z : E)) h4
  simp only [map_mul, map_natCast, map_sum] at h5
  have hnm : ((n * m : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne'
  apply mul_left_cancel₀ hnm
  rw [h5]
  simp only [hx, hy, ← hbar, map_mul, map_natCast, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end

theorem gram_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG barE hbar c hc d hd

  have step : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
      ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
    intro c hc d hd
    induction hd using Submodule.span_induction with
    | mem d hd => exact integral_of_coords X gP gQ hG barE hbar hc hd
    | zero => exact ⟨0, by simp⟩
    | add d d' _ _ h h' =>
      obtain ⟨y, hy⟩ := h
      obtain ⟨y', hy'⟩ := h'
      refine ⟨y + y', ?_⟩
      simp only [map_add, hy, hy', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul s d _ h =>
      obtain ⟨y, hy⟩ := h
      refine ⟨H.bar s * y, ?_⟩
      simp only [map_mul, ← hbar, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  induction hc using Submodule.span_induction with
  | mem c hc => exact step c hc d hd
  | zero => exact ⟨0, by simp⟩
  | add c c' _ _ h h' =>
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', hy'⟩ := h'
    refine ⟨y + y', ?_⟩
    simp only [map_add, hy, hy', Pi.add_apply, add_mul, Finset.sum_add_distrib]
  | smul s c _ h =>
    obtain ⟨y, hy⟩ := h
    refine ⟨s * y, ?_⟩
    simp only [map_mul, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.FlatCM.GramInt
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHomGramForm_integral_coordinateLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  atlas_forward_decl GlobalTheory.FlatCM.GramInt.gram_integral
end

section
section
open NumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM GlobalTheory.CM.IntCoord

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat

theorem sum_smul_diff_mem_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he
  obtain ⟨n, hn, x, hx, f, hf, hfn⟩ := hc
  have hcA := integral_tangent_coordinates K _ FP
  have hcB := integral_tangent_coordinates K _ FB
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have := hf.isMonHom
  have ht : IsTangent (u ≫ f) := by
    have hv := hu.1
    unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨d, hd, -⟩ := hcB.1 _ ht
  have hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FP hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have heq : n • d = ∑ a, MP a (τ (x a) • e) := by
    have h1 := hpow n
    rw [← comp_pow, hfn] at h1
    exact (hcB.1 _ h1.1).unique h1 (hprod Finset.univ)
  have hdval : d = ∑ a, τE (c a) • MP a e := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine smul_right_injective _ hn0 ?_
    show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e
    rw [Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]
    congr 1
    show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)
    rw [← hτE, hx a, map_mul, map_natCast]
  rw [← hdval]
  refine (hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s),
    Category.assoc]

end GlobalTheory.FlatCM.HomLat
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_smul_differential_mem_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.sum_smul_diff_mem_eigLat
end

section
section
set_option autoImplicit false

open NumberField

namespace GlobalTheory.FlatCM.HomLat

theorem exists_selfDual_lieSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG
  refine ⟨GlobalTheory.FlatCM.HomLat.lat X, GlobalTheory.T.cmLinearHomCoordinateLattice_fg E H hH K ρ σ₁ p X, GlobalTheory.FlatCM.HomLat.intl_mem X,
    fun barE hbar d => ⟨fun hd c hc => GlobalTheory.T.cmHomGramForm_integral_coordinateLattice E H hH K ρ σ₁ p X gP gQ hG barE hbar c hc d hd,
      GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing E H hH K ρ σ₁ p X gP gQ hG barE hbar d⟩, ?_⟩
  intro FP FB MP hMP τ hτ τE hτE
  refine le_antisymm (GlobalTheory.T.lieEigenLattice_le_span_cmHom_images E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE) ?_
  refine Submodule.span_le.2 ?_
  rintro w ⟨c, hc, e, he, rfl⟩
  induction hc using Submodule.span_induction generalizing e with
  | mem c hc => exact GlobalTheory.T.sum_smul_differential_mem_eigenLattice E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE c hc e he
  | zero => simp
  | add c d _ _ hc hd =>
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact add_mem (hc e he) (hd e he)
  | smul s c _ hc =>
    have h1 : ∑ a, τE ((s • c) a) • MP a e = ∑ a, τE (c a) • MP a ((τ s : K) • e) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : τE ((s • c) a) = (τ s : K) * τE (c a) := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        exact congrArg (· * τE (c a)) (hτE s)
      rw [h2, mul_smul, (MP a).map_smul, smul_comm]
    rw [h1]
    exact hc _ (by simpa [algebraMap_smul] using (FP.eigLat (X.A true).t.act τ).smul_mem (τ s) he)

end GlobalTheory.FlatCM.HomLat
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  atlas_forward_decl GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.SelfDualIndex

variable {E : Type} [Field E] [NumberField E] {p : ℕ}

theorem bdd_of_fg {Λ : Submodule (𝓞 E) (Fin p → E)} (h : Λ.FG) : GlobalTheory.BetaEx.Bdd Λ := by
  classical
  obtain ⟨s, rfl⟩ := h
  choose a ha0 ha using fun v : Fin p → E => GlobalTheory.BetaEx.exists_smul_std v
  refine ⟨∏ v ∈ s, a v, Finset.prod_ne_zero_iff.2 fun v _ => ha0 v, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s a hx, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha x)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

omit [NumberField E] in

theorem ιMulti_single_ne_zero :
    exteriorPower.ιMulti E p (fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) ≠ 0 := by
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating : (Fin p → E) [⋀^Fin p]→ₗ[E] E)) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
  change Matrix.det (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 0 at this
  rw [show (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 1 from by
    ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this
  exact one_ne_zero this

omit [NumberField E] in

theorem idx_eq (Λ : Submodule (𝓞 E) (Fin p → E)) (J : Ideal (𝓞 E)) (hJ : J • GlobalTheory.BetaEx.detSpan Λ = 1) :
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) = J := by
  rw [GlobalTheory.FlatCM.idx, GlobalTheory.FlatCM.Model.detSpan_span]
  set ω := exteriorPower.ιMulti E p (fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) with hω
  have hω0 : ω ≠ 0 := ιMulti_single_ne_zero
  have hι : ∀ v : Fin p → Fin p → E, exteriorPower.ιMulti E p v = (Matrix.of v).det • ω := by
    intro v
    rw [hω, ← GlobalTheory.FlatCM.Model.ιMulti_comb]
    congr 1
    funext i
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hspan : ∀ x : E, x • ω ∈ Submodule.span (𝓞 E) {ω} ↔ ∃ b : 𝓞 E, (b : E) = x := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, smul_left_injective E hω0 ?_⟩
      show (b : E) • ω = x • ω
      rw [← hb]
      exact algebraMap_smul E b ω
    · rintro ⟨b, rfl⟩
      exact ⟨b, (algebraMap_smul E b ω).symm⟩
  have hint : ∀ r ∈ J, ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x := fun r hr x hx => by
    have := Submodule.smul_mem_smul hr hx
    rw [hJ] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 this
    exact ⟨b, by rw [← Algebra.smul_def]; exact hb⟩
  ext r
  rw [Submodule.mem_colon]
  constructor
  · intro h
    have h2 : ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet Λ x).1 hx
        let u : Fin p → Fin p → E := fun i j => v i j
        have hm : exteriorPower.ιMulti E p u ∈ GlobalTheory.FlatCM.detSpan E p Λ :=
          Submodule.subset_span ⟨u, hv, rfl⟩
        have := h _ hm
        rw [hι u, ← algebraMap_smul E r, smul_smul] at this
        exact (hspan _).1 this
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by change (a : E) + (b : E) = _; rw [ha, hb]; ring⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c * a, by change (c : E) * (a : E) = (r : E) * ((c : E) * x); rw [ha]; ring⟩
    have h1 : (1 : E) ∈ J • GlobalTheory.BetaEx.detSpan Λ := by rw [hJ]; exact Submodule.one_le.1 le_rfl
    have h3 : ∀ z ∈ J • GlobalTheory.BetaEx.detSpan Λ, (r : E) * z ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro a ha x hx
        obtain ⟨b, hb⟩ := h2 x hx
        refine ⟨a * b, J.mul_mem_right b ha, ?_⟩
        rw [Algebra.linearMap_apply, map_mul, Algebra.smul_def]
        change (a : E) * (b : E) = (r : E) * ((a : E) * x)
        rw [hb]; ring
      · intro x y hx hy
        rw [mul_add]; exact add_mem hx hy
    obtain ⟨b, hb, hbr⟩ := h3 1 h1
    rw [mul_one] at hbr
    have : b = r := RingOfIntegers.ext hbr
    exact this ▸ hb
  · intro hr w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [hι, ← algebraMap_smul E r, smul_smul]
      exact (hspan _).2 (hint r hr _ (GlobalTheory.BetaEx.det_mem (Matrix.of y) hy))
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.SelfDualIndex

namespace GlobalTheory.SelfDualIndex

open scoped Matrix

theorem idx_mul_map_bar_eq : ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E →+* 𝓞 E) (barE : E →+* E),
    (∀ x : 𝓞 E, barE x = ((bar x : 𝓞 E) : E)) → ∀ (p : ℕ) (G : Matrix (Fin p) (Fin p) (𝓞 E))
    (Λ : Submodule (𝓞 E) (Fin p → E)), Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    (∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (G a b : E) * barE (d b)) →
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) *
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map bar =
      Ideal.span {G.det} := by
  intro E _ _ bar barE hbar p G Λ hfg hO hsd
  have hsurj : Function.Surjective barE := (Algebra.IsAlgebraic.algHom_bijective barE.toRatAlgHom).2

  have hstd : Formalism.L2.Pj.stdLat E p ≤ Λ := fun v hv => by
    choose b hb using (GlobalTheory.BetaEx.mem_std v).1 hv
    convert hO b using 1
    funext a
    exact (hb a).symm
  obtain ⟨J, -, hJ, -⟩ := GlobalTheory.BetaEx.exists_index_ideal _ Λ hstd (bdd_of_fg hfg)
    (fun m _ => GlobalTheory.BetaEx.exists_smul_std m)
  rw [GlobalTheory.DetIdeal.detSpan_std] at hJ
  have hJ1 : J • GlobalTheory.BetaEx.detSpan Λ = 1 := hJ.symm
  rw [idx_eq Λ J hJ1]
  set D := GlobalTheory.BetaEx.detSpan Λ with hD
  have hdual := GlobalTheory.DetIdeal.detSpan_bdual Λ J hJ1

  set G' : Matrix (Fin p) (Fin p) E := G.map fun x => (x : E) with hG'
  have hG'det : G'.det = (G.det : E) := (RingHom.map_det (algebraMap (𝓞 E) E) G).symm
  have hpair : ∀ c d : Fin p → E,
      ∑ a, ∑ b, c a * (G a b : E) * barE (d b) = (G' *ᵥ fun b => barE (d b)) ⬝ᵥ c := by
    intro c d
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, hG', Matrix.map_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdetW : ∀ V : Matrix (Fin p) (Fin p) E,
      (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)).det = (G.det : E) * barE V.det := by
    intro V
    have e : (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)) = barE.mapMatrix V * G'ᵀ := by
      ext i a
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [e, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hG'det, mul_comm]
  have hΦ : ∀ v ∈ Λ, (G' *ᵥ fun b => barE (v b)) ∈ GlobalTheory.DetIdeal.bdual Λ := by
    intro v hv c hc
    obtain ⟨y, hy⟩ := (hsd v).1 hv c hc
    rw [← hpair]
    exact Submodule.mem_one.2 ⟨y, hy⟩

  have hG0 : (G.det : E) ≠ 0 := by
    intro h0
    rw [← hG'det] at h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set d : Fin p → E := fun k => Function.surjInv hsurj (w k) with hd
    have hbd : ∀ k, barE (d k) = w k := fun k => Function.surjInv_eq hsurj (w k)
    have hdt : ∀ t : E, t • d ∈ Λ := by
      intro t
      refine (hsd _).2 fun c _ => ⟨0, ?_⟩
      rw [hpair]
      have : (fun b => barE ((t • d) b)) = barE t • w := by
        funext b
        simp [hbd, smul_eq_mul]
      rw [this, Matrix.mulVec_smul, hw, smul_zero, zero_dotProduct]
      simp
    obtain ⟨k, hk0, hk⟩ := bdd_of_fg hfg
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hw0 (funext hne)
    have hdi : d i ≠ 0 := fun h => hi (by rw [← hbd i, h, map_zero])
    have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
    apply RingOfIntegers.not_isField E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {b} hb => ?_⟩
    have hbE : (b : E) ≠ 0 := by exact_mod_cast hb
    obtain ⟨c, hc⟩ := (GlobalTheory.BetaEx.mem_std _).1 (hk _ (hdt ((b : E)⁻¹ / ((k : E) * d i)))) i
    refine ⟨c, RingOfIntegers.ext ?_⟩
    change (b : E) * (c : E) = 1
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    change (b : E) * ((k : E) * ((b : E)⁻¹ / ((k : E) * d i) * d i)) = 1
    field_simp
  have hsm : ∀ (c : 𝓞 E) (x : E), barE (c • x) = (bar c : E) * barE x := by
    intro c x
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact hbar c
  have hone : ∀ j ∈ J, ∀ x ∈ D, ∃ c : 𝓞 E, (c : E) = (j : E) * x := by
    intro j hj x hx
    have := Submodule.smul_mem_smul hj hx
    rw [hJ1] at this
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
    exact ⟨c, by rw [← Algebra.smul_def]; exact hc⟩

  have hB1 : ∀ x ∈ D, ∃ j ∈ J, (j : E) = (G.det : E) * barE x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet Λ x).1 hx
      have hm := GlobalTheory.BetaEx.det_mem (Matrix.of fun i => G' *ᵥ fun b => barE (v i b)) fun i => hΦ (v i) (hv i)
      rw [hdual, hdetW] at hm
      obtain ⟨j, hj, hje⟩ := hm
      exact ⟨j, hj, hje⟩
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hae⟩ := hx
      obtain ⟨b, hb, hbe⟩ := hy
      refine ⟨a + b, J.add_mem ha hb, ?_⟩
      change (a : E) + (b : E) = _
      rw [hae, hbe, map_add]; ring
    | smul c x _ hx =>
      obtain ⟨a, ha, hae⟩ := hx
      refine ⟨bar c * a, J.mul_mem_left _ ha, ?_⟩
      change (bar c : E) * (a : E) = _
      rw [hae, hsm]; ring

  have hB2 : ∀ a ∈ J, ∀ b ∈ J, ∃ c : 𝓞 E, (c : E) * (G.det : E) = (a : E) * barE b := by
    intro a ha b hb
    have haE : (a : E) ∈ GlobalTheory.BetaEx.detSpan (GlobalTheory.DetIdeal.bdual Λ) := by
      rw [hdual]; exact ⟨a, ha, rfl⟩
    generalize (a : E) = e at haE
    induction haE using Submodule.span_induction with
    | mem e he =>
      obtain ⟨W, hW, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet _ e).1 he
      have hGu : IsUnit G'.det := by rw [hG'det]; exact isUnit_iff_ne_zero.2 hG0
      set V : Matrix (Fin p) (Fin p) E := Matrix.of fun i k => Function.surjInv hsurj ((G'⁻¹ *ᵥ W i) k) with hV
      have hVb : ∀ i, (fun k => barE (V i k)) = G'⁻¹ *ᵥ W i := fun i => funext fun k =>
        Function.surjInv_eq hsurj _
      have hWV : W = Matrix.of fun i => G' *ᵥ fun k => barE (V i k) := by
        ext i k
        rw [Matrix.of_apply, hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
      have hVΛ : ∀ i, V i ∈ Λ := by
        intro i
        refine (hsd _).2 fun c hc => ?_
        obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hW i c hc)
        refine ⟨y, ?_⟩
        rw [hpair]
        have : (G' *ᵥ fun k => barE (V i k)) = W i := by
          rw [hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
        rw [this]
        exact hy
      obtain ⟨c0, hc0⟩ := hone b hb V.det (GlobalTheory.BetaEx.det_mem V hVΛ)
      refine ⟨bar c0, ?_⟩
      rw [hWV, hdetW, ← hbar, hc0, map_mul, hbar b]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      refine ⟨c + c', ?_⟩
      change ((c : E) + (c' : E)) * _ = _
      rw [add_mul, hc, hc']; ring
    | smul r x _ hx =>
      obtain ⟨c, hc⟩ := hx
      refine ⟨r * c, ?_⟩
      change ((r : E) * (c : E)) * _ = _
      rw [Algebra.smul_def, mul_assoc, hc]
      change (r : E) * _ = (r : E) * x * _
      ring
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨b, hb, rfl⟩ := hs
      obtain ⟨c, hc⟩ := hB2 a ha b hb
      refine Ideal.mem_span_singleton'.2 ⟨c, RingOfIntegers.ext ?_⟩
      change (c : E) * (G.det : E) = (a : E) * (bar b : E)
      rw [hc, hbar]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
  · rw [Ideal.span_singleton_le_iff_mem]
    have h1 : (1 : E) ∈ J • D := by rw [hJ1]; exact Submodule.one_le.1 le_rfl
    have key : ∀ e ∈ J • D, ∀ e' ∈ J • D, ∃ z ∈ J * J.map bar, (z : E) = (G.det : E) * e * barE e' := by
      intro e he e' he'
      refine Submodule.smul_induction_on he ?_ ?_
      · intro a ha x hx
        refine Submodule.smul_induction_on he' ?_ ?_
        · intro a' ha' x' hx'
          obtain ⟨j, hj, hje⟩ := hB1 x' hx'
          obtain ⟨c, hc⟩ := hone j hj x hx
          refine ⟨a * bar a' * c, Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ ha')), ?_⟩
          change (a : E) * (bar a' : E) * (c : E) = _
          rw [hsm, hc, hje, Algebra.smul_def]
          change _ = (G.det : E) * ((a : E) * x) * _
          ring
        · intro y y' hy hy'
          obtain ⟨z, hz, hze⟩ := hy
          obtain ⟨z', hz', hze'⟩ := hy'
          refine ⟨z + z', add_mem hz hz', ?_⟩
          change (z : E) + (z' : E) = _
          rw [hze, hze', map_add]; ring
      · intro y y' hy hy'
        obtain ⟨z, hz, hze⟩ := hy
        obtain ⟨z', hz', hze'⟩ := hy'
        refine ⟨z + z', add_mem hz hz', ?_⟩
        change (z : E) + (z' : E) = _
        rw [hze, hze']; ring
    obtain ⟨z, hz, hze⟩ := key 1 h1 1 h1
    rw [map_one, mul_one, mul_one] at hze
    have : z = G.det := RingOfIntegers.ext hze
    exact this ▸ hz

end GlobalTheory.SelfDualIndex
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_ideal_mul_conj_eq_gram_det_selfDual : ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E →+* 𝓞 E) (barE : E →+* E),
    (∀ x : 𝓞 E, barE x = ((bar x : 𝓞 E) : E)) → ∀ (p : ℕ) (G : Matrix (Fin p) (Fin p) (𝓞 E))
    (Λ : Submodule (𝓞 E) (Fin p → E)), Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    (∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (G a b : E) * barE (d b)) →
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) *
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map bar =
      Ideal.span {G.det} := by
  atlas_forward_decl GlobalTheory.SelfDualIndex.idx_mul_map_bar_eq
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCM.IdealZero

theorem idealSt_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hg
  obtain ⟨Λ, hfg, hstd, hdual, hdesc⟩ := GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite E H hH K ρ σ₁ p X gP gQ hg
  have hbinj : Function.Injective ((algebraMap (𝓞 E) E).comp (H.bar : 𝓞 E →+* 𝓞 E)) :=
    (RingOfIntegers.coe_injective (K := E)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let barE : E →+* E := IsFractionRing.lift hbinj
  have hbarE : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E) := fun x => IsFractionRing.lift_algebraMap hbinj x
  refine ⟨_, GlobalTheory.T.index_ideal_mul_conj_eq_gram_det_selfDual E _ barE hbarE p gP Λ hfg hstd (hdual barE hbarE), ?_⟩
  intro FP FB MP hMP τ hτ
  have hτinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let τE : E →+* K := IsFractionRing.lift hτinj
  have hτE : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K) := fun x => IsFractionRing.lift_algebraMap hτinj x
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b => match b with
    | true => FP
    | false => (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A false).pol).some
  let M : ∀ k : Fin p ⊕ Fin 0, (Fin (FA k.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun k => match k with
    | .inl a => MP a
    | .inr a => a.elim0
  obtain ⟨-, -, hinj, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA FB M
      (fun k => match k with
        | .inl a => hMP a
        | .inr a => a.elim0)
  have hfgA : (FP.eigLat (X.A true).t.act τ).FG :=
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ FP).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hrk : latRank K (FP.eigLat (X.A true).t.act τ) = 1 := by
    rw [(GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ, if_pos hτ]
  rw [subP, hdesc FP FB MP hMP τ hτ τE hτE]
  exact GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map E K τ τE hτE p _ _ _ MP Λ hfgA hrk (fun a => hinj (.inl a))
    (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ)) fun a b e => by simpa using e)
    hfg hstd

end GlobalTheory.FlatCM.IdealZero

end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  atlas_forward_decl GlobalTheory.FlatCM.IdealZero.idealSt_zero
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff0

theorem idxZero {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L N : Submodule (𝓞 K) V) : idx K 0 L N = ⊤ := by
  have : detSpan K 0 N = detSpan K 0 L := by
    unfold detSpan
    congr 1
    ext w
    simp
  rw [idx, this]
  exact (Ideal.eq_top_iff_one _).2 (Submodule.mem_colon.2 fun _ h => by simpa using h)

theorem cmDiff_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re := by

  intro E _ _ _ H hH _ χ hχ K _ _ ρ σ₁ p q X F h hF hq τ hτ
  subst hq
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A b).pol).some
  have hM : ∀ j : Fin p ⊕ Fin 0, ∃ M, (FA j.isLeft).IsDiffOf F (X.φ j) M := fun j =>
    (DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ F (X.φ j) (X.lin j).1).1.exists
  choose M hM using hM
  obtain ⟨gP, gQ, hg⟩ := GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject E H K ρ σ₁ p 0 X
  have hD : IsDiffs (FA true) (FA false) F (fun a => M (.inl a)) (fun a => M (.inr a)) :=
    ⟨fun a => hM (.inl a), fun a => hM (.inr a)⟩
  obtain ⟨𝔫, h𝔫₀, hid₀⟩ := GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal E H hH K ρ σ₁ p X gP gQ hg
  have hQd : gQ.det = 1 := Matrix.det_fin_zero
  have h𝔫 : 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} := by
    rw [hQd, mul_one]; exact h𝔫₀
  have hid' : idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ) * Ideal.span {τ gQ.det} =
      𝔫.map τ * idx K 0 (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ (FA false) F (fun a => M (.inr a)) (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
    rw [hQd, map_one, Ideal.span_singleton_one, Ideal.mul_top, idxZero, Ideal.mul_top]
    exact hid₀ (FA true) F (fun a => M (.inl a)) hD.1 τ hτ
  obtain ⟨hP0, hQ0, hdP, hdQ⟩ :=
    GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H K ρ σ₁ p 0 X χ hχ gP gQ hg (FA true) (FA false) F _ _ hD h hF τ hτ
  obtain ⟨hle, hrk1, -, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA F M hM
  set τb : 𝓞 E →+* 𝓞 K := τ.comp (H.bar : 𝓞 E →+* 𝓞 E) with hτb
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτb' : τb H.rt = -ρ := by
    simp [hτb, GlobalTheory.CM.EigDec.bar_rt, hτ]
  have hne : ¬ τb H.rt = ρ := by
    rw [hτb']
    intro e
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact hρ ((mul_eq_zero.1 this).resolve_left two_ne_zero)
  have hdec := (GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ X.B F p 0 X.split X.typeB X.ρ_sq).1
  have hrkP : latRank K (F.eigLat X.B.t.act τ) = p := by rw [hdec, if_pos hτ]
  have hrkQ : latRank K (F.eigLat X.B.t.act τb) = 0 := by rw [hdec, if_neg hne]
  have hfg : ∀ σ, (F.eigLat X.B.t.act σ).FG := fun σ =>
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ F).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hsubP : subP (FA true) F (fun a => M (.inl a)) τ ≤ F.eigLat X.B.t.act τ :=
    iSup_le fun a => hle (.inl a, τ)
  have hsubQ : subQ (FA false) F (fun a => M (.inr a)) τb ≤ F.eigLat X.B.t.act τb :=
    iSup_le fun a => hle (.inr a, τb)
  have hrsP : latRank K (subP (FA true) F (fun a => M (.inl a)) τ) = p := by
    unfold subP
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin p => ((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ))
      fun a b e => by simpa using e)).trans ?_
    have h1 : ∀ a : Fin p, latRank K (((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K))) = 1 := fun a => by
      have := hrk1 (.inl a, τ)
      simpa [hτ] using this
    calc _ = ∑ _a : Fin p, 1 := Finset.sum_congr rfl fun a _ => h1 a
      _ = p := by simp
  have hrsQ : latRank K (subQ (FA false) F (fun a => M (.inr a)) τb) = 0 := by
    unfold subQ
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin 0 => ((FA false).eigLat (X.A false).t.act τb).map
        ((M (.inr a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin 0 => ((Sum.inr a : Fin p ⊕ Fin 0), τb))
      fun a b e => by simpa using e)).trans ?_
    simp
  obtain ⟨hneP, hdegP⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h p _ _ hsubP (hfg τ) hrkP hrsP
  obtain ⟨hneQ, hdegQ⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h 0 _ _ hsubQ (hfg τb) hrkQ hrsQ
  rw [hdegP, hdegQ, hdP, hdQ]
  have hdvd := (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ ⊥).1
  have hfE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfK : 0 < Module.finrank ℚ K := Module.finrank_pos
  set n := Module.finrank ℚ K / Module.finrank ℚ E with hn
  have hnK : (Module.finrank ℚ K : ℝ) = n * Module.finrank ℚ E := by
    rw [hn, Nat.cast_div hdvd (by exact_mod_cast hfE.ne')]
    field_simp
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hfK hdvd) hfE
  have hbar : Ideal.absNorm (𝔫.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔫 := by
    rw [(GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E E _ 𝔫).2, Nat.div_self hfE, pow_one]
  have hnorm : ∀ x : 𝓞 E, (Ideal.absNorm (Ideal.span {x}) : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := fun x => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  have hspan : Ideal.span {τ gQ.det} = (Ideal.span {gQ.det}).map τ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at hid'
  have e1 := congrArg Ideal.absNorm hid'
  rw [map_mul, map_mul, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2] at e1
  have e2 := congrArg Ideal.absNorm h𝔫
  rw [map_mul, hbar, ← Ideal.span_singleton_mul_span_singleton, map_mul] at e2
  have hA : (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneP)
  have hB : (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneQ)
  have hP1 : (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hP0))
  have hQ1 : (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hQ0))
  have hN1 : (Ideal.absNorm 𝔫 : ℝ) ≠ 0 := by
    intro h0
    have : ((Ideal.absNorm 𝔫 * Ideal.absNorm 𝔫 : ℕ) : ℝ) = 0 := by push_cast; rw [h0, zero_mul]
    rw [e2] at this
    push_cast at this
    exact (mul_ne_zero hP1 hQ1) this
  have l1 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e1
  have l2 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e2
  simp only [Nat.cast_mul, Nat.cast_pow] at l1 l2
  rw [Real.log_mul hA (pow_ne_zero _ hQ1), Real.log_mul (pow_ne_zero _ hN1) hB, Real.log_pow, Real.log_pow] at l1
  rw [Real.log_mul hN1 hN1, Real.log_mul hP1 hQ1] at l2
  rw [← hnorm, ← hnorm]
  have hfE' : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast hfE.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have key : Real.log (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ)
        / Module.finrank ℚ K
      - Real.log (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ)
        / Module.finrank ℚ K =
      Real.log (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) / (2 * Module.finrank ℚ E)
        - Real.log (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) / (2 * Module.finrank ℚ E) := by
    rw [← sub_div, ← sub_div, hnK]
    rw [div_eq_div_iff (mul_ne_zero hn' hfE') (mul_ne_zero two_ne_zero hfE')]
    linear_combination (2 * Module.finrank ℚ E : ℝ) * l1 + (n : ℝ) * (Module.finrank ℚ E : ℝ) * l2
  linear_combination key

end GlobalTheory.FlatCore.CMDiff0

end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  atlas_forward_decl GlobalTheory.FlatCore.CMDiff0.cmDiff_definite
end

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FlatCore

namespace GlobalTheory.DefCoreLie

theorem frameDeg_def (hCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) [NeZero H.d] (χ : DirichletCharacter ℂ H.d) (hχ : GlobalTheory.IsKroneckerChar χ)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (hL : Laws U x) (hq : Dw.q = 0) : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh hq t htρ)⟩

end GlobalTheory.DefCoreLie

namespace GlobalTheory.DefCoreLie

theorem degLie_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := GlobalTheory.T.deformation_case_finite_components p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl

end GlobalTheory.DefCoreLie
end
