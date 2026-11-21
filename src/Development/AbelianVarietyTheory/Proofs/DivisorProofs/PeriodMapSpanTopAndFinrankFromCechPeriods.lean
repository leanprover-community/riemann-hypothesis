import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLattice

section
namespace GlobalTheory

theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_eval_eq_top_and_finrank_dual : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  intro W _ _ Λ _ n b P hinj hsurj
  let Φ : W →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => P (b i))
  have hΦ : ∀ w i, Φ w i = P (b i) w := fun w i => rfl
  have h1 : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    intro l
    rw [← b.sum_repr l, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have h2 : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (b.constr ℤ v).toAddMonoidHom
    refine ⟨w, funext fun i => ?_⟩
    rw [hΦ, hw]
    simp
  let e : W ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofBijective Φ ⟨h1, h2⟩
  let c : Module.Basis (Fin n) ℂ W := Module.Basis.ofEquivFun e
  have hc : ∀ i, c.dualBasis i = P (b i) := by
    intro i
    ext w
    rw [Module.Basis.dualBasis_apply]
    exact hΦ w i
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← c.dualBasis.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · simpa using Module.finrank_eq_card_basis c.dualBasis

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeEvaluation_span_dual_finrank : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  atlas_forward_decl GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
open Opposite GlobalTheory.CatCoh

namespace GlobalTheory.CechPer

theorem eq_zero_of_isPer_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  intro A _ g L u hA x hx
  obtain ⟨c, h, rfl, ⟨hd, hc, hω⟩, hp⟩ := hx
  obtain ⟨hopen, -, -, -, -, hmono, -, hloc, hres, halg, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have vsub : ∀ (U : A.left.Opens) (a b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a - b : Sec (str A) U) z = val u.ex U a z - val u.ex U b z := by
    intro U a b z hz
    obtain ⟨e, he⟩ := halg U z hz
    exact (he (a - b : Sec (str A) U)).trans ((map_sub e a b).trans (congrArg₂ (· - ·) (he a).symm (he b).symm))
  have hreg : ∀ U V : A.left.affineOpens, IsReg u.ex (U.1 ⊓ V.1) (h U - h V) := by
    intro U V
    apply GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA
    intro z hz
    obtain ⟨W, hW, hzW⟩ := hloc _ z hz
    have hWU : W ≤ U := (le_inf_iff.1 hW).1
    have hWV : W ≤ V := (le_inf_iff.1 hW).2
    refine ⟨W.1, hW, hzW, (c.1.1 (op V) (op W) (homOfLE hWV).op - c.1.1 (op U) (op W) (homOfLE hWU).op :
      Sec (str A) W.1), fun y hy ↦ ?_⟩
    have e0 := vsub W.1 (c.1.1 (op V) (op W) (homOfLE hWV).op) (c.1.1 (op U) (op W) (homOfLE hWU).op) y hy
    have e1 := hc U W (homOfLE hWU).op y hy
    have e2 := hc V W (homOfLE hWV).op y hy
    refine Eq.trans ?_ e0.symm
    rw [Pi.sub_apply]
    linear_combination e2 - e1
  have hb := GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA A.left.affineOpens (fun U ↦ U.1) h
    (iSup_affineOpens_eq_top A.left) hd (fun U l z hz ↦ by simpa using hp U l z hz) hreg
  choose b hb using hb
  let b' : ∀ U : A.left.affineOpens, Sec (str A) U.1 := b
  refine (Hyp1.mk_eq_zero (F := OAff (str A))).2 ⟨fun T ↦ b' T.unop, Tot1.ext (fun T T' a ↦ ?_) (fun T ↦ ?_)⟩
  · obtain ⟨U⟩ := T
    obtain ⟨V⟩ := T'
    have hVU : V.1 ≤ U.1 := leOfHom a.unop
    have hz0 := GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA V.1
      ((b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1)) (fun z hz ↦ by
        have e0 := vsub V.1 (b' V - Sec.res (str A) hVU (b' U)) (c.1.1 (op U) (op V) a) z hz
        have e1 := vsub V.1 (b' V) (Sec.res (str A) hVU (b' U)) z hz
        have e2 := hres U.1 V.1 hVU (b' U) z hz
        have e3 : h V z = val u.ex V.1 (b' V) z := hb V z hz
        have e4 : h U z = val u.ex U.1 (b' U) z := hb U z (hmono _ _ hVU hz)
        have e5 := hc U V a z hz
        refine e0.trans ?_
        linear_combination e1 - e2 - e3 + e4 + e5)
    exact sub_eq_zero.1 (show (b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1) = 0 from hz0)
  · obtain ⟨U⟩ := T
    change KaehlerDifferential.D ℂ (Sec (str A) U.1) (b' U) = c.1.2 (op U)
    apply sub_eq_zero.1
    apply GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA U
    intro z hz
    rw [map_sub, (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz).2.2 (b' U), ← hω U z hz, sub_eq_zero]
    refine (Filter.EventuallyEq.fderiv_eq ?_).symm
    filter_upwards [(hopen U.1).mem_nhds hz] with y hy
    exact hb U y hy

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  atlas_forward_decl GlobalTheory.CechPer.eq_zero_of_isPer_zero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem evForm_secPull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  intro A _ g L u A' _ g' L' u' φ M h hM p z hz
  have hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left := fun w => by rw [hM w]; rfl
  have hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) w =
      val u.ex p.1.2.1 b (M w) := by
    intro w hw b
    have k := valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw
    rw [← hpt] at k
    exact k
  have hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1 := by
    intro w hw
    change ⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1
    rw [hpt, top_le_preimage_comp]
    exact fun x hx => p.2 (hw hx)
  refine ⟨hpre z hz, hval z hz, ?_⟩
  have hopen : ∀ U, IsOpen (pre u.ex U) := fun U => (u.hol U 0).1
  have hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U) := fun U b => (u.hol U b).2
  have hopen' : ∀ U, IsOpen (pre u'.ex U) := fun U => (u'.hol U 0).1
  obtain ⟨-, hsm, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)
  obtain ⟨-, hsm', hD'⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz
  intro ξ
  have hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [SemiHom.m1_D, hD', hD]
    have e : val u'.ex p.1.1.1 (secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M :=
      Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b
    rw [e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz)))
      M.differentiableAt, M.fderiv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, ContinuousLinearMap.add_comp]
  | smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  atlas_forward_decl GlobalTheory.CechPer.evForm_secPull
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isPer_of_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  intro A _ g L u c K W k q hcomp hbasis hdiff hder hper
  classical
  obtain ⟨hopen, hvd, hpp, hvp, -, hmono, -, -, hres, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hev := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u
  have hevres := GlobalTheory.T.evForm_restriction_eq A g L u
  let f : ∀ (U V : A.left.affineOpens), V ≤ U → Sec (str A) V.1 := fun U V h ↦
    c.1.1 (Opposite.op U) (Opposite.op V) (homOfLE h).op
  have hf : ∀ (U V T : A.left.affineOpens) (h : V ≤ U) (h' : T ≤ V), ∀ z ∈ pre u.ex T.1,
      val u.ex T.1 (f U T (h'.trans h)) z = val u.ex V.1 (f U V h) z + val u.ex T.1 (f V T h') z := by
    intro U V T h h' z hz
    have e : f U T (h'.trans h) = Sec.res (str A) h' (f U V h) + f V T h' :=
      cechDeRhamTotalCocyclesOne.comp c (homOfLE h).op (homOfLE h').op
    obtain ⟨ev, hev⟩ := halg T.1 z hz
    rw [← hres V.1 T.1 h' _ z hz, e]
    exact (hev _).trans ((map_add ev _ _).trans (congrArg₂ _ (hev _).symm (hev _).symm))
  let h : A.left.affineOpens → (Fin g → ℂ) → ℂ := fun U z ↦
    if hz : z ∈ pre u.ex U.1 then
      k (hbasis U z hz).choose z - val u.ex _ (f U _ (hbasis U z hz).choose_spec.1) z else 0
  have hh : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U z = k i z - val u.ex _ (f U _ hi) z := by
    intro U i hi z hz
    have hzU : z ∈ pre u.ex U.1 := hmono _ _ hi hz
    obtain ⟨hj, hzj⟩ := (hbasis U z hzU).choose_spec
    simp only [h, dif_pos hzU]
    generalize_proofs p1 p2
    generalize p1.choose = j at *
    obtain ⟨l, hli, hlj, hzl, e1, e2⟩ := hcomp i j z hz hzj
    have a1 := hf U _ _ hi hli z hzl
    have a2 := hf U _ _ hj hlj z hzl
    have b1 : k l z = k i z + val u.ex _ (f _ _ hli) z := e1 _
    have b2 : k l z = k j z + val u.ex _ (f _ _ hlj) z := e2 _
    linear_combination b1 - b2 - a1 + a2
  have hnhds : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U =ᶠ[nhds z] fun y ↦ k i y - val u.ex _ (f U _ hi) y := fun U i hi z hz ↦
    Filter.eventually_of_mem ((hopen _).mem_nhds hz) fun y hy ↦ hh U i hi y hy
  refine ⟨c, h, rfl, ⟨fun U z hz ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    exact ((((hdiff i).differentiableAt n).sub ((hvd _ _).differentiableAt n)).congr_of_eventuallyEq
      (hnhds U i hi z hzi)).differentiableWithinAt
  · obtain ⟨i, hi, hzi⟩ := hbasis V z hz
    have hVU : V ≤ U := leOfHom a.unop
    have a1 := hf U V _ hVU hi z hzi
    change _ = _ + val u.ex V.1 (f U V hVU) z
    rw [hh V i hi z hzi, hh U i (hi.trans hVU) z hzi, a1]
    ring
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    refine (hnhds U i hi z hzi).fderiv_eq.trans ((fderiv_fun_sub ((hdiff i).differentiableAt n)
      ((hvd _ (f U _ hi)).differentiableAt n)).trans ?_)
    rw [hder i z hzi, sub_eq_iff_eq_add]
    refine (congrArg _ (cechDeRhamTotalCocyclesOne.conn c (homOfLE hi).op)).trans ((map_add _ _ _).trans ?_)
    exact congrArg₂ _ (hevres U (W i) (homOfLE hi).op _ z hzi) ((hev _ z hzi).2.2 _)
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    rw [hh U i hi z hzi, hh U i hi _ ((hpp _ l z).2 hzi), hper i l z hzi, hvp _ (f U _ hi)]
    ring

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  atlas_forward_decl GlobalTheory.CechPer.isPer_of_basis
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.Nat

theorem isPer_pull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  intro A _ g L u A' _ g' L' u' φ M h hex hM x x' q hp hx
  obtain ⟨c, h₀, rfl, ⟨hd, hc, hw⟩, hq⟩ := hx
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ x'
  have hp' : Hyp1.mk _ (pullZZ1 (pairPull h) c) = Hyp1.mk _ (pullZZ1 (pairRes φ.left (str A')) c') := hp
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 hp'
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10, -, a12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10, -, b12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A' g' L' u'
  let Mc : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap M
  have hP := GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback A g L u A' g' L' u' φ Mc h hex
  have hpre : ∀ (U : A.left.Opens) z, z ∈ pre u'.ex (φ.left ⁻¹ᵁ U) ↔ M z ∈ pre u.ex U := by
    intro U z
    change ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ.left ⁻¹ᵁ U) ↔ ⊤ ≤ (u.ex (M z)).left ⁻¹ᵁ U
    rw [hex]
    rfl
  have hf : ∀ (p l : Pair φ.left) (e : l ≤ p) (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1)
      (a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2),
      (show Sec (str A') l.1.1.1 from b (Opposite.op l)) - Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p)) =
        secPull (str A) (str A') l (c.1.1 _ _ a') - (show Sec (str A') l.1.1.1 from c'.1.1 _ _ a) := by
    intro p l e a a'
    exact congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.1 (Opposite.op p) (Opposite.op l) (homOfLE e).op) hb
  have hω : ∀ (p : Pair φ.left), KaehlerDifferential.D ℂ (Sec (str A') p.1.1.1) (b (Opposite.op p)) =
      (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) -
        (show Ω[Sec (str A') p.1.1.1⁄ℂ] from c'.1.2 (Opposite.op p.1.1)) := by
    intro p
    have e1 := congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.2 (Opposite.op p)) hb
    have e2 : q1 (pairRes φ.left (str A')) (Opposite.op p) (c'.1.2 (Opposite.op p.1.1)) = c'.1.2 (Opposite.op p.1.1) :=
      SemiHom.oneFormMap_eq_self_of_id _ (fun _ => rfl) _
    exact e1.trans (congrArg (fun t => (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) - t) e2)
  have hstep : ∀ (p l : Pair φ.left) (e : l ≤ p), ∀ z ∈ pre u'.ex l.1.1.1, ∀ (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1),
      h₀ l.1.2 (M z) - val u'.ex l.1.1.1 (b (Opposite.op l)) z =
        h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z + val u'.ex l.1.1.1 (c'.1.1 _ _ a) z := by
    intro p l e z hz a
    obtain ⟨hz', hv, -⟩ := hP l z hz
    let a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2 := (homOfLE (Pair.le_snd e)).op
    have hs : ∀ x y v w : Sec (str A') l.1.1.1, x - y = v - w →
        val u'.ex l.1.1.1 x z - val u'.ex l.1.1.1 y z = val u'.ex l.1.1.1 v z - val u'.ex l.1.1.1 w z := by
      intro x y v w e
      obtain ⟨ev, hev⟩ := b10 _ z hz
      rw [hev x, hev y, hev v, hev w, ← map_sub, ← map_sub, e]
    have e1 : val u'.ex l.1.1.1 (b (Opposite.op l)) z -
        val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex l.1.1.1 (secPull (str A) (str A') l (c.1.1 _ _ a')) z - val u'.ex l.1.1.1 (c'.1.1 _ _ a) z :=
      hs _ _ _ _ (hf p l e a a')
    have e3 : val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex p.1.1.1 (b (Opposite.op p)) z := b9 _ _ _ _ z hz
    have e4 : val u'.ex l.1.1.1 (secPull (str A) (str A') l (c.1.1 _ _ a')) z =
        val u.ex l.1.2.1 (c.1.1 _ _ a') (M z) := hv _
    have e2 := hc p.1.2 l.1.2 a' (M z) hz'
    linear_combination e2 - e1 - e3 - e4
  refine GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis A' g' L' u' c' (Pair φ.left) (fun p => p.1.1)
    (fun p z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z) _ ?_ ?_ ?_ ?_ ?_
  · intro p r z hzp hzr
    have h1 : M z ∈ pre u.ex (p.1.2.1 ⊓ r.1.2.1) := by
      rw [a5]; exact ⟨(hP p z hzp).1, (hP r z hzr).1⟩
    obtain ⟨U, hU, hzU⟩ := a8 _ _ h1
    have h2 : z ∈ pre u'.ex (p.1.1.1 ⊓ r.1.1.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5, b5]; exact ⟨⟨hzp, hzr⟩, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    let l : Pair φ.left := ⟨(W, U), hW.trans inf_le_right⟩
    have lp : l ≤ p := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ p.1.1.1 from hW.trans (inf_le_left.trans inf_le_left), show U.1 ≤ p.1.2.1 from hU.trans inf_le_left⟩)
    have lr : l ≤ r := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ r.1.1.1 from hW.trans (inf_le_left.trans inf_le_right), show U.1 ≤ r.1.2.1 from hU.trans inf_le_right⟩)
    exact ⟨l, Pair.le_fst lp, Pair.le_fst lr, hzW, hstep p l lp z hzW, hstep r l lr z hzW⟩
  · intro U' z hz
    obtain ⟨U, -, hzU⟩ := a8 _ _ (a12 (M z))
    have h2 : z ∈ pre u'.ex (U'.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5]; exact ⟨hz, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    exact ⟨⟨(W, U), hW.trans inf_le_right⟩, show W.1 ≤ U'.1 from hW.trans inf_le_left, hzW⟩
  · intro p
    exact ((hd p.1.2).comp Mc.differentiable.differentiableOn fun z hz => (hP p z hz).1).sub (b2 _ _)
  · intro p z hz
    obtain ⟨hz', -, hE⟩ := hP p z hz
    have d1 : DifferentiableAt ℂ (h₀ p.1.2) (Mc z) := (hd p.1.2).differentiableAt ((a1 _).mem_nhds hz')
    have d2 : DifferentiableAt ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z :=
      (b2 _ _).differentiableAt ((b1 _).mem_nhds hz)
    have d3 : HasFDerivAt (fun z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z)
        ((fderiv ℂ (h₀ p.1.2) (Mc z)).comp Mc - fderiv ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z) z :=
      (d1.hasFDerivAt.comp z Mc.hasFDerivAt).sub d2.hasFDerivAt
    have e1 := congrArg (evForm u'.ex p.1.1.1 z) (hω p)
    rw [map_sub, hE] at e1
    have e2 := ((GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' _ z hz).2.2 (b (Opposite.op p))).symm.trans e1
    rw [d3.fderiv, hw p.1.2 _ hz']
    exact (congrArg (fun t => _ - t) e2).trans (sub_sub_cancel _ _)
  · intro p l z hz
    have e1 := hq p.1.2 ⟨M l, hM l⟩ (M z) (hP p z hz).1
    change h₀ p.1.2 (M (z + l)) - _ = _
    have e2 : val u'.ex p.1.1.1 (b (Opposite.op p)) (z + l) = val u'.ex p.1.1.1 (b (Opposite.op p)) z := b4 _ _ l z
    rw [map_add, e2]
    change h₀ p.1.2 (M z + M l) = _ at e1
    rw [e1]
    ring

end GlobalTheory.CechPer.Nat
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_of_isPull1_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  atlas_forward_decl GlobalTheory.CechPer.Nat.isPer_pull
end

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_holUnif_square : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  intro A _ g L u hA
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hg := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨n, hn⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ (A ⊗ A) hAA
  obtain ⟨L', ⟨v⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif (A ⊗ A) n hAA hn
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨M₁, hM₁, hΛ₁, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (fst A A) inferInstance
  obtain ⟨M₂, hM₂, hΛ₂, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (snd A A) inferInstance
  refine ⟨n, L', v, M₁, M₂, hAA, hM₁, hM₂, fun w => ?_, fun l => hΛ₁ l l.2, fun l => hΛ₂ l l.2⟩
  rw [LinearMap.add_apply, u.ex_add, hM₁, hM₂, Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  atlas_forward_decl GlobalTheory.CechPer.exists_holUnif_square
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem mem_primDR_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  intro A _ g L u hA c p hp
  obtain ⟨n, L', v, M₁, M₂, hAA, h1, h2, h3, hM1, hM2⟩ := GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety A g L u hA
  rw [mem_prim_iff]
  have key : ∀ (φ : A ⊗ A ⟶ A) (M : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (_hw : ∀ w, u.ex (M w) = v.ex w ≫ φ)
      (hM : ∀ l : v.Λ, M l ∈ u.Λ),
      IsPer v.ex v.Λ (cmp1 (str (A ⊗ A)) (pullOver (dp0 ℂ) (𝟙 _) φ c)) (fun l ↦ p ⟨M l, hM l⟩) := by
    intro φ M hw hM
    have hm := IsMor.of_over (dp0 ℂ) (φ := φ.left) (s := str A) (s' := str (A ⊗ A))
      (by rw [← Category.assoc, Over.w])
    exact GlobalTheory.T.isPer_of_isPull1_of_isPer A g L u (A ⊗ A) n L' v φ M hm.w hw hM _ _ _ (comparison_pullback hm c) hp
  have hμ := key μ[A] (M₁ + M₂) h3 (fun l ↦ add_mem (hM1 l) (hM2 l))
  have hf := key (fst A A) M₁ h1 hM1
  have hs := key (snd A A) M₂ h2 hM2
  obtain ⟨hlin, -⟩ := GlobalTheory.T.cechDeRhamPeriods_linear (A ⊗ A) n L' v
  have hdiff := (hlin _ _ _ _ hμ (hlin _ _ _ _ hf hs).1).2
  have hq : ((fun l : v.Λ ↦ p ⟨(M₁ + M₂) l, add_mem (hM1 l) (hM2 l)⟩) -
      ((fun l : v.Λ ↦ p ⟨M₁ l, hM1 l⟩) + fun l : v.Λ ↦ p ⟨M₂ l, hM2 l⟩)) = 0 := by
    funext l
    rw [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_eq_zero, ← map_add]
    rfl
  rw [hq] at hdiff
  have h0 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero (A ⊗ A) n L' v hAA _ hdiff
  rw [← map_add, ← map_sub] at h0
  exact sub_eq_zero.1 ((GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex (A ⊗ A) hAA).1 (h0.trans (map_zero _).symm))

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  atlas_forward_decl GlobalTheory.CechPer.mem_primDR_of_isPer
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_prim_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q,
    IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧
      ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  intro A _ g L u x q hx c hc
  obtain ⟨hOpen, hDiff, -, hPer, -, -, -, -, hRes, hHom, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨c₀, h₀, hc₀, ⟨p1, p2, p3⟩, hp⟩ := hx
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 (hc.trans hc₀.symm)
  have hval_add : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s + t) z = val u.ex U s z + val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_add]
  have hval_sub : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s - t) z = val u.ex U s z - val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_sub]
  have hcf : ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V),
      c.1.1 (Opposite.op U) (Opposite.op V) a = c₀.1.1 (Opposite.op U) (Opposite.op V) a +
        (b (Opposite.op V) - Sec.res (str A) (leOfHom a.unop) (b (Opposite.op U))) := by
    intro U V a
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.1 (Opposite.op U) (Opposite.op V) a) hb
    simp only [dTot0_f] at this
    exact (eq_add_of_sub_eq' this.symm :)
  have hcω : ∀ U : A.left.affineOpens, c.1.2 (Opposite.op U) =
      c₀.1.2 (Opposite.op U) + KaehlerDifferential.D ℂ _ (b (Opposite.op U)) := by
    intro U
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.2 (Opposite.op U)) hb
    simp only [dTot0_ω] at this
    change _ = (c.1 - c₀.1).2 _ at this
    rw [this]
    change c.1.2 _ = c₀.1.2 _ + (c.1.2 _ - c₀.1.2 _)
    abel
  refine ⟨fun U z ↦ h₀ U z + val u.ex U.1 (b (Opposite.op U)) z, ⟨fun U ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩,
    fun U l z hz ↦ ?_⟩
  · exact (p1 U).add (hDiff U.1 _)
  · have hle : V.1 ≤ U.1 := leOfHom a.unop
    have hr : val u.ex V.1 (Sec.res (str A) hle (b (Opposite.op U))) z = val u.ex U.1 (b (Opposite.op U)) z :=
      hRes U.1 V.1 hle _ z hz
    simp only
    rw [p2 U V a z hz, hcf U V a, hval_add _ _ _ z hz, hval_sub _ _ _ z hz, hr]
    ring
  · have hd₀ : DifferentiableAt ℂ (h₀ U) z := ((p1 U) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    have hd₁ : DifferentiableAt ℂ (val u.ex U.1 (b (Opposite.op U))) z :=
      ((hDiff U.1 _) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    obtain ⟨-, -, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    change fderiv ℂ (h₀ U + val u.ex U.1 (b (Opposite.op U))) z = _
    rw [fderiv_add hd₀ hd₁, p3 U z hz, hcω U, map_add, hD]
  · simp only
    rw [hp U l z hz]
    erw [hPer]
    ring

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q, IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧ ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  atlas_forward_decl GlobalTheory.CechPer.exists_prim_of_isPer
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem zero_periods_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  intro A _ g L u q hq
  obtain ⟨hopen, -, hadd, -, hinf, -, -, hbasis, -, -, -, htop⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨h, ⟨hdiff, hres0, hder0⟩, hper⟩ := GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods A g L u 0 q hq 0 (map_zero _)
  have hres : ∀ (U V : A.left.affineOpens), V.1 ≤ U.1 → ∀ z ∈ pre u.ex V.1, h V z = h U z := by
    intro U V hVU z hz
    have := hres0 U V (homOfLE hVU).op z hz
    rw [this]
    change h U z + valAt' _ _ (0 : Γ(A.left, V.1)) = h U z
    unfold valAt' valAt
    split_ifs <;> simp
  have hder : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, fderiv ℂ (h U) z = 0 := by
    intro U z hz
    rw [hder0 U z hz]
    change evForm u.ex U.1 z 0 = 0
    simp
  have hex : ∀ z, ∃ U : A.left.affineOpens, z ∈ pre u.ex U.1 := fun z ↦ by
    obtain ⟨W, -, hW⟩ := hbasis ⊤ z (htop z)
    exact ⟨W, hW⟩
  choose Uz hUz using hex
  let G : (Fin g → ℂ) → ℂ := fun z ↦ h (Uz z) z
  have hG : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, G z = h U z := by
    intro U z hz
    obtain ⟨W, hWle, hW⟩ := hbasis (U.1 ⊓ (Uz z).1) z (by rw [hinf]; exact ⟨hz, hUz z⟩)
    have h1 := hres U W (hWle.trans inf_le_left) z hW
    have h2 := hres (Uz z) W (hWle.trans inf_le_right) z hW
    simp only [G]
    rw [← h1, ← h2]
  have hloc : ∀ z, G =ᶠ[nhds z] h (Uz z) := fun z ↦ by
    filter_upwards [(hopen _).mem_nhds (hUz z)] with w hw
    exact hG _ w hw
  have hGd : Differentiable ℂ G := fun z ↦
    (((hdiff (Uz z)).differentiableAt ((hopen _).mem_nhds (hUz z)))).congr_of_eventuallyEq (hloc z)
  have hGf : ∀ z, fderiv ℂ G z = 0 := fun z ↦ by
    rw [(hloc z).fderiv_eq]; exact hder _ z (hUz z)
  funext l
  have hl : (0 : Fin g → ℂ) + l ∈ pre u.ex (Uz 0).1 := (hadd _ l 0).2 (hUz 0)
  have e1 := hper (Uz 0) l 0 (hUz 0)
  have e2 := hG (Uz 0) _ hl
  have e3 := is_const_of_fderiv_eq_zero hGd hGf ((0 : Fin g → ℂ) + l) 0
  have e4 := hG (Uz 0) 0 (hUz 0)
  simp only [Pi.zero_apply]
  linear_combination -e1 - e2 + e3 + e4

end GlobalTheory.CechPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  atlas_forward_decl GlobalTheory.CechPer.zero_periods_eq_zero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechPer.isPer_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  intro A _ g L u x q q' hq hq'
  have h := ((GlobalTheory.T.cechDeRhamPeriods_linear A g L u).1 x x q q' hq hq').2
  rw [sub_self] at h
  exact sub_eq_zero.mp (GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero A g L u _ h)
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_unique' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  atlas_forward_decl GlobalTheory.CechPer.isPer_unique
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_periods_eq_top_and_finrank : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  intro A _ g L u hA P hP
  obtain ⟨b, -, -⟩ := GlobalTheory.exists_basis_of_discrete_of_span_eq_top_complex_pi g u.Λ u.discrete u.full
  refine GlobalTheory.T.latticeEvaluation_span_dual_finrank (primDR A) u.Λ (2 * g) b P (fun w hw ↦ ?_) (fun p ↦ ?_)
  · have h0 : (fun l ↦ P l w) = 0 := funext hw
    have h1 := hP w
    rw [h0] at h1
    have h2 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero A g L u hA _ h1
    have h3 : w.1 = 0 := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).1 (h2.trans (map_zero _).symm)
    exact Subtype.ext h3
  · obtain ⟨x, hx⟩ := GlobalTheory.T.surjective_periodMap_abelianVariety_lattice A g L u hA p
    obtain ⟨c, rfl⟩ := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).2 x
    have hc := GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods A g L u hA c p hx
    exact ⟨⟨c, hc⟩, fun l ↦ congrFun (GlobalTheory.T.isPer_unique' A g L u _ _ _ (hP ⟨c, hc⟩) hx) l⟩

end GlobalTheory.CechPer
end
