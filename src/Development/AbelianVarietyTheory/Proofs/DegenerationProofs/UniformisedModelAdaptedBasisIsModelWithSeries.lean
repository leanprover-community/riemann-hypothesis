import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformised
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparates
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.Shift
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

theorem lin_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (s : LB.Sec (LB.LinComb L φ ε)) (t : I → LB.Sec (LB.LinComb L φ ε)) :
    (∀ j, s.f j = ∑ i, constFn p _ (a i) * (t i).f j) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        sval s r z J = ∑ i, cst (r ≫ p) z (a i) * sval (t i) r z J := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι) (hm : r z ∈ LB.wchart L φ j),
      gs r z (LB.wchart L φ j) (∑ i, constFn p (LB.wchart L φ j) (a i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
        ∑ i, cst (r ≫ p) z (a i) * gs r z (LB.wchart L φ j) ((t i).f j) := fun Z r z j hm => by
    have e : ∀ (b : I → Γ(Y, LB.wchart L φ j)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
      simp only [gs_eq r z _ hm, map_sum]
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)
  constructor
  · intro h Z r z J hJ
    exact (congrArg (gs r z _) (h _)).trans (key Z r z _ (hJ.mem φ r))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have m := hJ'.mem φ (𝟙 Y)
    refine (sec_trans s (𝟙 Y) y (j := j) hy m).trans (Eq.trans ?_ (key Y (𝟙 Y) y j hy).symm)
    refine (congrArg _ (h Y (𝟙 Y) y J hJ')).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (t i) (𝟙 Y) y (j := j) hy m]
    exact mul_left_comm _ _ _

section
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V)

abbrev tr (mu : D.X) : D.P.A.left ⟶ D.P.A.left := (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A mu).left

theorem tr_hom (mu : D.X) : tr D mu ≫ D.P.A.hom = D.P.A.hom := Over.w _

theorem tr_tr (mu nu : D.X) (h : mu + nu = 0) : tr D mu ≫ tr D nu = 𝟙 _ := by
  have c₃ : SectionScalarValuation.cQ D D.P.A 0 = 1 := by
    have := SectionScalarValuation.cQ_nsmul D D.P.A 0 0
    rwa [zero_nsmul, pow_zero] at this
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ, _root_.mul_assoc, ← SectionScalarValuation.cQ_add, h, c₃,
    _root_.mul_one, Over.id_left]

abbrev EB (k : ℕ) (α mu : D.X) : Type :=
  LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)) (DegPre.deltaε k))

def Rel {k : ℕ} {α mu : D.X} (e : EB D k α mu) (β : D.SecB k α) (gm : D.SecB k (α + k • mu)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval gm r z J = sval β (r ≫ tr D mu) z J * (val e r z J).val

theorem exists_fwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (β : D.SecB k α) : ∃ gm, Rel D e β gm := by
  have hform : FormEq (Sum.elim (fun i => tr D mu ≫ D.famφB α i)
      (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨gm, hgm⟩ := exists_sec D.P.isLB hform (pullMulSec β (tr D mu) e he)
  exact ⟨gm, fun Z r z J hJ => (hgm Z r z J hJ).trans (sval_pullMulSec _ _ _ he r z hJ)⟩

theorem exists_bwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (gm : D.SecB k (α + k • mu)) :
    ∃ β, Rel D e β gm := by
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have h2 : tr D mu ≫ tr D (-mu) = 𝟙 _ := tr_tr D _ _ (add_neg_cancel mu)
  have hform : FormEq (Sum.elim (fun i => tr D (-mu) ≫ D.famφB (α + k • mu) i)
      (fun i => tr D (-mu) ≫ Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i) i))
      (Sum.elim (DegPre.famε k) (fun i => - DegPre.deltaε k i)) (D.famφB α) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib, inv_inv,
      ← Category.assoc, h1, Category.id_comp]
    rw [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  obtain ⟨β, hβ⟩ := exists_sec D.P.isLB hform (pullMulSec gm (tr D (-mu))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ e (tr D (-mu)))) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ he _)))
  refine ⟨β, fun Z r z J hJ => ?_⟩
  rw [hβ Z _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, val_inv, val_pull hJ, Category.assoc, h2, Category.comp_id,
    _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem isBasisB_move {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) {I : Type} [Fintype I]
    (β : I → D.SecB k α) (hβ : IsBasisB D β) (gm : I → D.SecB k (α + k • mu)) (u : Vˣ)
    (h : ∀ i, ∃ g, Rel D e (β i) g ∧ ∀ j, (gm i).f j = constFn D.P.A.hom _ (u : V) * g.f j) : IsBasisB D gm := by
  intro s
  obtain ⟨s₀, hs⟩ := exists_bwd D e he s
  choose g hg hgm using h
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval (gm i) r z J = cst (r ≫ D.P.A.hom) z (u : V) * (sval (β i) (r ≫ tr D mu) z J * (val e r z J).val) :=
    fun i Z r z J hJ => by
      rw [← hg i Z r z J hJ]
      exact (congrArg (gs r z _) (hgm i _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans
        (congrArg₂ (· * ·) (gs_constFn _ _ r z (hJ.mem _ r) _) rfl))
  have key : ∀ b : I → V, (∀ j, s.f j = ∑ i, constFn D.P.A.hom _ (b i) * (gm i).f j) ↔
      (∀ j, s₀.f j = ∑ i, constFn D.P.A.hom _ (b i * u) * (β i).f j) := fun b => by
    rw [lin_iff D.P.isLB D.P.A.hom b s gm, lin_iff D.P.isLB D.P.A.hom (fun i => b i * u) s₀ β]
    constructor
    · intro H Z r z J hJ
      have e1 := H Z (r ≫ tr D (-mu)) z J hJ
      rw [hs Z _ z J hJ] at e1
      simp only [hv _ Z _ z J hJ, Category.assoc, h1, Category.comp_id, tr_hom] at e1
      refine (val e (r ≫ tr D (-mu)) z J).isUnit.mul_right_cancel (e1.trans ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [H1.cst_mul]; ring
    · intro H Z r z J hJ
      rw [hs Z _ z J hJ, H Z _ z J hJ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hv _ Z _ z J hJ, H1.cst_mul, Category.assoc, tr_hom]; ring
  obtain ⟨a, ha, hu⟩ := hβ s₀
  refine ⟨fun i => a i * (u⁻¹ : Vˣ), (key _).2 (by simpa using ha), fun b hb => funext fun i => ?_⟩
  rw [← hu _ ((key b).1 hb)]
  simp
end

theorem shift (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    (k : ℕ) (α mu : D.toPre.X) (n : ℕ) (hn : k * Q mu + QForm.bOf D.toPre Q mu α = n) :
    ∃ (e : EB D.toPre k α mu) (u : Vˣ), e.IsGen ∧ ∀ (f : ∀ α, D.toPre.SecB k α) (s : Fam D.toPre (FractionRing V) k),
      FamOf D.toPre _ f s → ∃ g, Rel D.toPre e (f α) g ∧
        ∀ j, (f (α + k • mu)).f j = constFn D.toPre.P.A.hom _ (ϖ ^ n * u) * g.f j := by
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, ⟨u, hc₀⟩, hval⟩ := SectionScalarValuation.famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre k α mu e' he' hC
  refine ⟨eB, u, heB, fun f s hf => ?_⟩
  obtain ⟨g, hg⟩ := exists_fwd D.toPre eB heB (f α)
  refine ⟨g, hg, GlobalTheory.LevelOneIdeal.secIsMul_of_sval hL D.toPre.P.A.hom
    (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨w, hw, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing V) hG k mu α
  have vu := hv w hw hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ w).1 (s.fe mu α w hw hc) _ (𝟙 _) y J hJ
  rw [← SectionScalarValuation.secScal_sval (hf _) _ y hJ, ← SectionScalarValuation.secScal_sval (hf _) _ y hJ, Category.id_comp, Category.id_comp,
    SectionScalarValuation.trF_prB] at hrel
  rw [hrel, hg _ _ y J hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V) ≫ jK V =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing V))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing V)) y J hJ
  have v₂ := hval (FractionRing V) _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y J hJ
  have hc₁ : c₀ = algebraMap V (FractionRing V) (ϖ ^ n * u) := by
    rw [hc₀, hn, zpow_natCast, map_mul, map_pow]
  have v₃ : gs ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) y ⊤ (scal (𝟙 _) c₀) =
      cst ((DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom) y (ϖ ^ n * u) := by
    rw [← w₁, ← Category.assoc, hc₁]
    exact (cst_comp _ (algebraMap V (FractionRing V)) y _).symm
  have v₄ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ DegPre.jFR (R := V) (FractionRing V) =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom := w₁
  rw [v₃, v₄] at v₂
  rw [Over.id_left, Category.id_comp, uVal, Category.id_comp, Category.id_comp, comp_cP] at vu
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨hsh, _, _, _, hfam, _, hB⟩ i₀ α ⟨m, hm⟩
  subst hm
  obtain ⟨ϖ, Q, hϖ, hQ, hlt, hq⟩ := GlobalTheory.ZH.PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  have hne : (u.j ϖ : PadicAlgCl p) ≠ 0 := by
    show algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) ≠ 0
    rw [map_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))]
    exact hϖ.ne_zero
  have hc : 0 < -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := neg_pos.2 (Real.log_neg (norm_pos_iff.2 hne) hlt)
  have hle : ∀ a b, l.q a ≤ l.q b ↔ Q a ≤ Q b := fun a b => by
    rw [hq, hq, mul_le_mul_iff_left₀ hc, Int.cast_le]
  have hs := q_shift hϖ hQ (cls i₀) m k
  have h0 := (hle _ _).1 (hsh i₀ m)
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hnn : 0 ≤ k * Q m + QForm.bOf u.D.toPre Q m (cls i₀) :=
    nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) hk'
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  obtain ⟨e, w, he, H⟩ := shift hLL.1.globalFns hϖ u.D hQ k (cls i₀) m n hn
  rw [hn] at hs
  constructor
  · intro hS
    have h1 := (hle _ _).1 (hS (-m))
    rw [smul_neg, add_neg_cancel_right, hs] at h1
    have hn0 : n = 0 := by
      have : (n : ℤ) ≤ 0 := by nlinarith
      omega
    subst hn0
    refine isBasisB_move u.D.toPre e he _ (hB i₀) _ w fun i => ?_
    obtain ⟨s, hs'⟩ := hfam i.1
    obtain ⟨g, hg, hg'⟩ := H (f i.1) s hs'
    rw [pow_zero, _root_.one_mul] at hg'
    exact ⟨g, hg, hg'⟩
  · intro hS
    obtain ⟨s, hs'⟩ := hfam i₀
    obtain ⟨g, -, hg'⟩ := H (f i₀) s hs'
    refine ⟨_, g, ?_, hg'⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      refine hS fun m' => ?_
      rw [add_assoc, ← smul_add]
      refine le_trans ((hle _ _).2 ?_) (hsh i₀ (m + m'))
      rw [hs]; simp
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ.not_isUnit) n
      (Nat.pos_of_ne_zero hn0))

end GlobalTheory.ZH.Shift
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBasis_terms_at_other_class_members : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  atlas_forward_decl GlobalTheory.ZH.Shift.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RedGood

theorem wt_lin {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec} (h : IsLin Φ.G.hom F a φ) (α : Φ.E.X)
    (l : Φ.N₀.ι) : Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  rw [← WtLin.weight_sum Φ F a α l, ← h l]
  rfl

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) :
    constFn f U 0 = 0 := by
  simp only [constFn, map_zero]

theorem good_of_parts {k : Type} [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ)
    {J : Type} [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (R : J → Φ.E.X → (Φ.H 1).Sec)
    (pos : Filter.Tendsto q Filter.cofinite Filter.atTop) (short : ∀ i, Short q N (cls i))
    (uniq : ∀ i i', (∃ m, cls i = cls i' + N • m) → cls i = cls i')
    (cover : ∀ α, ∃ i m, α = cls i + N • m)
    (part : ∀ i α, Φ.IsPart α (F i) (R i α))
    (zero : ∀ i α, ¬ (Short q N α ∧ ∃ m, α = cls i + N • m) → ∀ l, Φ.wt (R i α) α l = 0)
    (basis : ∀ i₀ α, Short q N α → (∃ m, α = cls i₀ + N • m) → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ →
      ∃! a : {i // cls i = cls i₀} → k, IsLin Φ.G.hom (fun i : {i // cls i = cls i₀} => R i α) a φ) :
    Φ.Good N q cls F := by
  have hcls : ∀ i₀ i α, (∃ m, α = cls i₀ + N • m) → (∃ m, α = cls i + N • m) → cls i = cls i₀ := by
    rintro i₀ i α ⟨m, hm⟩ ⟨m', hm'⟩
    refine uniq i i₀ ⟨m - m', ?_⟩
    rw [smul_sub, ← add_sub_assoc, ← hm, hm', add_sub_cancel_right]
  have hsum : ∀ (i₀ : J) (α : Φ.E.X) (a : J → k), (∀ i, a i ≠ 0 → cls i = cls i₀) → ∀ l,
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l =
        ∑ i : {i // cls i = cls i₀}, constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l := by
    intro i₀ α a ha l
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp)
      (fun i => constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(part i α).2 l]
    · have : a i = 0 := by
        by_contra h
        exact hi (ha i h)
      rw [this, constFn_zero, zero_mul]
  refine ⟨pos, short, ?_, ?_, ?_⟩
  · rintro i β ⟨l, hl⟩
    by_contra h
    exact hl (((part i β).2 l).symm.trans (zero i β h l))
  · intro α hα φ hφ
    obtain ⟨i₀, hm⟩ := cover α
    obtain ⟨a, ha, -⟩ := basis i₀ α hα hm φ hφ
    have key : ∀ i, (if h : cls i = cls i₀ then a ⟨i, h⟩ else 0) ≠ 0 → cls i = cls i₀ := by
      intro i hi
      by_contra h
      exact hi (dif_neg h)
    refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun i hi => ?_, fun l => ?_⟩
    · rw [key i hi]
      exact hm
    · rw [hsum i₀ α _ key l, wt_lin Φ ha α l]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dif_pos i.2]
  · intro α hα a ha h0
    obtain ⟨i₀, hm⟩ := cover α
    have key : ∀ i, a i ≠ 0 → cls i = cls i₀ := fun i hi => hcls i₀ i α hm (ha i hi)
    have hl := (GlobalTheory.SecRatio.ratio_and_lin _ _ (Φ.H_isLB 1)).2 k Φ.G.hom {i // cls i = cls i₀}
      (fun i => R i α)
    obtain ⟨φ, hφ, -⟩ := hl (fun i => a i)
    obtain ⟨φ₀, hφ₀, -⟩ := hl 0
    have hz₀ : ∀ β l, Φ.wt φ₀ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ₀ β l]
      exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, constFn_zero, zero_mul]
    have hz : ∀ β l, Φ.wt φ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ β l]
      by_cases hβ : β = α
      · subst hβ
        rw [← hsum i₀ β a key l, h0 l]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have : Φ.wt (R i α) β l = 0 := by
          by_contra h
          exact hβ ((part i α).1 ⟨l, h⟩)
        rw [this, mul_zero]
    have e : φ = φ₀ := WtPart.sec_ext Φ φ φ₀ fun β l => (hz β l).trans (hz₀ β l).symm
    subst e
    have hu := (basis i₀ α hα hm φ (by rintro β ⟨l, hl⟩; exact absurd (hz β l) hl)).unique hφ hφ₀
    funext i
    by_contra h
    exact h (congrFun hu ⟨i, key i h⟩)

theorem residue_j_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) {a : u.V}
    (ha : a ∈ IsLocalRing.maximalIdeal u.V) : IsLocalRing.residue (OO p) (u.j a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) *
      (b : PadicAlgCl p) = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'
  have hn : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2
  obtain ⟨c, hc⟩ := (u.norm_le _).1 hn
  refine ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_))
  rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]

theorem good_reduction : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l N fb hN J _ σ cls f hB F hF
  have hsh := GlobalTheory.T.adaptedBasis_terms_at_other_class_members hL o Ω S ρ p y₀ u l N hN J σ cls f hB
  obtain ⟨hshort, huniq, hcover, -, -, hzero, -⟩ := hB
  have hS : ∀ α : fb.Φ.E.X, Short (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) N α ↔ Short l.q N (fb.xe α) := by
    intro α
    constructor
    · intro h m
      simpa using h (fb.xe.symm m)
    · intro h m
      simpa using h (fb.xe m)
  have hC : ∀ (α : fb.Φ.E.X) (c : u.D.toPre.X),
      (∃ m, α = fb.xe.symm c + N • m) ↔ ∃ m, fb.xe α = c + N • m := by
    intro α c
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨fb.xe m, by simp⟩
    · rintro ⟨m, hm⟩
      exact ⟨fb.xe.symm m, fb.xe.injective (by simp [hm])⟩
  refine good_of_parts fb.Φ N _ _ F (fun i α => fb.red (fb.xe α) (f i (fb.xe α))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact l.pos.comp fb.xe.injective.tendsto_cofinite
  · intro i
    rw [hS, fb.xe.apply_symm_apply]
    exact hshort i
  · intro i i' h
    rw [hC, fb.xe.apply_symm_apply] at h
    rw [huniq i i' h]
  · intro α
    obtain ⟨i, h⟩ := hcover (fb.xe α)
    exact ⟨i, (hC _ _).2 h⟩
  · intro i α
    have := hF i (fb.xe α)
    rwa [fb.xe.symm_apply_apply] at this
  · intro i α h j
    rw [hS, hC] at h
    by_cases hc : ∃ m, fb.xe α = cls i + N • m
    · obtain ⟨a, β, ha, hβ⟩ := (hsh i _ hc).2 fun hs => h ⟨hs, hc⟩
      have := fb.lin _ Unit (fun _ => β) (fun _ => a) (f i (fb.xe α)) (fun j => by
        rw [hβ j, Fintype.sum_unique])
      rw [wt_lin fb.Φ this α j, Fintype.sum_unique, residue_j_eq_zero u ha, constFn_zero, zero_mul]
    · have := fb.lin _ Empty Empty.elim Empty.elim (f i (fb.xe α)) (fun j => by
        rw [hzero i _ (fun m e => hc ⟨m, e⟩) j, Fintype.sum_empty])
      rw [wt_lin fb.Φ this α j, Fintype.sum_empty]
  · intro i₀ α hα hc φ hφ
    rw [hS] at hα
    rw [hC] at hc
    have hb := fb.basis _ _ _ ((hsh i₀ _ hc).1 hα) φ (by rwa [fb.xe.symm_apply_apply])
    let e : {i // cls i = cls i₀} ≃ {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} :=
      Equiv.subtypeEquivRight fun i => fb.xe.symm.injective.eq_iff.symm
    have hlin : ∀ a : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} → kb p,
        IsLin fb.Φ.G.hom (fun i : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} =>
          fb.red (fb.xe α) (f i (fb.xe α))) a φ ↔
        IsLin fb.Φ.G.hom (fun i : {i // cls i = cls i₀} => fb.red (fb.xe α) (f i (fb.xe α))) (a ∘ e) φ := by
      intro a
      refine forall_congr' fun j => ?_
      rw [← e.sum_comp]
      rfl
    obtain ⟨a, ha, hu⟩ := hb
    refine ⟨a ∘ e.symm, (hlin _).2 ?_, fun b hb => ?_⟩
    · have : (a ∘ e.symm) ∘ e = a := by
        funext i
        simp
      rw [this]
      exact ha
    · rw [← hu _ ((hlin b).1 hb)]
      funext i
      simp

end GlobalTheory.ZH.RedGood
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_adapted_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  atlas_forward_decl GlobalTheory.ZH.RedGood.good_reduction
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuations_torusExtension_points : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  first | exact @GlobalTheory.ZH.TorusVal.main | exact GlobalTheory.ZH.TorusVal.main | (intros; apply GlobalTheory.ZH.TorusVal.main <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.GtDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) : LB.Gen M := ⟨fun i => res le_top c * t.s i⟩

theorem gm_scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) (r : Z ⟶ X) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scaleGen t c).s i) = gm r z ⊤ c * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top h c) rfl)

theorem scaleGen_isGen {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (c : Γ(Y, ⊤)ˣ) : (scaleGen t c).IsGen :=
  isGen_of_gm _ fun y j j' hj hj' => by
    have e1 : gm (𝟙 Y) y (LB.wchart M φ j) ((scaleGen t c).s j) =
        gm (𝟙 Y) y ⊤ c * gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y le_top hj c) rfl)
    have e2 : gm (𝟙 Y) y (LB.wchart M φ j') ((scaleGen t c).s j') =
        gm (𝟙 Y) y ⊤ c * gm (𝟙 Y) y (LB.wchart M φ j') (t.s j') :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y le_top hj' c) rfl)
    rw [e1, e2, gen_trans ht (𝟙 Y) y hj hj']
    exact mul_left_comm _ _ _

theorem corr_of_inj {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hL : L.IsLB)
    (h : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {W : Scheme.{0}} (p : W ⟶ Y)
    (hi : Function.Injective p.appTop.hom) (hp : ∀ w J, Good L w J → val t p w J = val t' p w J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  obtain ⟨ρ, hρ⟩ := FormalPoint.exists_ratio hL h t t' ht ht'
  have h1 : p.appTop.hom ρ.val = 1 := FormalPoint.appTop_eq_one_of_gm p ρ fun w => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL w
    exact mul_eq_right.1 ((hρ W p w J hJ).symm.trans (hp w J hJ))
  have h2 : ρ = 1 := Units.ext (hi (h1.trans (map_one _).symm))
  exact corr_of_val hL fun y J hJ => by rw [hρ _ _ y J hJ, h2, map_one, _root_.one_mul]

theorem gm_transfer {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z) {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j)
    (hj' : r z ∈ LB.wchart L φ j')
    (h : gm r z (LB.wchart L φ j) (t.s j) = gm r' z (LB.wchart L φ' j) (t'.s j)) :
    gm r z (LB.wchart L φ j') (t.s j') = gm r' z (LB.wchart L φ' j') (t'.s j') := by
  have m : ∀ i : K → L.ι, r z ∈ LB.wchart L φ i → r' z ∈ LB.wchart L φ' i := fun i hi =>
    Set.mem_iInter.2 fun k => by
      have h1 : (r ≫ φ k) z ∈ L.U (i k) := Set.mem_iInter.1 hi k
      rw [hr k] at h1
      exact h1
  rw [gen_trans ht r z hj' hj, gen_trans ht' r' z (m _ hj') (m _ hj), h]
  simp only [trF, hr]

theorem mem_wchart_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z) {i : K → L.ι} (hi : r z ∈ LB.wchart L φ i) :
    r' z ∈ LB.wchart L φ' i :=
  Set.mem_iInter.2 fun k => by
    have h1 : (r ≫ φ k) z ∈ L.U (i k) := Set.mem_iInter.1 hi k
    rw [hr k] at h1
    exact h1

theorem valR_transfer {A : Type} [CommRing A] [IsLocalRing A] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Sp A ⟶ Y) (r' : Sp A ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (h : ∀ z J, Good L z J → val t r z J = val t' r' z J) {j : K → L.ι}
    (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    valR r (LB.wchart L φ j) (t.s j).val = valR r' (LB.wchart L φ' j) (t'.s j).val := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  have h1 := h _ J hJ
  rw [val_of t' r' _ J (fun k => J (r ≫ φ k)) (fun k => by rw [hr k])] at h1
  have hm := (top_le_iff_cpt r _).1 hj
  have h2 := gm_transfer ht ht' r r' hr (cpt A) (hJ.mem φ r) hm h1
  apply toStkA_injective
  exact (toStkA_valR r _ _ hj _).trans ((congrArg Units.val h2).trans
    (toStkA_valR r' _ _ ((top_le_iff_cpt r' _).2 (mem_wchart_of_eq r r' hr _ hm)) _).symm)

theorem valR_spMap_fn {A O : Type} [CommRing A] [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by
  have := (GlobalTheory.ZH.CrdCalc.valR_spMap β (𝟙 (Sp O)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)
  rw [Category.comp_id] at this
  rw [this, GlobalTheory.ZH.CrdCalc.valR_eq (𝟙 (Sp O)) ⊤ le_top]
  congr 1
  have h : (𝟙 (Sp O) : Sp O ⟶ Sp O).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
    (((𝟙 (Sp O) : Sp O ⟶ Sp O).appLE ⊤ ⊤ le_top).hom _) = a
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of O)).inv_hom_id_apply a

theorem exists_gen_extend {W F : Type} [CommRing W] [IsLocalRing W] [Field F] (hL : L.IsLB) (κ : W →+* F)
    {φ' : K → (Sp W ⟶ X)} {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} (hφ : ∀ k, spMap κ ≫ φ' k = φ k)
    (s : LB.Gen (LB.LinComb L φ ε)) (hs : s.IsGen) (j : K → L.ι) (hj : ⊤ ≤ LB.wchart L φ' j) (a : Wˣ)
    (ha : κ a = valR (𝟙 (Sp F)) (LB.wchart L φ j) (s.s j).val) :
    ∃ s' : LB.Gen (LB.LinComb L φ' ε), s'.IsGen ∧
      ∀ z J, Good L z J → val s' (spMap κ) z J = val s (𝟙 _) z J := by
  obtain ⟨t, ht⟩ := exists_gen_of_local L hL φ' ε
  let A : Γ(Sp W, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a
  let c : Γ(Sp W, ⊤)ˣ := res hj (t.s j)
  have hr : ∀ k, spMap κ ≫ φ' k = 𝟙 _ ≫ φ k := fun k => (hφ k).trans (Category.id_comp _).symm
  refine ⟨scaleGen t (A * c⁻¹), scaleGen_isGen t ht _, fun z J hJ => ?_⟩
  obtain rfl : z = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hm : spMap κ (cpt F) ∈ LB.wchart L φ' j := hj trivial
  rw [val_of s (𝟙 _) _ J (fun k => J (spMap κ ≫ φ' k)) (fun k => by rw [hr k])]
  refine gm_transfer (scaleGen_isGen t ht _) hs (spMap κ) (𝟙 _) hr _ hm (hJ.mem φ' _) ?_
  have e1 := gm_scaleGen (M := LB.LinComb L φ' ε) t (A * c⁻¹) (spMap κ) (cpt F) j hm
  have e2 : gm (spMap κ) (cpt F) ⊤ c = gm (spMap κ) (cpt F) (LB.wchart L φ' j) (t.s j) := gm_res _ _ hj trivial _
  refine e1.trans ?_
  rw [map_mul, map_inv, e2]
  refine (inv_mul_cancel_right _ _).trans (Units.ext ?_)
  exact (toStkA_valR (spMap κ) ⊤ (cpt F) le_top A).symm.trans ((congrArg _ ((valR_spMap_fn κ a).trans ha)).trans
    (toStkA_valR (𝟙 (Sp F)) _ (cpt F) ((top_le_iff_cpt _ _).2 (mem_wchart_of_eq _ _ hr _ hm)) (s.s j)))

theorem appTop_injective {W F : Type} [CommRing W] [CommRing F] (κ : W →+* F) (h : Function.Injective κ) :
    Function.Injective (spMap κ).appTop.hom := by
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ)
  intro a b hab
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((spMap κ).appTop.hom a) =
      κ ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) := fun a => congrArg (fun q => q.hom a) n
  have := (e a).symm.trans ((congrArg _ hab).trans (e b))
  exact (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective (h this)

end Gen

section Desc

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

theorem prod_gtT (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (cP D T χ * b).left)⁻¹ * h (cP D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  have := FormalPoint.prod_gtφT (𝟙 T) b χ h
  simpa only [Over.id_left, Category.id_comp] using this

theorem exists_descend (ρ : T' ⟶ T) (hi : Function.Injective ρ.left.appTop.hom) (ξ' : GtPt D T') (b : T ⟶ D.P.A)
    (hb : ρ ≫ b = ξ'.b) (S : Set D.X) (hS : AddSubmonoid.closure S = ⊤)
    (h : ∀ χ ∈ S, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε), s.IsGen ∧
      ∀ z J, Good D.P.L z J → val s ρ.left z J = val (ξ'.s χ) (𝟙 _) z J) :
    ∃ ξ : GtPt D T, ξ.b = b ∧ ∀ χ z J, Good D.P.L z J → val (ξ.s χ) ρ.left z J = val (ξ'.s χ) (𝟙 _) z J := by
  have one : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have F0 : FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim (DegPre.gtφT D T b 0) DegPre.gtε :=
    fun U _ h => by rw [prod_gtT, cPoint_zero, _root_.one_mul]; simp
  have cg : ∀ χ χ' : D.X, (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b).IsGen := fun χ χ' =>
    pullGen_isGen _ _ _ _ D.cub.isGen _
  have vm : ∀ χ χ' z J, Good D.P.L z J → val (ξ'.s (χ + χ')) (𝟙 _) z J *
      val (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b) ρ.left z J =
        val (ξ'.s χ) (𝟙 _) z J * val (ξ'.s χ') (𝟙 _) z J := fun χ χ' z J hJ => by
    have e := FormalPoint.val_s_add ξ' (𝟙 T') hJ χ χ'
    have e' := val_cub D.cub ρ hJ (cP D T χ) (cP D T χ') b
    rw [comp_cP, comp_cP, hb] at e'
    rw [Category.id_comp] at e
    exact (congrArg₂ (· * ·) rfl e').trans e
  have all : ∀ χ, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε), s.IsGen ∧
      ∀ z J, Good D.P.L z J → val s ρ.left z J = val (ξ'.s χ) (𝟙 _) z J := fun χ => by
    have hχ : χ ∈ AddSubmonoid.closure S := hS ▸ AddSubmonoid.mem_top χ
    induction hχ using AddSubmonoid.closure_induction with
    | mem χ hχ => exact h χ hχ
    | zero =>
      obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB F0 _ one
      exact ⟨s, hs, fun z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans
        ((val_corr hJ ξ'.s_zero _).trans (val_one _)).symm)⟩
    | add χ χ' _ _ h₁ h₂ =>
      obtain ⟨s₁, g₁, v₁⟩ := h₁
      obtain ⟨s₂, g₂, v₂⟩ := h₂
      obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T b (χ + χ')) (ε' := DegPre.gtε) (fun U _ h => by
          refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
            (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gtT b χ h) (prod_gtT b χ' h))
            (prod_neg _ _ (prod_cub (cP D _ χ) (cP D _ χ') b h))).trans ?_
          rw [prod_gtT, cPoint_add]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
        (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s₁ s₂)
          (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b)))
        (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) (invGen_isGen _ _ _ _ (cg χ χ')))
      refine ⟨s, hs, fun z J hJ => (hv _ _ z J hJ).trans ?_⟩
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        ((congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ)).trans (vm χ χ' z J hJ).symm)) (val_inv _ _))).trans ?_
      exact mul_inv_cancel_right _ _
  choose s hs hv using all
  refine ⟨⟨b, s, hs, corr_of_inj D.P.isLB F0 (hs 0) one ρ.left hi fun z J hJ => ?_,
    fun χ χ' => corr_of_inj D.P.isLB (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hs _) (cg χ χ'))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) ρ.left hi fun z J hJ => ?_⟩, rfl, hv⟩
  · exact (hv 0 z J hJ).trans (((val_corr hJ ξ'.s_zero _).trans (val_one _)).trans (val_one _).symm)
  · refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gtT b χ h) (prod_gtT b χ' h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gtT b (χ + χ') h)
        (prod_cub (cP D _ χ) (cP D _ χ') b h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · exact (val_mul hJ _ _ _).trans (((congrArg₂ (· * ·) (hv _ z J hJ) rfl).trans ((vm χ χ' z J hJ).trans
      (congrArg₂ (· * ·) (hv _ z J hJ) (hv _ z J hJ)).symm)).trans (val_mul hJ _ _ _).symm)

end Desc

section Pts

theorem exists_factor {V O : Type} [CommRing V] [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (j : V →+* O) (y : Sp O ⟶ X) (hy : y ≫ q = spMap j) :
    ∃ s : Finset O, ∀ (W : Type) [CommRing W] (f : V →+* W) (κ : W →+* O), Function.Injective κ → κ.comp f = j →
      (∀ x ∈ s, x ∈ κ.range) → ∃ y' : Sp W ⟶ X, y' ≫ q = spMap f ∧ spMap κ ≫ y' = y := by
  classical
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y (cpt O)) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact (top_le_iff_cpt y U).2 hz (Set.mem_univ x)
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U) ⟶ CommRingCat.of O, Spec.map φ ≫ hU.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of V ⟶ Γ(X, U), Spec.map ρ = hU.fromSpec ≫ q := ⟨_, Spec.map_preimage _⟩
  have hft : ρ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hρ]
    infer_instance
  have hj : ρ ≫ φ = CommRingCat.ofHom j := Spec.map_injective (by
    rw [Spec.map_comp, hρ, ← Category.assoc, hφ, hy])
  letI := ρ.hom.toAlgebra
  obtain ⟨s, hs⟩ := (hft : Algebra.FiniteType V Γ(X, U)).out
  refine ⟨s.image φ.hom, fun W _ f κ hκ hf hs' => ?_⟩
  have hmem : ∀ a, φ.hom a ∈ κ.range := by
    intro a
    have ha : a ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hs' _ (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact ⟨f r, (DFunLike.congr_fun hf r).trans (congrArg (fun q => q.hom r) hj).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let e : W ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b h => hκ (congrArg Subtype.val h), κ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* W := e.symm.toRingHom.comp (φ.hom.codRestrict κ.range hmem)
  have hψ : ∀ a, κ (ψ a) = φ.hom a := fun a => congrArg Subtype.val (e.apply_symm_apply ⟨_, hmem a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, ← Spec.map_comp]
    congr 1
    ext r
    exact hκ ((hψ _).trans ((congrArg (fun q => q.hom r) hj).trans (DFunLike.congr_fun hf r).symm))
  · rw [← hφ, ← Category.assoc]
    congr 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact hψ a

theorem isAdicComplete_of_ne {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] {I : Ideal W} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) : IsAdicComplete I W := by
  have hle : I ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  have he' : IsLocalRing.maximalIdeal W ^ e = I := by
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hm : ∀ n, I ^ n • (⊤ : Submodule W W) ≤ IsLocalRing.maximalIdeal W ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hle n)
  have : IsHausdorff I W := ⟨fun x hx => IsHausdorff.haus' (I := IsLocalRing.maximalIdeal W) x fun n => (hx n).mono (hm n)⟩
  have : IsPrecomplete I W := ⟨fun u hu => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal W) u fun {m n} hmn => (hu hmn).mono (hm m)
    refine ⟨L, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans ((hL _).mono (Submodule.smul_mono_left ?_))⟩
    rw [pow_mul, ← he']
    exact Ideal.pow_right_mono (Ideal.pow_le_pow_right e.le_succ) n⟩
  exact ⟨⟩

end Pts

end GlobalTheory.GtDescent
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.GtDescent

variable {p : ℕ} [Fact p.Prime]

theorem existsUnique_ext {X S : Scheme.{0}} (q : X ⟶ S) [hp : IsProper q] (c : Sp (OO p) ⟶ S)
    (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ q = gPt p ≫ c) : ∃! y : Sp (OO p) ⟶ X, y ≫ q = c ∧ gPt p ≫ y = x := by
  have hv : ValuativeCriterion q := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let Q : ValuativeCommSq q := { R := OO p, K := PadicAlgCl p, i₁ := x, i₂ := c, commSq := ⟨hx⟩ }
  obtain ⟨U⟩ := hv Q
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, fun ψ hψ => ?_⟩
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨ψ, hψ.2, hψ.1⟩)

theorem exists_ring {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (j : V →+* OO p) [IsLocalHom j]
    (hj : Function.Injective j) (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hK : ∀ x, (j x : PadicAlgCl p) ∈ K) (s : Finset (OO p)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : V →+* W) (κ : W →+* OO p), Function.Injective κ ∧
      IsLocalHom κ ∧ κ.comp f = j ∧ (∀ x ∈ s, x ∈ κ.range) ∧
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map f) W := by
  let K₁ := IntermediateField.adjoin ℚ_[p] ((s.image (OO p).subtype : Finset _) : Set (PadicAlgCl p))
  have : FiniteDimensional ℚ_[p] K₁ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ K₁
  have : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_sup K K₁
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[p] E) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] E
  have hf : Module.Finite ℤ_[p] (integralClosure ℤ_[p] E) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] E _
  have := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] E)
  let κ := integralClosureToPadicAlgClIntegers E
  have hl : IsLocalHom κ := isLocalHom_integralClosureToPadicAlgClIntegers E
  have hκ : Function.Injective κ := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : OO p => (z : PadicAlgCl p)) h))
  let f₁ : V →+* E := ((OO p).subtype.comp j).codRestrict E fun x => (le_sup_left : K ≤ E) (hK x)
  let f : V →+* integralClosure ℤ_[p] E := f₁.codRestrict (integralClosure ℤ_[p] E) fun x =>
    (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 (j x).2)
  have hc : κ.comp f = j := RingHom.ext fun x => rfl
  refine ⟨integralClosure ℤ_[p] E, inferInstance, inferInstance, f, κ, hκ, hl, hc, fun x hx => ?_,
    isAdicComplete_of_ne (fun h => ?_) (fun h => ?_)⟩
  · exact ⟨⟨⟨x, (le_sup_right : K₁ ≤ E) (IntermediateField.subset_adjoin _ _ (by simpa using hx))⟩,
      (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 x.2)⟩, rfl⟩
  · have hi : Function.Injective f := fun a b h => hj (by rw [← hc]; exact congrArg κ h)
    exact IsDiscreteValuationRing.not_a_field V ((Ideal.map_eq_bot_iff_of_injective hi).1 h)
  · have : (IsLocalRing.maximalIdeal V).map f ≤ IsLocalRing.maximalIdeal _ :=
      Ideal.map_le_iff_le_comap.2 fun x hx hu => hx (IsLocalHom.map_nonunit (f := j) x (hu.map κ))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_j : gPt p ≫ spMap u.j = (TF (R := u.V) (PadicAlgCl p)).hom := by
  change _ = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem exists_intGood : ∃ J, u.IntGood J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  have H : ∀ x : Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left, ∃ i, ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left,
      ψ ≫ u.D.toPre.P.A.hom = spMap u.j → gPt p ≫ ψ = x → ⊤ ≤ ψ ⁻¹ᵁ u.D.toPre.P.L.U i := fun x => by
    by_cases h : ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = x
    · obtain ⟨ψ, h₁, h₂⟩ := h
      obtain ⟨i, hi⟩ := exists_chart hL (ψ (cpt (OO p)))
      refine ⟨i, fun ψ' h₁' h₂' => ?_⟩
      obtain rfl : ψ' = ψ := (existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) x
        (by rw [← h₂, Category.assoc, h₁])).unique ⟨h₁', h₂'⟩ ⟨h₁, h₂⟩
      exact (top_le_iff_cpt _ _).2 hi
    · obtain ⟨i, -⟩ := exists_chart hL (x (cpt (PadicAlgCl p)))
      exact ⟨i, fun ψ h₁ h₂ => (h ⟨ψ, h₁, h₂⟩).elim⟩
  choose J hJ using H
  exact ⟨J, fun ψ h => hJ _ ψ h rfl⟩

theorem spMap_cpt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    spMap f (cpt B) = cpt A := IsLocalRing.comap_closedPoint f

theorem gtφT_over {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφT D T b χ k ≫ D.P.A.hom = T.hom := by
  fin_cases k <;> exact Over.w _

theorem exists_model (hl : IsLocalHom u.j) (hj : Function.Injective u.j) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (hK : ∀ x, (u.j x : PadicAlgCl p) ∈ K) (g : GtPtF u.D.toPre (PadicAlgCl p))
    (hg : u.GtN g 0) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : u.V →+* W) (κ : W →+* OO p),
      IsLocalHom κ ∧ κ.comp f = u.j ∧ IsAdicComplete ((IsLocalRing.maximalIdeal u.V).map f) W ∧
      ∃ ξ : GtPt u.D.toPre (Over.mk (spMap f)), spMap ((OO p).subtype.comp κ) ≫ ξ.b.left = g.b.left ∧
        ∀ χ z J, Good u.D.toPre.P.L z J →
          val (ξ.s χ) (spMap ((OO p).subtype.comp κ)) z J = val (g.s χ) (𝟙 _) z J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  obtain ⟨J, hJ⟩ := exists_intGood u
  obtain ⟨b₀, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) g.b.left
    ((Over.w g.b).trans (gPt_j u).symm)
  obtain ⟨s₀, hs₀⟩ := exists_factor u.D.toPre.P.A.hom u.j b₀ hb₁
  have : AddGroup.FG u.D.toPre.X := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨X₀, hX₀⟩ := (AddGroup.fg_iff_addMonoid_fg.1 this).fg_top
  have hv : ∀ χ, ‖valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ = 1 := fun χ => by
    rw [hg J hJ χ]; simp
  let v : u.D.toPre.X → OO p := fun χ => ⟨_, (mem_OO_iff _).2 (hv χ).le⟩
  have hu : ∀ χ, IsUnit (v χ) := fun χ => by
    by_contra h
    exact ((not_isUnit_OO_iff _).1 h).ne (hv χ)
  obtain ⟨W, _, _, f, κ, hκ, hκl, hc, hs, hW⟩ := exists_ring u.j hj K hK (s₀ ∪ X₀.image v)
  obtain ⟨b', hb₃, hb₄⟩ := hs₀ W f κ hκ hc fun x hx => hs x (Finset.mem_union_left _ hx)
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  let π : TF (R := u.V) (PadicAlgCl p) ⟶ Over.mk (spMap f) := Over.homMk (spMap ((OO p).subtype.comp κ)) (by
    rw [← gPt_j, ← ef, eκ]; exact Category.assoc _ _ _)
  let b : Over.mk (spMap f) ⟶ u.D.toPre.P.A := Over.homMk b' hb₃
  have hb : spMap ((OO p).subtype.comp κ) ≫ b' = g.b.left := by rw [eκ, Category.assoc, hb₄, hb₂]
  let ξ' : GtPt u.D.toPre (TF (R := u.V) (PadicAlgCl p)) := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  obtain ⟨ξ, h₁, h₂⟩ := exists_descend π (appTop_injective _ (Subtype.val_injective.comp hκ)) ξ' b
    (Over.OverMorphism.ext hb) X₀ hX₀ fun χ hχ => by
      obtain ⟨a, ha⟩ := hs (v χ) (Finset.mem_union_right _ (Finset.mem_image_of_mem v hχ))
      have hau : IsUnit a := IsLocalHom.map_nonunit (f := κ) a (ha ▸ hu χ)
      have hφ : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ b χ k =
          DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := fun k => by
        have := (TorusCoord.comp_eq_of_left b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
          (hb.trans (Category.id_comp _).symm)).1 χ k
        rw [Category.id_comp, ← TorusCoord.gtφT_eq] at this
        exact this
      refine exists_gen_extend hL ((OO p).subtype.comp κ) hφ (g.s χ) (g.isGen χ)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) ?_ hau.unit (congrArg Subtype.val ha)
      refine (top_le_iff_cpt (𝟙 (Sp W)) (LB.wchart u.D.toPre.P.L (DegPre.gtφT u.D.toPre _ b χ)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)))).2 ?_
      refine Set.mem_iInter.2 fun k => ?_
      have h3 := (top_le_iff_cpt _ _).1 (hJ (spMap κ ≫ DegPre.gtφT u.D.toPre _ b χ k)
        ((Category.assoc _ _ _).trans ((congrArg _ (gtφT_over b χ k)).trans ef)))
      rw [← Category.assoc, ← eκ, hφ k, Scheme.Hom.comp_apply, spMap_cpt] at h3
      exact h3
  exact ⟨W, inferInstance, inferInstance, f, κ, hκl, hc, hW, ξ, by rw [h₁]; exact hb, h₂⟩

theorem exists_integral_point : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u g hg
  obtain ⟨-, hl, hj, K, hK, hK'⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  obtain ⟨W, _, _, f, κ, hκ, hc, hW, ξ, h₁, h₂⟩ := exists_model u hl hj K (fun x => by
    rw [← SetLike.mem_coe, hK']; exact ⟨_, rfl⟩) g hg
  have hL := u.D.toPre.P.isLB
  obtain ⟨x, hx, -⟩ := FormalPoint.existsUnique_isPointOf u.U.toUnifPre ξ
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  refine ⟨spMap κ ≫ x.left, (Category.assoc _ _ _).trans ((congrArg _ (Over.w x)).trans ef),
    spMap κ ≫ ξ.b.left, by rw [← Category.assoc, ← eκ, h₁], fun e ce hce => ?_⟩
  obtain ⟨a₁, a₂⟩ := (FormalPoint.hasCoords_iff _ _ _ _ _).1
    (hx e _ (spMap (Ideal.Quotient.mk (u.lev e)) ≫ spMap κ) ce (hce.trans (Category.assoc _ _ _).symm))
  refine ⟨a₁.trans (Category.assoc _ _ _), fun χ jj hjj => ?_⟩
  have hne : u.lev e ≠ ⊤ := fun h => by
    have : u.lev e ≤ IsLocalRing.maximalIdeal _ := Ideal.map_le_iff_le_comap.2 fun x hx hu =>
      Ideal.pow_le_self e.succ_ne_zero hx (IsLocalHom.map_nonunit (f := u.j) x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))
  have : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (OO p ⧸ u.lev e) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (u.lev e)) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hφ := (TorusCoord.comp_eq_of_left ξ.b (u.U.gt e).pG _ ce a₁.symm).1 χ
  have hφ' : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ ξ.b χ k =
      𝟙 _ ≫ DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := fun k => by
    have := (TorusCoord.comp_eq_of_left ξ.b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
      (h₁.trans (Category.id_comp _).symm)).1 χ k
    rw [← TorusCoord.gtφT_eq] at this
    exact this
  have hm := mem_wchart_of_eq _ _ (fun k => (hφ k).symm) _ ((top_le_iff_cpt _ _).1 hjj)
  rw [Scheme.Hom.comp_apply, spMap_cpt] at hm
  have ht := (top_le_iff_cpt (spMap κ) _).2 hm
  obtain ⟨t₁, v₁⟩ := CrdCalc.valR_spMap (OO p).subtype (spMap κ) _ ht
  obtain ⟨t₂, v₂⟩ := CrdCalc.valR_spMap (Ideal.Quotient.mk (u.lev e)) (spMap κ) _ ht
  refine ⟨valR (spMap κ) _ ((ξ.s χ).s jj).val, (v₁ _).symm.trans ?_, (v₂ _).symm.trans ?_⟩
  · rw [← eκ] at t₁ ⊢
    exact valR_transfer hL (ξ.isGen χ) (g.isGen χ) _ (𝟙 _) hφ' (h₂ χ) t₁
  · exact valR_transfer hL (ξ.isGen χ) ((u.U.gt e).t_gen χ) _ ce hφ (fun z J hJ => (a₂ χ z J hJ).symm) t₂

end GlobalTheory.GtDescent
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  first | exact @GlobalTheory.GtDescent.exists_integral_point | exact GlobalTheory.GtDescent.exists_integral_point | (intros; apply GlobalTheory.GtDescent.exists_integral_point <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IotaShift
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (y : D.X) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen)
    (b : TF (R := R) F ⟶ D.P.A) (hb : b = g.b * cP D _ y) :
    ∃ ω : Frm D F k b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J =
      val w (𝟙 _) z J * val (g.s y) (𝟙 _) z J ^ k *
        (val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J *
          val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J) := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : jFK (R := R) F ≫ D.xK y = (cP D (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      have a₃ : ∏ i, h (DegPre.gtφ D F g.b y i) ^ ((k : ℤ) * DegPre.gtε i) =
          (∏ i, h (DegPre.gtφ D F g.b y i) ^ DegPre.gtε i) ^ (k : ℤ) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [a₃, prod_gt, prod_line, prod_line, hb, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (GeneratorPullback.powGen D.P.L _ _ (g.s y) k))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (powGen_isGen _ _ _ _ (g.isGen y) k))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen y) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _))
  refine ⟨u, hu, fun z J hJ => ?_⟩
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (map_pow _ _ _))) ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _))))

theorem coef_shift_frame (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) :
    ∃ ω : Frm D F k g'.b, ω.IsGen ∧ ∀ (s : Fam D F k) α, coef s g w (α + k • y) = coef s g' ω α := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  rw [ιb] at hb
  obtain ⟨ω, hω, vω⟩ := exists_frame y g w hw g'.b hb
  refine ⟨ω, hω, fun s α => coef_eq fun z J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k y α
  have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _
    (lift (𝟙 (TF (R := R) F)) g.b).left z J hJ
  have t : lift (𝟙 (TF (R := R) F)) g.b ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) g'.b := by
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
  rw [hv u hu hc _ _ z J hJ, ← Over.comp_left, t, val_famMult _ hJ, uVal, lift_fst_assoc, lift_fst, lift_snd,
    Category.id_comp, Over.id_left] at e₁
  have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g α y k
  rw [Category.id_comp, Over.id_left] at e₂
  have e₃ := hs α z J hJ
  have e₄ : th D z J (cP D _ α) g.b h.b = th D z J (cP D _ α) g.b (cP D _ y) := by rw [ιb]
  have e₅ : val (h.s α) (𝟙 _) z J = val (D.tau y α) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) z J := ιv α z J hJ
  rw [e₅, e₄] at e₃
  rw [isCoef_coef g' hω α s z J hJ, e₁, vω z J hJ]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
  linear_combination (norm := module) a₃ - a₂

theorem coef_shift (hG : GlobalFnsSt) {k : ℕ} {y : D.X} {g h g' : GtPtF D F} (hι : GtPtF.IsIota y h)
    (hadd : GtPtF.IsAdd g h g') (w : Frm D F k g.b) (hw : w.IsGen) (w' : Frm D F k g'.b) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (s : Fam D F k) α, coef s g' w' α = c * coef s g w (α + k • y) := by
  obtain ⟨ω, hω, e⟩ := coef_shift_frame hG hι hadd w hw
  obtain ⟨c, hc, -, e'⟩ := ((coef_basic R D F k g').2.2 ω hω).2.2.1 w' hw'
  exact ⟨c, hc, fun s α => by rw [e', e]⟩

end

theorem parAt_add_iota : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k a g h g' y _ hι hadd
  constructor
  · intro H w' hw' l hl
    obtain ⟨w, hw⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g).1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w hw l hl
    refine ⟨c * κ, mul_ne_zero hc hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc, funext (e s)]
    exact ((Equiv.addRight (k • y)).hasSum_iff.2 (hs σ s hσ)).mul_left c
  · intro H w hw l hl
    obtain ⟨w', hw'⟩ := (coef_basic u.V u.D.toPre (PadicAlgCl p) k g').1
    obtain ⟨c, hc, e⟩ := coef_shift hL.1.globalFns hι hadd w hw w' hw'
    obtain ⟨κ, hκ, hs⟩ := H w' hw' l hl
    refine ⟨c⁻¹ * κ, mul_ne_zero (inv_ne_zero hc) hκ, fun σ s hσ => ?_⟩
    rw [_root_.mul_assoc]
    refine (Equiv.addRight (k • y)).hasSum_iff.1 ?_
    have := (hs σ s hσ).mul_left c⁻¹
    simp only [e s, inv_mul_cancel_left₀ hc] at this
    exact this

end GlobalTheory.ZH.IotaShift
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesProportional_add_iota_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (a : u.PtC) (g h g' : GtPtF u.D.toPre (PadicAlgCl p)) (y : u.D.toPre.X), 1 ≤ k → GtPtF.IsIota y h → GtPtF.IsAdd g h g' → (u.ParAt k a g ↔ u.ParAt k a g') := by
  atlas_forward_decl GlobalTheory.ZH.IotaShift.parAt_add_iota
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ s : J → Fam u.D.toPre (PadicAlgCl p) k, (∀ i, FamOf u.D.toPre _ (f i) (s i)) → ∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), u.GtN g ν → w.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ α, (∀ i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m) ∧ (∀ i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α))) ∧ ∃ i, ‖GlobalTheory.UT.coef (s i) g w α‖ = κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := by
  first | exact @GlobalTheory.TermSize.term_sizes | exact GlobalTheory.TermSize.term_sizes | (intros; apply GlobalTheory.TermSize.term_sizes <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesAtPoint

section Pull
variable {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem secLin_of_secScal {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem exists_pull (hL : L.IsLB) {φ : K₁ → (Y ⟶ X)} {ε : K₁ → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ' : K₁ → (Y' ⟶ X)} (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s' φ ε s h 1 ∧
      ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y') (j : K₁ → L.ι), ⊤ ≤ (x ≫ h) ⁻¹ᵁ LB.wchart L φ j →
        valR x (LB.wchart L φ' j) (s'.f j) = valR (x ≫ h) (LB.wchart L φ j) (s.f j) := by
  subst e
  refine ⟨DVR.pullSec L φ ε s h, DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ (𝟙 _) y hJ).symm, fun R _ x j hj => ?_⟩
  have hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  refine (CrdCalc.valR_res x _ hj' _).trans ?_
  exact (CrdCalc.valR_eq x (h ⁻¹ᵁ LB.wchart L φ j) hj _).trans (CrdCalc.valR_eq (x ≫ h) _ hj (s.f j)).symm

theorem exists_isGen {R : Type} [CommRing R] [IsLocalRing R] {M : LB (Sp R)} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  have : (𝟙 (Sp R) : Sp R ⟶ Sp R) (IsLocalRing.closedPoint R) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  have hl' : ⊤ ≤ M.U l := (CrdCalc.top_le_iff (𝟙 (Sp R)) _).2 hl
  have le : ∀ V : (Sp R).Opens, V ≤ V ⊓ M.U l := fun V => le_inf le_rfl (le_top.trans hl')
  refine ⟨⟨fun j => res (le _) (M.g j l)⟩, fun i j => ?_⟩
  have e := congrArg (res (le (M.U i ⊓ M.U j))) (hM.cocycle i j l)
  rw [map_mul, DVR.res_res', DVR.res_res', DVR.res_res', DVR.res_refl'] at e
  simp only [DVR.res_res']
  exact e.symm

end Pull

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_frm (k : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) :
    ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen :=
  exists_isGen (R := PadicAlgCl p) (DVR.linComb_isLB _ u.D.toPre.P.isLB _ _)

theorem hasSum_crd {k : ℕ} {J : Type} {σ : J → (u.H k).Sec} {f : J → ∀ α, u.D.toPre.SecB k α}
    (hf : ∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) {s : J → Fam u.D.toPre (PadicAlgCl p) k}
    (hs : ∀ i, FamOf u.D.toPre _ (f i) (s i)) {a : u.PtC} {g : GtPtF u.D.toPre (PadicAlgCl p)} (hg : u.ParAt k a g)
    {w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b} (hw : w.IsGen) {v : J → PadicAlgCl p}
    (hv : Crd (u.H k) σ (u.toG a) v) :
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ i, HasSum (fun χ => GlobalTheory.UT.coef (s i) g w χ) (κ * v i) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  obtain ⟨l, rfl⟩ : ∃ l₀, l = fun _ : Fin 1 => l₀ := ⟨l 0, funext fun i => congrArg l (Subsingleton.elim _ _)⟩
  obtain ⟨κ, hκ, H⟩ := hg w hw l (hl.trans ((u.toG a).preimage_mono
    (LB.wchart_le u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l) 0)))
  refine ⟨κ * (c⁻¹).val, mul_ne_zero hκ (Units.ne_zero _), fun i => ?_⟩
  obtain ⟨σ', h₁, h₂⟩ := exists_pull u.U.LG.isLB (σ i) (UnifPre.gFK (G := u.G) (PadicAlgCl p))
    (φ' := fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (funext fun _ => (Category.comp_id _).symm)
  have e : (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd]
    rfl
  have hsum := H σ' (s i) ⟨1, fun _ => 1, fun _ => σ i, fun _ => f i, fun _ => hf i, secLin_of_secScal _ h₁,
    fun α => secLin_of_secScal _ (hs i α)⟩
  have h₃ := h₂ (PadicAlgCl p) (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left (fun _ => l) (e.symm ▸ hl)
  have h₄ := h₃.trans (congrArg (fun x => valR x (LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => l))
    ((σ i).f fun _ => l)) e)
  rw [hv, _root_.mul_assoc, Units.inv_mul_cancel_left]
  exact (congrArg (fun x => HasSum _ (κ * x)) h₄).mp hsum

theorem main : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB a ha w hw
  have hN : 4 ≤ S.N := (GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ u).2.2.2.1
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) hN
  obtain ⟨-, hsep, hon⟩ := GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB
  obtain ⟨a, rfl⟩ := hon a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_torusExtension_parameter_genericFibrePoint hL hT o Ω S ρ p y₀ u l a
  obtain ⟨-, hex, huq, hadd, hι⟩ := GlobalTheory.T.valuations_torusExtension_points hL o Ω S ρ p y₀ u l
  obtain ⟨ν, hν⟩ := hex g
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) S.N, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hB.2.2.2.2.1 i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D S.N s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  obtain ⟨fr, hfr⟩ := exists_frm u S.N g
  obtain ⟨κ, hκ, hsum⟩ := hasSum_crd u hB.2.2.2.1 hs hg hfr hw
  refine ⟨ν, ?_, ?_⟩
  · obtain ⟨r, hr, H⟩ := GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint hL o Ω S ρ p y₀ u l S.N hN S.J σ cls f hB s hs g ν fr hν hfr
    refine ⟨fun α i => κ⁻¹ * GlobalTheory.UT.coef (s i) g fr α, ‖κ⁻¹‖ * r,
      mul_pos (norm_pos_iff.2 (inv_ne_zero hκ)) hr, fun i => ?_, fun α i h => ?_, fun α => ⟨fun i => ?_, ?_⟩⟩
    · have := (hsum i).mul_left κ⁻¹
      rwa [inv_mul_cancel_left₀ hκ] at this
    · exact (H α).1 i (right_ne_zero_of_mul h)
    · rw [norm_mul, _root_.mul_assoc]
      exact mul_le_mul_of_nonneg_left ((H α).2.1 i) (norm_nonneg _)
    · obtain ⟨i, hi⟩ := (H α).2.2
      exact ⟨i, by rw [norm_mul, _root_.mul_assoc, hi]⟩
  · rintro ⟨m, hm⟩
    obtain ⟨-, hio, hsub⟩ := GlobalTheory.ZH.gt_add_iota_sub_exist hL o Ω S ρ p y₀ u
    obtain ⟨h, hh⟩ := hio m
    obtain ⟨g', hg'⟩ := hsub g h
    obtain ⟨ν', hν'⟩ := hex g'
    have e := huq g _ _ hν (hadd g' h g _ _ hg' hν' (hι m h hh))
    have e0 : (ν' : u.D.toPre.X → ℝ) = 0 := funext fun α => by
      have := congrFun e α
      rw [Pi.add_apply, hm α] at this
      exact right_eq_add.1 this
    obtain ⟨c, hc, hlev⟩ := GlobalTheory.T.exists_integralPoint_of_torusPoint_valuationZero hL o Ω S ρ p y₀ u g' (e0 ▸ hν')
    obtain ⟨a', ha'⟩ := hon (gPt p ≫ c) (by rw [Category.assoc, hc])
    have hp' : u.ParAt S.N a' g :=
      (GlobalTheory.T.seriesProportional_add_iota_iff hL o Ω S ρ p y₀ u S.N a' g' h g m hN1 hh hg').1
        ((GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g' a' hc ha'.symm hlev).2 S.N hN1)
    obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (DVR.linComb_isLB _ u.U.LG.isLB _ _) σ (u.toG a')
    obtain ⟨κ', hκ', hsum'⟩ := hasSum_crd u hB.2.2.2.1 hs hp' hfr hw'
    have h₁ := CrdCalc.crd_smul (Units.mk0 κ hκ) hw
    have h₂ := CrdCalc.crd_smul (Units.mk0 κ' hκ') hw'
    have e₃ : (fun j => ((Units.mk0 κ' hκ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w' j) =
        fun j => ((Units.mk0 κ hκ : (PadicAlgCl p)ˣ) : PadicAlgCl p) * w j :=
      funext fun j => (hsum' j).unique (hsum j)
    rw [e₃] at h₂
    exact ⟨c, hc, ha'.symm.trans (congrArg u.toG (hsep a' a _ h₂ h₁))⟩

end GlobalTheory.ZH.SeriesAtPoint
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_at_point_integral_of_period_valuation : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∀ w, Crd (u.H S.N) σ a w → ∃ ν : u.D.toPre.X →+ ℝ, Ser l.q S.N cls w ν ∧ ((∃ m, ∀ α, ν α = QuadraticMap.polar l.q m α) → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = a) := by
  atlas_forward_decl GlobalTheory.ZH.SeriesAtPoint.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem utest_nonempty_mod : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hb
  obtain ⟨-, hdim, hsm, h4, -⟩ := utest_dim_and_split hL o Ω S ρ p y₀ u
  have h1 : 1 ≤ S.N := le_trans (by norm_num) h4
  obtain ⟨fb⟩ := GlobalTheory.T.nonempty_geometric_special_fibre_uniformised hL o Ω S ρ p y₀ u S.N h1
  obtain ⟨F, hF, hred⟩ := fb.exp S.J σ f (fun i => hb.2.2.2.1 i 0)
  refine ⟨{ isLB := LB.isLB_linComb u.U.LG.isLB _ _
            smooth := hsm
            Φ := fb.Φ
            r := fb.r
            cart := fb.cart
            xe := fb.xe
            F := F
            good := GlobalTheory.T.good_reduction_adapted_basis hL o Ω S ρ p y₀ u l S.N fb h1 S.J σ cls f hb F hF
            pol := fb.pol
            dim := ?_
            red := hred
            ser := GlobalTheory.T.theta_series_at_point_integral_of_period_valuation hL hT o Ω S ρ p y₀ u l σ cls f hb }⟩
  rw [fb.dim, fb.xe.toIntLinearEquiv.finrank_eq]
  exact hdim

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_adaptedBasis_is_modelWithSeries : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  atlas_forward_decl GlobalTheory.ZH.utest_nonempty_mod
end
