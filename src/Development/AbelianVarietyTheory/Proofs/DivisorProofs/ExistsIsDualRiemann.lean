import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.RiemIndep

section Frames

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L N : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem ex_add_mem (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

open PullHermitian in

theorem herm_eq_zero (hN : N.IsLB) (h0 : cls N hN = 0) (u : HolUnif A N g) (B : Matrix (Fin g) (Fin g) ℂ)
    (c : u.Λ → ℂ) (hB : B.IsHermitian) (hc : ∀ l, ‖c l‖ = 1)
    (hf : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i → u.fr i z =
      c l * Complex.exp (Real.pi * hermForm B z l + Real.pi / 2 * hermForm B l l) * u.fr i (z + l)) : B = 0 := by
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hN).1 h0
  obtain ⟨r, hr, hrφ⟩ := exists_glue (fun i : N.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i})
    (fun i => (u.hol _ 0).1) (fun z => exists_chart (u.ex z).left hN)
    (fun i z => valAt' (u.ex z).left _ (t.s i).val / u.fr i z)
    (fun i => by
      simp only [div_eq_mul_inv]
      exact (u.hol _ (t.s i).val).2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have hij := inf_of _ hi hj
      have e := congrArg (unitVal _ hij) (ht i j)
      have e' : unitVal _ hi (t.s i) = unitVal _ hij (N.g i j) * unitVal _ hj (t.s j) :=
        (unitVal_res _ inf_le_left hij hi _).symm.trans (e.trans ((map_mul _ _ _).trans
          (congrArg (_ * ·) (unitVal_res _ inf_le_right hij hj _))))
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), u.fr_compat i j z hij, valAt'_eq_unitVal _ hi,
        valAt'_eq_unitVal _ hj, valAt'_eq_unitVal _ hij, e', Units.val_mul]
      ring)
  haveI := u.discrete
  refine (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full B c r hB hc hr (fun z => ?_) fun l z => ?_).1
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    rw [hrφ i z hi, valAt'_eq_unitVal _ hi]
    exact div_ne_zero (Units.ne_zero _) (u.fr_ne _ _ hi)
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ N.U i := by rwa [ex_add_mem]
    have h1 := u.fr_ne _ _ hi
    have h2 := u.fr_ne _ _ hi'
    rw [hrφ i z hi, hrφ i (z + l) hi', ex_add_mem, div_eq_iff h2, mul_right_comm, ← hf l i z hi]
    field_simp

variable (u : HolUnif A L g) (u' : HolUnif A' L' g) (ψ : A ⟶ A') (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))

theorem covers (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) (k : Fin 3) (z : Fin g → ℂ) :
    u'.ex (![T + T, T, 0] k z) = u.ex z ≫ ![ψ * ψ, ψ, 1] k := by
  fin_cases k
  · change u'.ex (T z + T z) = u.ex z ≫ (ψ * ψ)
    rw [u'.ex_add, hT, MonObj.comp_mul]
  · exact hT z
  · change u'.ex 0 = u.ex z ≫ 1
    rw [MonObj.comp_one]
    exact (u'.ker 0).2 (zero_mem _)

abbrev diagLB (L' : LB A'.left) (ψ : A ⟶ A') : LB A.left :=
  LB.LinComb L' (fun k => (![ψ * ψ, ψ, 1] k).left) ![1, -2, 1]

theorem cls_diagLB (hL' : L'.IsLB) (h : (diagLB L' ψ).IsLB) : cls _ h = lam (cls L' hL') ψ ψ := by
  refine (CechPic.cls_linComb hL' _ _ h).trans ?_
  rw [Fin.sum_univ_three, lam]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem factor_diag (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) {H : Matrix (Fin g) (Fin g) ℂ} {χ : u'.Λ → ℂ}
    (hA : u'.IsAH H χ) (l : u.Λ) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (diagLB L' ψ).U i →
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i z =
        c * Complex.exp (Real.pi * (2 * hermForm H (T z) (T l)) + Real.pi / 2 * (2 * hermForm H (T l) (T l))) *
          (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i (z + l) := by
  have hl : T l ∈ u'.Λ := by
    rw [← u'.ker, hT, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hT, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hχ := hA.2.2.1
  refine ⟨χ ⟨T l + T l, add_mem hl hl⟩ / χ ⟨T l, hl⟩ ^ 2, by simp [hχ], fun i z hz => ?_⟩
  have hc : ∀ k, ⊤ ≤ (u'.ex (![T + T, T, 0] k z)).left ⁻¹ᵁ L'.U (i k) := fun k => by
    rw [covers u u' ψ T hT]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' _ i).1 hz k
  have h0 := hA.2.2.2 ⟨T l + T l, add_mem hl hl⟩ (i 0) (T z + T z) (hc 0)
  have h1 := hA.2.2.2 ⟨T l, hl⟩ (i 1) (T z) (hc 1)
  have h4 : χ ⟨T l, hl⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
  change ∏ k, u'.fr (i k) (![T + T, T, 0] k z) ^ (![1, -2, 1] k : ℤ) =
    _ * ∏ k, u'.fr (i k) (![T + T, T, 0] k (z + l)) ^ (![1, -2, 1] k : ℤ)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply,
    LinearMap.zero_apply, map_add, zpow_one, zpow_neg, zpow_ofNat]
  rw [h0, h1, add_zero]
  simp only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  generalize (T z ⬝ᵥ H.mulVec (star (T l))) = a
  generalize (T l ⬝ᵥ H.mulVec (star (T l))) = b
  have e : Complex.exp (Real.pi * (a + a + (a + a)) + Real.pi / 2 * (b + b + (b + b))) =
      Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) * Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
  rw [e]
  generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
  simp only [mul_pow, mul_inv]
  field_simp

open PullHermitian in

theorem hermForm_eq_of_lam (hL : L.IsLB) (hL' : L'.IsLB) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (hA : u.IsAH H χ) (hA' : u'.IsAH H' χ')
    (h : lam (cls L' hL') ψ ψ = lam (cls L hL) (𝟙 A) (𝟙 A)) (z w : Fin g → ℂ) :
    hermForm H' (T z) (T w) = hermForm H z w := by
  have hI : ∀ z, u.ex (LinearMap.id (R := ℂ) z) = u.ex z ≫ 𝟙 A := fun z => (Category.comp_id _).symm
  choose c hc hf using factor_diag u u (𝟙 A) LinearMap.id hI hA
  choose c' hc' hf' using factor_diag u u' ψ T hT hA'
  have d : (diagLB L (𝟙 A)).IsLB := LB.isLB_linComb hL _ _
  have d' : (diagLB L' ψ).IsLB := LB.isLB_linComb hL' _ _
  set H₂ := (LinearMap.toMatrix' T).transpose * H' * (LinearMap.toMatrix' T).transpose.conjTranspose with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hA'.1
  have hs : ∀ z w, hermForm ((2 : ℂ) • H₂ - (2 : ℂ) • H) z w = 2 * hermForm H' (T z) (T w) - 2 * hermForm H z w :=
    fun z w => by rw [hermForm_sub_smul, hH₂, hermForm_pull]
  have key := herm_eq_zero (LB.isLB_div d' d)
    (by rw [CechPic.cls_div d' d, cls_diagLB ψ hL', cls_diagLB _ hL, h, sub_self])
    (SameFactor.divUnif (linCombUnif u u _ _ ![1, -2, 1] (covers u u _ _ hI))
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)) rfl)
    ((2 : ℂ) • H₂ - (2 : ℂ) • H) (fun l => c' l / c l)
    ((hH₂h.smul (by simp [IsSelfAdjoint])).sub (hA.1.smul (by simp [IsSelfAdjoint])))
    (fun l => (norm_div _ _).trans ((congrArg₂ (· / ·) (hc' l) (hc l)).trans (div_one _))) fun l i z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e1 := hf' l i.1 z h1
      have e2 := hf l i.2 z h2
      refine (congrArg₂ (fun a b => a * b⁻¹) e1 e2).trans ?_
      rw [hs, hs]
      change _ = _ * (_ * _⁻¹)
      rw [mul_sub, mul_sub, sub_add_sub_comm, Complex.exp_sub]
      simp only [LinearMap.id_apply, mul_inv, div_eq_mul_inv]
      ring
  have := hs z w
  rw [key] at this
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

end Frames

theorem exists_lin (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y) :
    ∃ T : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), (∀ z, (d'.u.ex (T z)).left ≫ d'.φ = (d.u.ex z).left ≫ d.φ) ∧
      ∀ z w, hermForm d'.H (T z) (T w) = hermForm d.H z w := by
  obtain ⟨ψ, e⟩ := SharpPull.exists_lift d.isPull d'.isPull (𝟙 P.A)
  have hψ := SharpPull.isMonHom_lift d.isPull d'.isPull e
  have hψφ : ψ.left ≫ d'.φ = d.φ := e.trans (Category.comp_id _)
  have hA := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d'.isPull
  obtain ⟨t₁, t₂⟩ := TorusTransfer.tangent_bijective d'.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d'.isPull.1 P.smoothDim)
  obtain ⟨T, hT, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d'.B hA hA' d.L d'.L P.g P.g d.u d'.u t₁ t₂ ψ hψ
  refine ⟨T, fun z => ?_, hermForm_eq_of_lam d.u d'.u ψ T d.isLB d'.isLB hT d.isAH d'.isAH ?_⟩
  · rw [hT, Over.comp_left, Category.assoc, hψφ]
  have k (b : P.RiemannData y) (x : d.B ⟶ b.B) : lam (cls b.L b.isLB) x x =
      CechPic.pull ((lift x x).left ≫ sqMap b.isPull.1.w) P.c := by
    rw [CechPic.pull_comp, b.pol, CechPic.pull_lam, lift_fst, lift_snd]
  have k₁ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.fst _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_fst x x))
  have k₂ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.snd _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_snd _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_snd x x))
  have k₃ : ψ.left ≫ d'.φ = (𝟙 d.B : d.B ⟶ d.B).left ≫ d.φ := hψφ.trans (Category.id_comp _).symm
  rw [k, k]
  congr 2
  exact pullback.hom_ext ((k₁ _ _).trans (k₃.trans (k₁ _ _).symm)) ((k₂ _ _).trans (k₃.trans (k₂ _ _).symm))

open Matrix HermFrame in

theorem riemann_dual_form_indep : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
    (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
    HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
      HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f') := by
  intro S P y d d' W f f' hW
  obtain ⟨T, hT, hH⟩ := RiemIndep.exists_lin S P y d d'
  set M := LinearMap.toMatrix' T with hM
  have hMv : ∀ z, M *ᵥ z = T z := fun z => LinearMap.toMatrix'_mulVec T z
  have hchg : d.H = chg M d'.H := by
    ext a b
    rw [← form_single (chg M d'.H), form_chg, hMv, hMv]
    exact (form_single d.H a b).symm.trans (hH _ _).symm
  have hinj : Function.Injective M.mulVec := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun v hv => ?_
    by_contra hne
    have h1 := (posDef_iff.1 d.posDef).2 v hne
    rw [hchg, form_chg] at h1
    have h0 : M *ᵥ v = 0 := hv
    rw [h0] at h1
    simp [form] at h1
  have hU : IsUnit M := mulVec_injective_iff_isUnit.1 hinj
  have hMN : M * M⁻¹ = 1 := mul_nonsing_inv M ((isUnit_iff_isUnit_det M).1 hU)
  have hfn : ∀ g : Γ(P.A.left, W), d.fn W g = d'.fn W g ∘ T := fun g => by
    funext z
    simp only [PPAS.RiemannData.fn, Function.comp_apply, hT]
  have hTd : ∀ v, fderiv ℂ (⇑T) 0 v = T v := fun v => by
    have := (LinearMap.toContinuousLinearMap T).fderiv (x := 0)
    exact congrArg (fun L => L v) this
  have hcov : ∀ g : Γ(P.A.left, W), d.cov W g = Mᵀ *ᵥ d'.cov W g := fun g => by
    funext a
    have hd := d'.differentiableAt_fn g hW
    have hd' : DifferentiableAt ℂ (d'.fn W g) (T 0) := by rw [map_zero]; exact hd
    have hTdiff : DifferentiableAt ℂ (⇑T) 0 := (LinearMap.toContinuousLinearMap T).differentiableAt
    simp only [PPAS.RiemannData.cov]
    rw [hfn, fderiv_comp 0 hd' hTdiff, ContinuousLinearMap.comp_apply, hTd, map_zero, ← hMv,
      mulVec_single_one]
    change _ = ∑ b, M.col a b * fderiv ℂ (d'.fn W g) 0 (Pi.single b 1)
    generalize fderiv ℂ (d'.fn W g) 0 = L
    conv_lhs => rw [pi_eq_sum_univ (M.col a)]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hchg, dualGram_chg hMN, form_chg, hcov, hcov, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hMN,
    transpose_one, one_mulVec, one_mulVec]

end GlobalTheory.RiemIndep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Filter Topology GlobalTheory.Points
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.LieVB (omega unitSec dUnit)

namespace GlobalTheory.CovFactor

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)
  {W W' : P.A.left.Opens} {U : S.Opens}

theorem eventually_le (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) :
    ∀ᶠ z in 𝓝 (0 : Fin P.g → ℂ), ⊤ ≤ ((d.u.ex z).left ≫ d.φ) ⁻¹ᵁ W := by
  rw [← d.ex_zero] at h
  exact (d.u.hol (d.φ ⁻¹ᵁ W) 0).1.mem_nhds h

theorem cov_res (k : W' ≤ W) (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W') (f : Γ(P.A.left, W)) :
    d.cov W' (resG _ k f) = d.cov W f := by
  have : d.fn W' (resG _ k f) =ᶠ[𝓝 0] d.fn W f :=
    (eventually_le d h).mono fun z hz => valR_res _ k hz f
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq]

theorem cov_add (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (f g : Γ(P.A.left, W)) :
    d.cov W (f + g) = d.cov W f + d.cov W g := by
  have : d.fn W (f + g) =ᶠ[𝓝 0] d.fn W f + d.fn W g :=
    (eventually_le d h).mono fun z hz => by
      simp only [PPAS.RiemannData.fn, Pi.add_apply, valR_eq _ _ hz, map_add]
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq,
    fderiv_add (d.differentiableAt_fn f h) (d.differentiableAt_fn g h), Pi.add_apply,
    ContinuousLinearMap.add_apply]

theorem cov_mul (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (f g : Γ(P.A.left, W)) :
    d.cov W (f * g) = valR (y ≫ unitSec P.A) W f • d.cov W g +
      valR (y ≫ unitSec P.A) W g • d.cov W f := by
  have : d.fn W (f * g) =ᶠ[𝓝 0] d.fn W f * d.fn W g :=
    (eventually_le d h).mono fun z hz => by
      simp only [PPAS.RiemannData.fn, Pi.mul_apply, valR_eq _ _ hz, map_mul]
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq,
    fderiv_mul (d.differentiableAt_fn f h) (d.differentiableAt_fn g h), Pi.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, ← d.ex_zero]
  rfl

theorem valR_appLE {X Y : Scheme.{0}} {x : Sp ℂ ⟶ X} {π : X ⟶ Y} {W : X.Opens} {U : Y.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(Y, U)) :
    valR x W (π.appLE U W k a) = valR (x ≫ π) U a := by
  have h' : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U := h.trans (x.preimage_mono k)
  rw [valR, valR, dif_pos h, dif_pos h']
  exact congrArg _ (Conormal.appLE_appLE rfl k h h' a)

theorem cov_base (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (k : W ≤ P.A.hom ⁻¹ᵁ U) (a : Γ(S, U)) :
    d.cov W (P.A.hom.appLE U W k a) = 0 := by
  have : d.fn W (P.A.hom.appLE U W k a) =ᶠ[𝓝 0] fun _ => valR y U a :=
    (eventually_le d h).mono fun z hz => by
      refine (valR_appLE hz k a).trans ?_
      rw [Category.assoc, d.isPull.1.w, ← Category.assoc, Over.w (d.u.ex z)]
      exact congrArg (valR · U a) (Category.id_comp y)
  funext b
  simp [PPAS.RiemannData.cov, this.fderiv_eq]

theorem exists_factor (c : Conormal.IsChart P.A.hom (unitSec P.A) U W) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ L : Γ(omega P.A, U) →+ (Fin P.g → ℂ), (∀ (r : Γ(S, U)) s, L (r • s) = valR y U r • L s) ∧
      ∀ f, L (dUnit P.A c.le f) = d.cov W f := by
  have he := LieVB.sec_hom (MonObj.one (X := P.A))
  have h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W := hy.trans (y.preimage_mono c.le)
  letI := c.algebra
  letI : Module Γ(S, U) (Fin P.g → ℂ) := Module.compHom _ (valMap y U hy).hom
  have sm (r : Γ(S, U)) (v : Fin P.g → ℂ) : r • v = valR y U r • v := by
    rw [valR_eq _ _ hy]; rfl
  have au (f : Γ(P.A.left, W)) : valR y U (c.aug he f) = valR (y ≫ unitSec P.A) W f :=
    valR_appLE hy c.le f
  let D : Γ(P.A.left, W) →ₗ[Γ(S, U)] (Fin P.g → ℂ) :=
    { toFun := d.cov W
      map_add' := cov_add d h
      map_smul' := fun r f => by
        refine (cov_mul d h (P.A.hom.appLE U W c.le_base r) f).trans ?_
        rw [cov_base d h, smul_zero, add_zero, RingHom.id_apply, sm, valR_appLE h, Category.assoc,
          he, Category.comp_id] }
  let l := AugCot.lift (c.aug he) D (fun f g => by
    rw [sm, sm, au, au]; exact cov_mul d h f g) ∘ₗ (c.augCotEquiv he).symm.toLinearMap
  refine ⟨l.toAddMonoidHom, fun r s => (l.map_smul r s).trans (sm _ _), fun f => ?_⟩
  refine (congrArg l (c.augCotEquiv_d he f).symm).trans ?_
  simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact AugCot.lift_d _ _ _ _

theorem exists_cov_eq_mulVec (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g)
    (hc : y ∈ ptsIn p σ c.U) : ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens)
      (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)),
      y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y) := by
  have he := LieVB.sec_hom (MonObj.one (X := P.A))
  obtain ⟨U₀, W₀, hx₀, hle₀, c₀⟩ := Conormal.exists_isChart he (mem_ptsIn.1 hc)
  choose t ht using fun a => c₀.d_surjective he (resM (omega P.A) hle₀ (c.e a))
  refine ⟨Matrix.of fun a b => d.cov W₀ (t b) a, fun U W hU f hy => ?_⟩
  have hx := mem_ptsIn.1 hy
  obtain ⟨W₂, hW₂, hx₂, k₂⟩ := QCoh.exists_affine_mem_le (U := W ⊓ W₀) _ ⟨hU hx, c₀.le hx₀⟩
  obtain ⟨U₁, hx₁, h₁, h₂, c₁⟩ := Conormal.exists_isChart_inf he c₀.affine_base hW₂
    ((k₂.trans inf_le_right).trans c₀.le_base) hx₂ hx
  have hy₁ : y ∈ ptsIn p σ U₁ := mem_ptsIn.2 hx₁
  obtain ⟨L, hL, hd⟩ := exists_factor d c₁ hy₁
  have ho : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ (W₂ ⊓ P.A.hom ⁻¹ᵁ U₁) :=
    le_trans (show ⊤ ≤ y.1 ⁻¹ᵁ U₁ from hy₁) (y.1.preimage_mono c₁.le)
  have kW : W₂ ⊓ P.A.hom ⁻¹ᵁ U₁ ≤ W := inf_le_left.trans (k₂.trans inf_le_left)
  have kW₀ : W₂ ⊓ P.A.hom ⁻¹ᵁ U₁ ≤ W₀ := inf_le_left.trans (k₂.trans inf_le_right)
  have e (b : Fin P.g) : L (c.isFrame.basis (h₂.trans hle₀) b) = d.cov W₀ (t b) := by
    rw [← cov_res d kW₀ ho, ← hd, LieVB.dUnit_resG, IsFrame.basis_apply,
      ← LieVB.resM_dUnit P.A c₀.le h₂, ← resM_resM (h₁ := hle₀) (h₂ := h₂), ← ht]
    rfl
  rw [← cov_res d kW ho, ← hd, LieVB.dUnit_resG, ← LieVB.resM_dUnit P.A hU h₁,
    ← (c.isFrame.basis (h₂.trans hle₀)).sum_repr (resM _ h₁ _), map_sum]
  funext a
  simp only [hL, e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, of_apply,
    c.crd_eq _ h₁ (h₂.trans hle₀) hy₁]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

end GlobalTheory.CovFactor
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Points

namespace GlobalTheory.UnifImmersive

theorem primeSpectrum_eq (x x' : PrimeSpectrum (DualNumber ℂ)) : x = x' := by
  have H (p : PrimeSpectrum (DualNumber ℂ)) : Ideal.span {DualNumber.eps} = p.asIdeal :=
    DualNumber.isMaximal_span_singleton_eps.eq_of_le p.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).2 (p.isPrime.mem_of_pow_mem 2 (by simp [sq])))
  exact PrimeSpectrum.ext ((H x).symm.trans (H x'))

theorem le_preimage_of_fst {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t) ⁻¹ᵁ U) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro x _
  have hx := h (x := IsLocalRing.closedPoint ℂ) trivial
  have e : x = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) :=
    primeSpectrum_eq _ _
  rw [e]
  exact hx

theorem eq_const {X : Scheme.{0}} (t : Sp (DualNumber ℂ) ⟶ X) (o : Sp ℂ ⟶ X)
    (ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = o)
    (H : ∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ o ⁻¹ᵁ U → TrivSqZeroExt.snd (valR t U f) = 0) :
    t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ o := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := o (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  have h₀ : ⊤ ≤ o ⁻¹ᵁ U := fun z _ => by
    rwa [show z = IsLocalRing.closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  have h₁ : ⊤ ≤ t ⁻¹ᵁ U := le_preimage_of_fst t U (ho ▸ h₀)
  refine ext_of_valR hU h₁ (le_preimage_comp _ o h₀ le_top) fun f => ?_
  rw [valR_spMap_comp _ o U h₀, ← ho, valR_spMap_comp _ t U h₁]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, H U f h₀]

theorem eq_zero_of_cov : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y),
    ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧
      (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) →
    ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)),
      ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0 := by
  intro S P y d ⟨h₁, h₂⟩ w hw
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
  let t : Sp (DualNumber ℂ) ⟶ d.B.left := v.left
  have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t = LieVB.unitSec d.B := hv
  have hb : t ≫ d.B.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  have hu : LieVB.unitSec d.B ≫ d.φ = y ≫ LieVB.unitSec P.A := LieVB.unitSec_comp d.isPull
  have ho : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t ≫ d.φ = y ≫ LieVB.unitSec P.A := by
    rw [← Category.assoc, ht, hu]
  have e₁ := eq_const (t ≫ d.φ) _ ho fun W f hW => by
    have hW' : ⊤ ≤ t ⁻¹ᵁ d.φ ⁻¹ᵁ W := le_preimage_of_fst (t ≫ d.φ) W (ho ▸ hW)
    rw [valR_comp, valR_eq _ _ hW']
    refine (hd (d.φ ⁻¹ᵁ W) hW' (d.φ.app W f)).trans (Eq.trans ?_ (hw W f hW))
    have e : (fun z => valAt' (d.u.ex z).left (d.φ ⁻¹ᵁ W) (d.φ.app W f)) = d.fn W f :=
      funext fun z => (valR_comp _ _ _ _).symm
    rw [e]
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Pi.single a (w a) : Fin P.g → ℂ) = w a • Pi.single a 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    rfl
  have e₂ : t = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ LieVB.unitSec d.B := by
    refine d.isPull.1.hom_ext ?_ ?_
    · rw [e₁, Category.assoc, hu]
    · rw [hb, Category.assoc, LieVB.sec_hom, Category.comp_id]
  refine (h₁ v hv).unique hd fun U h f => ?_
  have h₀ : ⊤ ≤ LieVB.unitSec d.B ⁻¹ᵁ U := ht ▸ le_preimage_comp _ t h le_top
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd (valR_eq t U h f)).symm.trans ?_
  rw [e₂, valR_spMap_comp _ _ U h₀]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.UnifImmersive
end
end

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open GlobalTheory.ArchMetricCompare (cj cjPt_comp val_cj)
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} (w : φ ≫ A.hom = A'.hom ≫ f)
    (w' : ψ ≫ A'.hom = A''.hom ≫ g) (w'' : (ψ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) :
    sqMap w'' = sqMap w' ≫ sqMap w :=
  (pullback.map_comp ψ φ ψ φ g f w'.symm w'.symm w.symm w.symm).symm

namespace PPAS.RiemannData

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

def conj : P.RiemannData (spMap (starRingEnd ℂ) ≫ y) :=
  have h := isGrpPullback_pullback d.B cj
  have hL := pull_isLB d.isLB (pullback.fst d.B.hom cj)
  { B := (Over.pullback cj).obj d.B
    φ := pullback.fst d.B.hom cj ≫ d.φ
    isPull := h.comp d.isPull
    L := d.L.pull (pullback.fst d.B.hom cj)
    isLB := hL
    pol := by
      rw [sqMap_comp d.isPull.1.w h.1.w, CechPic.pull_comp, d.pol]
      exact (pull_sqMap_lam h _).trans
        (congrArg (CechPic.lam · _ _) (CechPic.cls_pull d.isLB _ hL).symm)
    u := ConjUnif.conjPull h d.u
    H := d.H.map star
    χ := _
    isAH := ConjUnif.conjPull_isAH h d.u d.isAH }

theorem conj_H : d.conj.H = d.H.map star := rfl

theorem conj_fn (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (z : Fin P.g → ℂ) :
    d.conj.fn W f z = star (d.fn W f (star z)) := by
  have e : (d.conj.u.ex z).left ≫ d.conj.φ = cj ≫ (show Sp ℂ ⟶ _ from (d.u.ex (star z)).left) ≫ d.φ :=
    ArchMetricCompare.cjPt_comp' (isGrpPullback_pullback d.B cj) _
  unfold fn
  rw [← Points.valAt'_eq_valR, ← Points.valAt'_eq_valR]
  exact (congrArg (valAt' · W f) e).trans (val_cj _ _ _)

theorem conj_cov (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (h : ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W) :
    d.conj.cov W f = star (d.cov W f) := by
  have D := (d.differentiableAt_fn f h).hasFDerivAt.star_star
  rw [star_zero] at D
  have e : d.conj.fn W f = star ∘ d.fn W f ∘ star := funext (d.conj_fn W f)
  funext a
  unfold cov
  rw [e, D.fderiv]
  simp

end PPAS.RiemannData

theorem PPAS.exists_conj_riemannData : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f) :=
  fun _ _ _ d => ⟨d.conj, d.conj_H, d.conj_cov⟩

end GlobalTheory
end
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.Twist (resM)
open GlobalTheory.LieVB (omega unitSec dUnit)
open scoped ComplexOrder

namespace GlobalTheory.DualRiemannEx

theorem form_dualGram_smul {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosDef)
    {t : ℝ} (ht : 0 < t) (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H)) u v = (t : ℂ)⁻¹ * form (dualGram H) u v := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e : ((t : ℂ) • H)⁻¹ = (t : ℂ)⁻¹ • H⁻¹ :=
    inv_eq_right_inv (by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ ht', mul_nonsing_inv _ hH.det_pos.ne'.isUnit, one_smul])
  rw [dualGram, dualGram, e, transpose_smul, form_smul]

theorem form_dualGram_conj {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (t : ℝ)
    (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H.map star)) (star u) (star v) =
      star (form (dualGram ((t : ℂ) • H)) u v) := by
  have e : (t : ℂ) • H.map star = ((t : ℂ) • H).map star := by
    ext a b
    simp
  rw [e, dualGram_map_star]
  simp [form_eq_sum]

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem top_le_of_mem {U : X.Opens} {y : CxPts p σ} (h : y ∈ ptsIn p σ U) : ⊤ ≤ y.1 ⁻¹ᵁ U := by
  intro z _
  rw [mem_ptsIn] at h
  rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]

theorem exists_isUnit
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1)
    (c : Chart (omega P.A) P.g) (hc : y ∈ ptsIn p σ c.U) :
    ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ c.crd p σ (dUnit P.A hU f) y := by
  obtain ⟨C, hC⟩ := hc₁ k X p σ P y d c hc
  refine ⟨C, ?_, hC⟩
  rw [← vecMul_injective_iff_isUnit]
  intro u v e
  have e₀ : (u - v) ᵥ* C = 0 := by rw [sub_vecMul]; exact sub_eq_zero.2 e
  refine sub_eq_zero.1 (hc₃ X P y.1 d (hc₂ X P y.1 d) _ fun W f hW => ?_)
  have hy : y ∈ ptsIn p σ (unitSec P.A ⁻¹ᵁ W) := mem_ptsIn.2 (hW (show _ ∈ ⊤ from trivial))
  rw [hC _ W le_rfl f hy, dotProduct_comm, dotProduct_mulVec, e₀, zero_dotProduct]

end GlobalTheory.DualRiemannEx

namespace GlobalTheory
open GlobalTheory.DualRiemannEx

theorem PPAS.exists_isDualRiemann_of
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (hc₄ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f))
    (hex₀ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S), Nonempty (P.RiemannData y))
    (hind : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
      (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
        HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
          HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f')) :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (P : PPAS X) (t : ℝ), 0 < t →
    ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h := by
  intro k _ X p P t ht
  have hE := P.isVB_omega
  have hex : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (d : P.RiemannData y.1)
      (C : Matrix (Fin P.g) (Fin P.g) ℂ), IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ (hE.pick y).crd p σ (dUnit P.A hU f) y := fun σ y => by
    obtain ⟨d⟩ := hex₀ X P y.1
    obtain ⟨C, h₁, h₂⟩ := exists_isUnit hc₁ hc₂ hc₃ P y d (hE.pick y) (hE.mem_pick y)
    exact ⟨d, C, h₁, h₂⟩
  choose D C hCu hC using hex
  have htc : (0 : ℂ) < (t : ℂ) := by exact_mod_cast ht
  let m (σ : k →+* ℂ) : Met p σ (omega P.A) P.g :=
    Met.ofPt hE (fun y => hE.pick y) (fun y => hE.mem_pick y)
      (fun y => chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)))
      (fun y => posDef_chg (hCu σ y) (posDef_dualGram ((D σ y).posDef.smul htc)))
  have hindep (σ : k →+* ℂ) (y : CxPts p σ) (d d' : P.RiemannData y.1) (W : P.A.left.Opens)
      (f f' : Γ(P.A.left, W)) (hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W) :
      form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') =
        form (dualGram ((t : ℂ) • d'.H)) (d'.cov W f) (d'.cov W f') := by
    rw [form_dualGram_smul d.posDef ht, form_dualGram_smul d'.posDef ht,
      hind X P y.1 d d' W f f' hW]
  have hform (σ : k →+* ℂ) (y : CxPts p σ) (d : P.RiemannData y.1) (U : X.Opens)
      (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W))
      (hy : y ∈ ptsIn p σ U) :
      (m σ).form (dUnit P.A hU f) (dUnit P.A hU f') y =
        form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') := by
    have hG : (m σ).G (hE.pick y) y = chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)) := by
      change chg ((hE.pick y).tr p σ (hE.pick y) y) _ = _
      rw [Chart.tr_self _ (hE.mem_pick y), chg_one]
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => hU (mem_ptsIn.1 hy) |> fun h => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact h
    rw [(m σ).form_eq (hE.pick y) (hE.mem_pick y) _ _ hy, hG, form_chg, ← hC σ y U W hU f hy,
      ← hC σ y U W hU f' hy]
    exact hindep σ y _ d W f f' hW
  have hconj (σ σ' : k →+* ℂ) : (m σ).IsConj (m σ') := Met.isConj_of_exists fun y y' e => by
    obtain ⟨d', hH, hcov⟩ : ∃ d' : P.RiemannData y'.1, d'.H = (D σ y).H.map star ∧
        ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W →
          d'.cov W f = star ((D σ y).cov W f) := by
      rw [e]
      exact hc₄ X P y.1 (D σ y)
    refine ⟨hE.pick y, hE.mem_pick y, Matrix.ext fun a b => ?_⟩
    have hc := hE.mem_pick y
    obtain ⟨U', W, hx, hle, cc⟩ := Conormal.exists_isChart
      (LieVB.sec_hom (MonObj.one (X := P.A))) (mem_ptsIn.1 hc)
    have hy : y ∈ ptsIn p σ U' := mem_ptsIn.2 hx
    have hy' : y' ∈ ptsIn p σ' U' := (mem_ptsIn_iff_of_conj e).2 hy
    choose f hf using fun a => cc.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
      (resM (omega P.A) hle ((hE.pick y).e a))
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact cc.le (mem_ptsIn.1 hy)
    have e₁ : (m σ).G (hE.pick y) y a b = form (dualGram ((t : ℂ) • (D σ y).H))
        ((D σ y).cov W (f a)) ((D σ y).cov W (f b)) := by
      rw [← (m σ).form_frame _ hc, ← Met.form_resM _ _ _ hle hy, ← hf a, ← hf b]
      exact hform σ y _ U' W cc.le _ _ hy
    have e₂ : (m σ').G (hE.pick y) y' a b = form (dualGram ((t : ℂ) • d'.H))
        (d'.cov W (f a)) (d'.cov W (f b)) := by
      rw [← (m σ').form_frame _ ((mem_ptsIn_iff_of_conj e).2 hc), ← Met.form_resM _ _ _ hle hy',
        ← hf a, ← hf b]
      exact hform σ' y' _ U' W cc.le _ _ hy'
    rw [e₂, map_apply, e₁, hH, hcov _ _ hW, hcov _ _ hW, form_dualGram_conj]
  exact ⟨⟨hE, m, hconj⟩, fun σ y => ⟨⟨D σ y⟩, fun d U W hU f f' hy => hform σ y d U W hU f f' hy⟩⟩

end GlobalTheory
end
end

section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem PPAS.exists_isDualRiemann : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (P : PPAS X) (t : ℝ), 0 < t → ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h :=
  PPAS.exists_isDualRiemann_of GlobalTheory.CovFactor.exists_cov_eq_mulVec GlobalTheory.UnifTangent.riemannData_tangent GlobalTheory.UnifImmersive.eq_zero_of_cov GlobalTheory.PPAS.exists_conj_riemannData
    GlobalTheory.RiemannExists.nonempty_riemannData GlobalTheory.RiemIndep.riemann_dual_form_indep

end GlobalTheory
end
