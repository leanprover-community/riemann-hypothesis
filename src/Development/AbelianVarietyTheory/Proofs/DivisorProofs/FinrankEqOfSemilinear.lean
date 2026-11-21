import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily

section
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.ShareNumbers

theorem real_bounds (PP TO Dp k f m r nW : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hk : 1 ≤ k) (hD : 1 ≤ Dp) (hr : 1 ≤ r)
    (hPP : (2 * f * m) ^ 4 * nW ≤ PP) (hn40 : 40 ≤ nW) (hnk : k ≤ nW) (hnr : f * r ^ 2 ≤ nW)
    (hTO : PP ^ 4 * Dp ^ 3 * k * f / m ≤ TO) :
    54 * f * r ^ 4 ≤ TO ∧ 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ TO := by
  have hm0 : 0 < m := by linarith
  have hc : 16 ≤ (2 * f * m) ^ 4 := by
    have : 2 ≤ 2 * f * m := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
  have hfm : f * m ≤ (2 * f * m) ^ 4 := by
    have h1 : 1 ≤ 2 * f * m := by nlinarith
    calc f * m ≤ 2 * f * m := by nlinarith
      _ = (2 * f * m) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)
  have hn0 : 0 ≤ nW := by linarith
  have hP640 : 640 ≤ PP := by nlinarith
  have hPm : m * nW ≤ PP := by nlinarith
  have hPfk : f * k ≤ PP := by nlinarith
  have hPfr : f * r ^ 2 ≤ PP := by nlinarith
  have hP0 : 0 ≤ PP := by linarith

  have h4 : PP ^ 3 ≤ PP ^ 4 / m := by
    rw [le_div_iff₀ hm0]
    have : m ≤ PP := by nlinarith
    calc PP ^ 3 * m ≤ PP ^ 3 * PP := by gcongr
      _ = PP ^ 4 := by ring
  have hDkf : 1 ≤ Dp ^ 3 * k * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hk) hf
  have hT : PP ^ 3 * (Dp ^ 3 * k * f) ≤ TO := by
    calc PP ^ 3 * (Dp ^ 3 * k * f) ≤ PP ^ 4 / m * (Dp ^ 3 * k * f) := by gcongr
      _ = PP ^ 4 * Dp ^ 3 * k * f / m := by ring
      _ ≤ TO := hTO
  have hP3 : 0 ≤ PP ^ 3 := by positivity
  constructor
  · have e1 : 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP ^ 3 := by
      have a : 54 * (f * r ^ 2) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * r ^ 2 := by positivity
      calc 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 54 * f * r ^ 4 ≤ 54 * (f * r ^ 2) * (f * r ^ 2) := by
      have : 0 ≤ r ^ 4 := by positivity
      have hff : f ≤ f * f := by nlinarith
      calc 54 * f * r ^ 4 = 54 * r ^ 4 * f := by ring
        _ ≤ 54 * r ^ 4 * (f * f) := by gcongr
        _ = _ := by ring
    calc 54 * f * r ^ 4 ≤ PP ^ 3 := e2.trans e1
      _ = PP ^ 3 * 1 := (mul_one _).symm
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT
  · have e1 : 28 * (f * k) * (f * k) ≤ PP ^ 3 := by
      have a : 28 * (f * k) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * k := by positivity
      calc 28 * (f * k) * (f * k) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by
      have hfk : 0 ≤ (f * k) ^ 3 := by positivity
      have hD2 : Dp * (Dp + 6) ≤ 7 * Dp ^ 3 := by
        have h1 : Dp ≤ Dp ^ 2 := by nlinarith
        have h2 : Dp ^ 2 ≤ Dp ^ 3 := by nlinarith
        nlinarith
      calc 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 4 * (f * k) ^ 3 * (7 * Dp ^ 3) := by gcongr
        _ = 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by ring
    calc _ ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := e2
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT

open Formalism.BasicNotions in

theorem params_bounds {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (p0 : ℕ) (hp : p0 ≤ D.R.r) :
    2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T.TO ∧
      (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / (T.TO : ℝ) ≤
        1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)) := by
  have hf2 : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hDp : T.Dp = D.R.f * (D.R.r * (D.R.r - 1) / 2) := by rw [T.Dp_eq, Nat.choose_two_right]
  have hD1 : 1 ≤ T.Dp := by
    rw [T.Dp_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hnk : D.R.k ≤ T.nWn := by
    have h := T.nW_lo.2.1
    have h' : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnr : D.R.f * D.R.r ^ 2 ≤ T.nWn := by
    have h := T.nW_lo.1
    have h' : D.R.f * D.R.r * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    calc D.R.f * D.R.r ^ 2 = D.R.f * D.R.r * D.R.r := by ring
      _ ≤ _ := h'.trans h
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast hm1
  have hTO : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
    have hn : 0 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f := by
      have : 0 ≤ T.PP ^ 4 := by positivity
      positivity
    have hd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    have hdm : (D.R.m : ℝ) * L.de2 ≤ D.R.m := mul_le_of_le_one_right hm0.le L.thickDensity_le_one
    calc T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m
        ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / ((D.R.m : ℝ) * L.de2) := div_le_div_of_nonneg_left hn hd hdm
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hn hx1) hd.le
  obtain ⟨A, B⟩ := real_bounds T.PP T.TO T.Dp D.R.k D.R.f D.R.m D.R.r T.nWn (by exact_mod_cast hm1)
    (by exact_mod_cast (show 1 ≤ D.R.f by omega)) (by exact_mod_cast hk1) (by exact_mod_cast hD1)
    (by exact_mod_cast (show 1 ≤ D.R.r by omega)) T.PP_nW (by exact_mod_cast T.nW_40) (by exact_mod_cast hnk)
    (by exact_mod_cast hnr) hTO
  constructor
  · have hA : 54 * (D.R.f * D.R.r ^ 4) ≤ T.TO := by
      have : ((54 * (D.R.f * D.R.r ^ 4) : ℕ) : ℝ) ≤ T.TO := by push_cast; linarith
      exact_mod_cast this
    have h1 : p0 * (D.R.r - p0) ≤ D.R.r * D.R.r := Nat.mul_le_mul hp (Nat.sub_le _ _)
    have h2 : 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * (D.R.f * D.R.r ^ 4) := by
      calc 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r)) := by gcongr
        _ = 50 * (D.R.f * D.R.r ^ 4) := by ring
    have h3 : D.R.r ≤ D.R.r ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : 1 ≤ D.R.r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h5 : D.R.r ^ 4 ≤ D.R.f * D.R.r ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [← hDp]
    have hT0 : (0 : ℝ) < T.TO := by
      have : 1 ≤ T.TO := le_trans (by omega) T.TO_40
      exact_mod_cast this
    have hq : (0 : ℝ) < 4 * ((D.R.f : ℝ) * D.R.k) ^ 3 := by
      have : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
      have : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
      positivity
    rw [div_le_div_iff₀ hT0 hq]
    linarith

end GlobalTheory.ShareNumbers

open GlobalTheory.ShareNumbers in

theorem GlobalTheory.ShareNumbers.numbers_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι p0 hp => params_bounds (Fm.parT x hx ι) p0 hp⟩⟩⟩
end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) := by
  atlas_forward_decl GlobalTheory.ShareNumbers.numbers_along_family
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L] [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) → finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧ (⨅ i, LinearMap.ker (a' i) : Submodule L W) = Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_baseChange | exact GlobalTheory.BadCount.finrank_iInf_ker_baseChange | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_baseChange <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open Module

namespace GlobalTheory.ShareOn.Alg

theorem finrank_eig_eq {LL G W : Type} [Field LL] [Group G] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤)
    (ρV : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))) (ρ : Representation ℂ G W)
    (hρ : ∀ g v, ρ g (f v) = f (ρV g v)) (H : Subgroup G) [Finite H] (μ : H →* LLˣ) :
    finrank ℂ (GlobalTheory.BadCount.eig ρ H ((Units.map σ.toMonoidHom).comp μ)) =
      finrank LL (⨅ h : H, LinearMap.ker (ρV h - ((μ h : LLˣ) : LL) • LinearMap.id) : Submodule LL (Fin n → LL)) := by
  classical
  letI : Algebra LL ℂ := σ.toAlgebra
  letI : Module LL W := Module.compHom W σ
  haveI : IsScalarTower LL ℂ W := ⟨fun a b w => by
    show (σ a * b) • w = σ a • (b • w)
    rw [mul_smul]⟩
  have hsum : ∀ v : Fin n → LL, f v = ∑ k, σ (v k) • f (Pi.single k 1) := by
    intro v
    conv_lhs => rw [show v = ∑ k, v k • Pi.single k (1 : LL) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    rw [hsum v]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b : Basis (Fin n) ℂ W := Basis.mk hli hsp'
  let f' : (Fin n → LL) →ₗ[LL] W :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun a v => by
        show f (a • v) = σ a • f v
        rw [map_smulₛₗ] }
  have hf' : f' = Fintype.linearCombination LL b := by
    apply LinearMap.ext
    intro v
    rw [Fintype.linearCombination_apply]
    show f v = _
    rw [hsum v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Basis.mk_apply]
    rfl
  have hbc : IsBaseChange ℂ f' := hf' ▸ IsBaseChange.of_fintype_basis LL b
  have key := (GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family LL ℂ (Fin n → LL) W H f' hbc
    (fun h => ρV h - ((μ h : LLˣ) : LL) • LinearMap.id)
    (fun h => ρ h - ((σ (μ h : LLˣ)) : ℂ) • LinearMap.id) (fun h v => by
      show ρ h (f v) - σ ((μ h : LLˣ) : LL) • f v = f (ρV h v - ((μ h : LLˣ) : LL) • v)
      rw [map_sub, map_smulₛₗ, hρ])).1
  exact key

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn.Alg

theorem top_le_span_single {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hsp : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  classical
  rw [← hsp]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ∑ k, v k • Pi.single k (1 : LL) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  exact Submodule.sum_mem _ fun k _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_eq_of_semilinear {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤) : finrank ℂ W = n := by
  rw [finrank_eq_card_basis (Basis.mk hli (top_le_span_single σ f hsp)), Fintype.card_fin]

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem halfUnip_bot (p : PtAt ex Csz) : HalfUnip p ⊥ := by
  refine ⟨0, fun g hg v => ?_⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  intro a b
  simp only [map_one, Pi.one_apply, Units.val_one]
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by rw [h, Matrix.one_apply_eq]⟩

theorem shareW_of_modelAt (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hM : ModelAt p i T)
    (hH : HalfUnip p p.P.P0)
    (hs : ∀ p0 : ℕ, p0 ≤ D.R.r → 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T)
    (he : (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / T ≤ y)) :
    ShareW p i y := by
  obtain ⟨C, hC, _, M, ka, ρ, σ, f, hpull, hρ, hli, hsp, hlev, hcard, hcase⟩ := hM
  let H : Subgroup p.P.Gp := p.P.P0
  let μ : H →* D.what₂.LLˣ := ((p.R.toRealDat.FW i).chi.comp H.subtype) * (p.P.ψ0)⁻¹
  let lam : H →* ℂˣ := (Units.map σ.toMonoidHom).comp μ
  have hty : spType p.R.toRealDat p.F.lv2 i = ⨅ h : H, LinearMap.ker ((p.R.toRealDat.FW i).ρ h -
      ((μ h : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id) := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hdim : finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hty]
    exact Alg.finrank_eig_eq σ f hli hsp (p.R.toRealDat.FW i).ρ ρ hρ H μ
  have hn : finrank ℂ (M.cusp ka) = p.R.toRealDat.nW i := Alg.finrank_eq_of_semilinear σ f hli hsp
  have key : (1 - y) * (finrank ℂ (M.cusp ka) : ℝ) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
    rcases hcase with hdef | ⟨h0, hr, harch⟩
    · have hd := (GlobalTheory.T.definite_cuspForms_finite_regularRepresentation _ _ _ _ M hdef ka ρ hpull).2 H (hlev H hH)
      rw [← Nat.cast_mul, hd.2 lam]
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
    · have hsO : sOf M ≤ T := by
        have := hs M.p0 hr.le
        unfold sOf TwoLevels.dimX
        rw [hcard]
        exact this
      have hR := GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights _ _ _ _ M (hlev ⊥ (halfUnip_bot p)) h0 hr ka T harch hsO
      have hS := (GlobalTheory.T.twoLevelFlagDomain_eigenspace_share _ _ _ _ M ka ρ hpull _ _ hR H (hlev H hH) lam).2
      have hY : ((M.dimY : ℝ) * (M.dimY + 6) / T) ≤ y := by
        unfold TwoLevels.dimY
        rw [hcard]
        exact he
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
  unfold ShareW
  rw [← hdim, ← hn]
  exact key

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders

theorem shareWSt_of_modelSt : ModelSt → ShareWSt := by
  intro hM
  unfold ModelSt AtRuns AtPts at hM
  unfold ShareWSt AtRuns AtPts
  refine (hM.and GlobalTheory.T.shareSize_bounds_along_family).imp ?_
  intro eps Fm CH _ h
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  refine ⟨max x1 x2, fun x hx hle ι p hp hmore r hr hown i => ?_⟩
  have hm := h1 x hx ((le_max_left _ _).trans hle) ι p hp hmore r hr hown i
  have hn := h2 x hx ((le_max_right _ _).trans hle) ι
  exact shareW_of_modelAt p i _ _ (by positivity) hm (by obtain ⟨_, _, -, -, h⟩ := GlobalTheory.T.exists_whittaker_character_pair _ _ _ _ _ _ _ _ _ _ p hp; exact h)
    (fun p0 h0 => (hn p0 h0).1) (hn 0 (Nat.zero_le _)).2

end GlobalTheory.ShareOn
end
end
