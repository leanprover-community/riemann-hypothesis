import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G2Assumption
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BasicDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltAddRadial
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullEquiv

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo.Cs

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private noncomputable def lam0 (g : GA E a) : ℝ :=
  Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)

private theorem deg_pos (ha : 1 ≤ a) : (0 : ℝ) < a * Module.finrank ℚ E :=
  mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)

private theorem central_log_mul (g h : GA E a) : lam0 (g * h) = lam0 g + lam0 h := by
  unfold lam0
  rw [map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']
  rfl

private theorem central_split_mul_retract (ha : 1 ≤ a) (g : GA E a) :
    splitCentre E a (lam0 g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  have e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g) := by
    rw [KernelIndexFullLattice.splitEq_holds E a]
    refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
    change Real.exp _ = _
    rw [lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]

private theorem central_log_eq_zero_on_norm_one (x : KernelIndexFullLattice.G1 E a) : lam0 (x.1 : GA E a) = 0 := by
  rw [lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]
  simp

private theorem central_log_split (ha : 1 ≤ a) (t : ℝ) : lam0 (splitCentre E a t) = t := by
  rw [lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]
  change Real.log (Real.exp _) / _ = _
  rw [Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.lamEx :
    LamEx := by
  intro E _ _ _ a ha
  refine ⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩
  obtain ⟨T, hT⟩ := (UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c
  refine ⟨T, fun h hh => ?_⟩
  obtain ⟨t, ht, e⟩ := hT 1 h hh.1 hh.2
  have e' := congrArg lam0 e
  rw [central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero] at e'
  rwa [e']
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have comp : ∀ (g h : GL (Fin a) (Cinf E)) (v : HV E a), sand g (sand h v) = sand (g * h) v := fun g h v => by
    rw [map_mul]; rfl
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← comp, ← e, comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

end

theorem UpperTheory.V.Lit.Geo.Cs.descEx :
    DescEx := by
  classical
  intro E _ _ _ a U f Y C c f₀ hf
  refine ⟨fun s p => if h : p ∈ cone E a then f (pt h.choose s.out) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dif_pos hp, hk, pt_mul, hf.f_cpt, hu, pt, pt, map_mul (finGL E a), ← mul_assoc, hf.f_lev _ u.2]
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem rat_pt (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    pt (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * pt g x := by
  unfold pt
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.descFun :
    DescFun := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS Φ hΦ
  refine ⟨fun s p₀ hp₀ => ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨φ, hφ, -⟩ := hS.f_sm
    have h0 := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at h0
    have h1 := Complex.reCLM.contDiff.contDiffAt.comp p₀ h0
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hΦ (τ p) x
    rw [hp] at this
    rw [this, pt, infGL_comm]
    simp
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hS.f_left γ.1 0 (pt g x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hΦ, hΦ, rat_pt, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hS.f_left 1 t (pt g x)
    rw [map_one, one_mul, ← hc, pt, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hΦ, hΦ]
    exact hl
end
end

section
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem eig_prod (c : ℂ) (φ : Sm E a) (h : lie E a (oneL E a) φ = c • φ) (l : List (Lie E a)) :
    lie E a (oneL E a) ((l.map (lie E a)).prod φ) = c • (l.map (lie E a)).prod φ := by
  induction l with
  | nil => simpa using h
  | cons X l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, one_comm, ih, map_smul]

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (j : Fin d) (T : Module.End ℂ W)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : Bor.cmp j (T.rTensor _ m) = T (Bor.cmp j m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => rw [LinearMap.rTensor_tmul, cmp_tmul, cmp_tmul, map_smul]

private theorem cmp_prod (Ξ : AlgRep E a) (j : Fin Ξ.d) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (l : List (Lie E a)) :
    Bor.cmp j ((l.map (smA Ξ)).prod m) = (l.map (lie E a)).prod (Bor.cmp j m) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, smA_apply, cmp_rTensor, ih, List.map_cons, List.prod_cons,
      Module.End.mul_apply]

private theorem ev_eq {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy]

end

theorem UpperTheory.V.Lit.Geo.Cs.rapidEig :
    RapidEig := by
  intro E _ _ _ a U Ξ r hr q α hα X j l
  refine ⟨eig_prod _ _ ?_ l, fun g => by rw [ev_eq, cmp_prod]⟩
  have h : Bor.cmp j (α X) ∈ LinearMap.eqLocus (lie E a (oneL E a)) (-(r : ℂ) • LinearMap.id) :=
    mem_tens.1 (span_le_tens (fun φ hφ => hφ.2.2 _ hr) (hα.val X)) j
  exact h
end

section
open UpperTheory.V.Lit.Geo.Cs

private theorem le_div_one_add_pow_succ_of_mul_le {x K Q A C F : ℝ} {N : ℕ} (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hN : A * C ≤ N)
    (hF : F ≤ C * (1 + Real.log Q)) (hx : 0 ≤ x) (h : x * Q ^ N ≤ K) :
    x ≤ K * Real.exp (A * C) * Real.exp (-(A * F)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hl : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hp : Q ^ N = Real.exp (N * Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  have h1 : A * F - A * C ≤ N * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hF hA
    have := mul_le_mul_of_nonneg_right hN hl
    nlinarith
  have h2 : x * Real.exp (A * F - A * C) ≤ K := by
    refine le_trans ?_ h
    rw [hp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hx
  have h3 : x = x * Real.exp (A * F - A * C) * (Real.exp (A * C) * Real.exp (-(A * F))) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, show A * F - A * C + (A * C + -(A * F)) = 0 by ring,
      Real.exp_zero, mul_one]
  rw [h3, mul_assoc K]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.V.Lit.Geo.Cs.rapidAll :
    RapidAll := by
  intro E _ _ _ a U Ξ f lam C hlam hf q α hα hR
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.Bor.oneReal E a Ξ
  obtain ⟨hq1, hq2, -⟩ := UpperTheory.V.Lit.Geo.qhtFacts E a
  refine ⟨|r|, abs_nonneg r, fun A hA X j l => ?_⟩
  obtain ⟨he, hv⟩ := UpperTheory.V.Lit.Geo.Cs.rapidEig E a U Ξ r hr q α hα X j l
  obtain ⟨K, hK⟩ := hR l X ⌈A * C⌉₊
  refine ⟨K * Real.exp (A * C), fun g => ?_⟩
  obtain ⟨g₁, hs⟩ : ∃ g₁ : KernelIndexFullLattice.G1 E a, splitCentre E a (lam g) * g₁.1 = g := ⟨_, hlam.split g⟩
  have hK' := hK g₁
  have hq : qht g = qht (E := E) (a := a) g₁.1 := by
    have := hq2 1 (lam g) g₁.1
    rw [map_one, one_mul, hs] at this
    exact this
  have ha := UpperTheory.V.Lit.Bor.aInv E a _ _ he (lam g) g₁.1
  rw [hs] at ha
  rw [← hq] at hK'
  have hb := le_div_one_add_pow_succ_of_mul_le (hq1 g) hA (Nat.le_ceil (A * C)) (hf g) (norm_nonneg _)
    (le_trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ j) (pow_nonneg (zero_le_one.trans (hq1 g)) _)) hK')
  have hb' : ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g₁.1‖ ≤
      K * Real.exp (A * C) * Real.exp (-(A * f g)) := by
    rw [← hv]
    exact hb
  have hc : ‖Complex.exp (-(r : ℂ) * (lam g : ℂ))‖ ≤ Real.exp (|r| * |lam g|) := by
    rw [Complex.norm_exp, Real.exp_le_exp, ← abs_mul]
    simpa using neg_le_abs (r * lam g)
  rw [ha, norm_mul, sub_eq_add_neg, Real.exp_add, mul_left_comm]
  exact mul_le_mul hc hb' (norm_nonneg _) (Real.exp_pos _).le
end

section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.pbSz :
    PbSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hAcd, C2, hC2⟩ := altSz V F q k (1 + c)
  obtain ⟨C1, hC1, hcomp1⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k (1 + c)
  obtain ⟨C3, hC3, hcomp3⟩ := compSz V (V →L[ℝ] V)
    ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  refine ⟨2 ^ k * (C3 * max C2 0) * C1, by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flowSz V k c W t p ht hW hWs
  have hg := hcomp1 w (UpperTheory.V.Lit.Geo.flow W t) p b hF1 hw
    (fun i h1 h2 => hF4 i h1 (by omega)) hws
  have hL : ‖fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    simpa using hF3 0 (Nat.zero_le _)
  have hA : Sz k _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p) (max C2 0) :=
    fun i hi => (hC2 _ hL i hi).trans (le_max_left _ _)
  have hf := hcomp3 _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t)) p (max C2 0) hF2
    hAcd.contDiffAt (fun i h1 h2 => hF3 i h2) hA
  have hprod := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).1 _ _ _ _
    (hAcd.contDiffAt.comp p hF2) (hw.comp p hF1) hf hg
  have e : 2 ^ k * (C3 * max C2 0) * C1 * b = 2 ^ k * (C3 * max C2 0) * (C1 * b) := by ring
  rw [e]
  exact hprod
end

section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
end

section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
end

section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem parametric_integral_deriv_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : V)
    (O : Set (V × ℝ)) (hO : IsOpen O) (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) (b : ℝ) (i : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Φ : V × ℝ → F), ContDiffOn ℝ ∞ Φ O →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (fun x => Φ (x, t)) p‖ ≤ b) →
      ‖iteratedFDeriv ℝ i (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p‖ ≤ b := by
  induction i with
  | zero =>
    intro F _ _ _ Φ _ h
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := b) (f := fun t => Φ (p, t))
      (fun t ht => h t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht))
    simpa using this
  | succ i ih =>
    intro F _ _ _ Φ hΦ h
    let Ψ : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ)
    have hΨ : ContDiffOn ℝ ∞ Ψ O :=
      (hΦ.fderiv_of_isOpen hO (by simp)).clm_comp contDiffOn_const
    have hd : ∀ x t, (x, t) ∈ O → fderiv ℝ (fun y => Φ (y, t)) x = Ψ (x, t) := fun x t hx => by
      have h1 : DifferentiableAt ℝ Φ (x, t) := (hΦ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
      exact (h1.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    have htube : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Icc (0 : ℝ) 1, (x, t) ∈ O :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => hO.mem_nhds (hp t ht)
    have e : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) =ᶠ[𝓝 p] fun x => ∫ t in (0 : ℝ)..1, Ψ (x, t) := by
      filter_upwards [htube] with x hx
      rw [(UpperTheory.V.Lit.Dr.paramDeriv V F x O Φ hO hx hΦ).2.fderiv]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hd x t (hx t ht)
    rw [← norm_iteratedFDeriv_fderiv, (e.iteratedFDeriv ℝ i).eq_of_nhds]
    refine ih _ Ψ hΨ fun t ht => ?_
    have e' : fderiv ℝ (fun y => Φ (y, t)) =ᶠ[𝓝 p] fun x => Ψ (x, t) := by
      filter_upwards [htube] with x hx using hd x t (hx t ht)
    rw [← (e'.iteratedFDeriv ℝ i).eq_of_nhds, norm_iteratedFDeriv_fderiv]
    exact h t ht

theorem UpperTheory.V.Lit.Geo.Cs.intSz :
    IntSz := by
  intro V F _ _ _ _ _ _ k p O Φ b hO hp hΦ h i hi
  exact parametric_integral_deriv_bound V p O hO hp b i F Φ hΦ fun t ht => h t ht i hi
end

section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
end

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
end

section
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr Filter Topology

theorem UpperTheory.V.Lit.Geo.Cs.locBd :
    LocBd := by
  intro E _ _ a p₀ hp
  obtain ⟨τ, h1, h2⟩ := locSec E a p₀ hp
  have c1 : ContinuousAt (fun p => toL (τ p).val) p₀ := h1.continuousAt
  have c1' : ContinuousAt (fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := c1
  have hi : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (τ p₀).val := by
    apply continuousAt_matrix_inv
    have := NormedRing.inverse_continuousAt (GeneralLinearGroup.det (τ p₀))
    simpa using this
  have c2' : ContinuousAt (fun p => (((τ p)⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := by
    have := ContinuousAt.comp (f := fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) hi c1'
    simpa only [Matrix.coe_units_inv, Function.comp_def] using this
  have c2 : ContinuousAt (fun p => toL ((τ p)⁻¹).val) p₀ := c2'
  refine ⟨max (‖toL (τ p₀).val‖ + 1) (‖toL ((τ p₀)⁻¹).val‖ + 1), ?_⟩
  filter_upwards [h2, c1.norm.eventually_lt_const (lt_add_one _), c2.norm.eventually_lt_const (lt_add_one _)]
    with p e b1 b2
  exact ⟨τ p, ⟨b1.le.trans (le_max_left _ _), b2.le.trans (le_max_right _ _)⟩, e⟩
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
end
end

section
open UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.Cs.geoRet :
    GeoRet := by
  intro Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h
  have hB := fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1
  have hA := fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)
  have hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y := fun s => (hB s).1
  have hv := fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp
  have hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p =
      pull (l s) (extDeriv (z.1 s)) p := fun s p hp => by
    rw [G.dOm_apply _ s hp, ← (hB s).2 p hp]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy
  refine ⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_,
    fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]
      rfl
    · rw [((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]
  · rw [hv s p hp]
    exact (hA s q _).1 p hp v i hi
  · rw [hd s p hp]
    exact (hA s (q + 1) _).1 p hp v i hi
  · have hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0 := fun x hx => by
      rw [← G.dOm_apply w s hx, hw]
      rfl
    have hH := homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl
    have hpos := (hl.1 s).2.1 p hp
    have hm := hc _ hpos p hp
    rw [hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]
    unfold pull
    rw [← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]
end

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.supp :
    UpperTheory.V.Lit.Geo.Cs.Supp := by
  intro E _ _ _ a U Ξ f Y C c f₀ hs Φ hΦ q α w R hc hw
  refine ⟨Real.exp (|C| * (1 + |R|)), fun X g hg => ?_⟩
  have hf : R < f g := by
    by_contra hle
    have hle' : f g ≤ R := not_lt.1 hle
    have h1 : |C| * (1 + |R|) < Real.log (qht g) :=
      (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hg)).2 hg
    have h0 := hs.f_nonneg g
    have h2 : C * (1 + f g) ≤ |C| * (1 + |R|) :=
      mul_le_mul (le_abs_self C) (by linarith [le_abs_self R]) (by linarith) (abs_nonneg C)
    linarith [hs.le_f g]
  obtain ⟨y, x, rfl⟩ : ∃ y x, infGL E a y * finGL E a x = g := ⟨_, _, infGL_mul_finGL g⟩
  have hz := hw (x : GL (Fin a) (Af E) ⧸ U) _ (sand_mem_cone y hOne_mem_cone) (by rw [hΦ y x]; exact hf)
  have h := hc y x X
  rw [hz] at h
  have h2 := congrArg (fun z => Ξ.mat y⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] using h2.symm
end

section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.g2 :
    G2 :=
  Cs.galois_twist_preserves_siegel_bound Cs.lamEx Cs.descEx Cs.descFun Cs.rapidAll Cs.corrSz Cs.decP Cs.decK Cs.loc Cs.geoSum Cs.geoRet Cs.supp
end
