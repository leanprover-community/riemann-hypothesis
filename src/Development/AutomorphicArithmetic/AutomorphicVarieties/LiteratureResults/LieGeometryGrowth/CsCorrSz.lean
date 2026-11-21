import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSecOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz

section
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

private theorem ev_eq_cmp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (UpperTheory.V.Lit.Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul φ v => simp [mul_comm]

private theorem alt_expand {V W M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup M] [Module ℝ M] {q n : ℕ} (α : V [⋀^Fin q]→ₗ[ℝ] M) (e : V ≃ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ W)
    (u : Fin q → W) :
    α (fun i => e.symm (u i)) = ∑ I : Fin q → Fin n, (∏ i, b.repr (u i) (I i)) • α fun i => e.symm (b (I i)) := by
  have h : (fun i => e.symm (u i)) = fun i => ∑ k, b.repr (u i) k • e.symm (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]
    simp only [map_sum, map_smul]
  rw [h]
  refine (α.toMultilinearMap.map_sum (fun i k => b.repr (u i) k • e.symm (b k))).trans ?_
  exact Finset.sum_congr rfl fun I _ => α.map_smul_univ _ _

theorem UpperTheory.V.Lit.Geo.Cs.corrForm :
    CorrForm := by
  intro E _ _ _ a Ξ q v
  classical
  obtain ⟨τ, h1, hτ, -, -, hi, hs⟩ := secOne E a
  let b := Module.finBasis ℝ (HV E a)
  let u : HV E a → Fin q → HV E a := fun p i => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)
  refine ⟨(Fin q → Fin (Module.finrank ℝ (HV E a))) × Fin Ξ.d, inferInstance,
    fun I i => hv.symm (b (I.1 i)), fun I => I.2,
    fun I p k => ((∏ i, b.repr (u p i) (I.1 i) : ℝ) : ℂ) * Ξ.mat (τ p) k I.2,
    fun p => toL (τ p).val, by simp only [h1]; rfl, hτ, fun I => ?_, fun U α w hc g x => ?_⟩
  · refine contDiffAt_pi.2 fun k => ContDiffAt.mul ?_ ?_
    · refine Complex.ofRealCLM.contDiff.contDiffAt.comp (hOne E a)
        (f := fun p => ∏ i, b.repr (u p i) (I.1 i)) ?_
      refine contDiffAt_prod fun i _ => ?_
      have hu : ContDiffAt ℝ ∞ (fun p => u p i) (hOne E a) := (hi.clm_apply contDiffAt_const).const_smul _
      exact (LinearMap.toContinuousLinearMap (b.coord (I.1 i))).contDiff.contDiffAt.comp (hOne E a) hu
    · have := (((matSmooth E a Ξ k I.2).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ (hOne E a))))).comp (hOne E a) hτ
      simpa only [Function.comp_def, extGL_val] using this
  · refine hs.mono fun p hp => ?_
    have e1 : sand (g * τ p) (hOne E a) = sand g p := by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    have e2 : ∀ i, (2 : ℝ) • sand (g * τ p) (u p i) = sand g (v i) := fun i => by
      simp only [u, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp
    have h := hc (g * τ p) x fun i => hv.symm (u p i)
    simp only [LinearEquiv.apply_symm_apply, e1, e2] at h
    have e3 : infGL E a (g * τ p) * finGL E a x = pt g x * infGL E a (τ p) := pt_mul g (τ p) x
    simp only [Tw, tp_apply, mulVecL_apply, h, e3, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left, chart_val]
    rw [alt_expand α hv b (u p)]
    funext k
    have e4 : ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (r : ℝ) (y : GA E a),
        ev (r • α fun i => hv.symm (b (I i))) y = (r : ℂ) • ev (α fun i => hv.symm (b (I i))) y := fun I r y => by
      rw [← algebraMap_smul ℂ r, map_smul]; rfl
    rw [map_sum]
    simp only [Finset.sum_apply, e4, Matrix.mulVec, dotProduct, Pi.smul_apply, ← ev_eq_cmp,
      Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end

section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.altEv :
    AltEv := by
  classical
  intro V F _ _ _ _ _ _ q k
  let bs := Module.finBasis ℝ V
  let L : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun g σ => g (fun i => bs (σ i))
      map_add' := fun g h => by ext σ; simp
      map_smul' := fun c g => by ext σ; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have e : g.toAlternatingMap = (0 : V [⋀^Fin q]→L[ℝ] F).toAlternatingMap :=
      Module.Basis.ext_alternating bs (fun v _ => by simpa [L] using congrFun hg v)
    ext m
    simpa using DFunLike.congr_fun e m
  obtain ⟨M, hM⟩ := L.exists_leftInverse_of_injective hker
  let A : (Fin q → Fin (Module.finrank ℝ V)) → F →L[ℝ] (V [⋀^Fin q]→L[ℝ] F) := fun σ =>
    LinearMap.toContinuousLinearMap (M.comp (LinearMap.single ℝ (fun _ => F) σ))
  refine ⟨Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) => fun i => bs (σ i)),
    ∑ σ, ‖A σ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro f x b hb hcd hsz
  have mem : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      (fun i => bs (σ i)) ∈ Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) =>
        fun i => bs (σ i)) :=
    fun σ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  have hrep : f = fun y => ∑ σ, A σ (f y (fun i => bs (σ i))) := by
    funext y
    calc f y = M (L (f y)) := (LinearMap.congr_fun hM (f y)).symm
      _ = M (∑ σ, Pi.single σ (L (f y) σ)) := by rw [Finset.univ_sum_single]
      _ = ∑ σ, A σ (f y (fun i => bs (σ i))) := by
        rw [map_sum]
        rfl
  intro i hi
  have hcdi : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      ContDiffAt ℝ i (fun y => f y (fun i => bs (σ i))) x :=
    fun σ => (hcd _ (mem σ)).of_le (by exact_mod_cast le_top)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := Finset.univ)
    (f := fun σ y => A σ (f y (fun i => bs (σ i))))
    (fun σ _ => (A σ).contDiff.contDiffAt.comp x (hcdi σ))
  rw [hrep, hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  refine ((A σ).norm_iteratedFDeriv_comp_left (hcdi σ) le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_left (hsz _ (mem σ) i hi) (norm_nonneg _)
end

section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

private theorem term_sz {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ) (τ : V → W) (Θ : V → F) (p : V)
    (hτ : ContDiffAt ℝ ∞ τ p) (hΘ : ContDiffAt ℝ ∞ Θ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W → ℂ) (b : ℝ), ContDiffAt ℝ ∞ u (τ p) → Sz k u (τ p) b →
      Sz k (fun y => u (τ y) • Θ y) p (C * b) := by
  obtain ⟨c, hc⟩ := exists_sz k τ p
  obtain ⟨t, ht⟩ := exists_sz k Θ p
  obtain ⟨C, hC, H⟩ := compSz V W ℂ k c
  let L : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨2 ^ k * (‖L‖ * C) * t, by have := ht.nonneg; positivity, fun u b hu hb => ?_⟩
  have h1 := H u τ p b hτ hu (fun i _ hi => hc i hi) hb
  have s1 : ContDiffAt ℝ ∞ (fun y => u (τ y)) p := hu.comp p hτ
  have h2 := (appSz V ℂ (F →L[ℝ] F) k p).2.1 L _ _ s1 h1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (u (τ y))) p := L.contDiff.contDiffAt.comp p s1
  have h3 := (appSz V F F k p).1 _ Θ _ _ s2 hΘ h2 ht
  exact h3.mono (le_of_eq (by ring))

private theorem val_sz (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (hw : Corr U Ξ α w) (ρ : GA E a → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) (k : ℕ) (v : Fin q → HV E a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, ContDiffAt ℝ ∞ (fun p => Tw U Ξ w g x p v) (hOne E a) ∧
      Sz k (fun p => Tw U Ξ w g x p v) (hOne E a) (M * ρ (pt g x)) := by
  obtain ⟨ι, _, X, j, Θ, τ, h1, hτ, hΘ, H⟩ := corrForm E a Ξ q v
  choose C hC HC using fun i => term_sz k τ (Θ i) (hOne E a) hτ (hΘ i)
  choose D hD HD using fun i => chartSz E a k ρ hρ (Bor.cmp (j i) (α (X i))) (hb (X i) (j i))
  refine ⟨∑ i, C i * D i, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hD i), fun g x => ?_⟩
  have e := H U α w hw g x
  have su : ∀ i, ContDiffAt ℝ ∞ (chart (Bor.cmp (j i) (α (X i))).1 (pt g x)) (τ (hOne E a)) := fun i => by
    rw [h1]; exact contDiffAt_chart (Bor.cmp (j i) (α (X i))).2 _ isUnit_one
  have st : ∀ i, ContDiffAt ℝ ∞ (fun p => chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p) (hOne E a) :=
    fun i => ((su i).comp _ hτ).smul (hΘ i)
  refine ⟨(ContDiffAt.sum fun i _ => st i).congr_of_eventuallyEq e, ?_⟩
  have := (appSz (HV E a) ℝ (Fin Ξ.d → ℂ) k (hOne E a)).2.2 ι Finset.univ _ _ (fun i _ => st i)
    (fun i _ => HC i _ (D i * ρ (pt g x)) (su i) (by rw [h1]; exact HD i _))
  refine (this.congr e.symm).mono (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.corrSz :
    UpperTheory.V.Lit.Geo.Cs.CorrSz := by
  intro E _ _ _ a U Ξ q α w hw ρ hρ hb k
  obtain ⟨T, C, hC, H⟩ := Cs.altEv (HV E a) (Fin Ξ.d → ℂ) q k
  choose M hM HM using Cs.val_sz E a U Ξ q α w hw ρ hρ hb k
  have h0 : 0 ≤ ∑ v ∈ T, M v := Finset.sum_nonneg fun v _ => hM v
  refine ⟨C * ∑ v ∈ T, M v, mul_nonneg hC h0, fun g x => ?_⟩
  rw [mul_assoc]
  exact H _ _ _ (mul_nonneg h0 (hρ _)) (fun v _ => (HM v g x).1) fun v hv => (HM v g x).2.mono
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) hv) (hρ _))
end
