import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiOfClosedTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoreUHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.SecUHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoverJ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ZeroAp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvQHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvUHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowDvdOfEv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.DvdMulEntriesRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordWD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpOneHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpExHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TieRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TraceEqNextCoeff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.frEx_holds :
    FrEx := by
  intro l _ K L₀ bk τp hτp P AI T a hL₀ r Cl Cv J hCl hcr
  haveI := K.2
  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2
  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, -, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hFc : ∀ m, (F m).IsCr := fun m =>
    hFcr m ((GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)
  exact ⟨N, F, F₀, rr, hFc, hF₀cr hFc, hlink⟩
end

section
noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

open Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Per

theorem func_holds : IntBasis → Func := by
  intro hB l _ F I _ x z hx hz
  classical
  letI : Fintype I := Fintype.ofFinite I
  let eqv := Fintype.equivFin (Option I)
  let y : Fin (Fintype.card (Option I)) → Om l := fun k => (eqv.symm k).elim z x
  have hy : ∀ k, ‖y k‖ ≤ 1 := by
    intro k
    dsimp only [y]
    cases eqv.symm k with
    | none => simpa using hz
    | some i => simpa using hx i
  obtain ⟨m, e, hli, he, hc⟩ := hB l F _ y hy
  choose c hc1 hc2 using hc
  have hyz : y (eqv none) = z := by simp [y]
  have hyx : ∀ i, y (eqv (some i)) = x i := by intro i; simp [y]
  by_cases hz0 : z = 0
  · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [hz0]
  have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hz0
    rw [← hyz, hc2, hne, Finset.sum_empty]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖((c (eqv none) j : ↥F) : Om l)‖) hm
  let f : (Fin m → ↥F) →ₗ[↥F] Om l := Fintype.linearCombination ↥F e
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    funext j
    exact Fintype.linearIndependent_iff.1 hli a (by simpa [f, Fintype.linearCombination_apply] using ha) j
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let lam : Om l →ₗ[↥F] ↥F := LinearMap.proj j₀ ∘ₗ G
  have key : ∀ a : Fin m → ↥F, lam (∑ j, (a j : Om l) * e j) = a j₀ := by
    intro a
    have h1 : (∑ j, (a j : Om l) * e j) = f a := by
      simp only [f, Fintype.linearCombination_apply]
      rfl
    have h2 : G (f a) = a := by
      have := LinearMap.congr_fun hG a
      simpa using this
    rw [h1]
    simp only [lam, LinearMap.comp_apply, h2, LinearMap.proj_apply]
  have hlz : lam z = c (eqv none) j₀ := by
    rw [← hyz, hc2, key]
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro i
    rw [← hyx i, hc2, key]
    exact hc1 _ _
  · rw [hlz]
    rw [← hyz, hc2]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro j _
    rw [norm_mul]
    calc ‖((c (eqv none) j : ↥F) : Om l)‖ * ‖e j‖
        ≤ ‖((c (eqv none) j : ↥F) : Om l)‖ * 1 :=
          mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)
      _ = ‖((c (eqv none) j : ↥F) : Om l)‖ := mul_one _
      _ ≤ _ := hj₀ j (Finset.mem_univ j)
  · rw [hlz]
    exact hc1 _ _

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trId_holds :
    TrId := by
  intro l _ B _ u zb hz s d d' m t t' c pv p θ Pi e e' V V' h1 h2 lam
  have hscal : ∀ (z : ℤ_[l]) (x : Om l), u (lam (zOm l z * x)) = zb z * u (lam x) := by
    intro z x
    have hx : zOm l z * x = (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • x := by
      rw [Algebra.smul_def]
      rfl
    rw [hx, map_smul, smul_eq_mul, map_mul, hz]
  have hk : ∀ k, ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (c k * t' j k)) = s * u (lam (c k * pv k)) := by
    intro k
    simpa using h2 k (lam ∘ₗ LinearMap.mulLeft ↥(MaximalUnramifiedExtension l) (c k))
  have hE : (fun i => zb ((Pi *ᵥ e' - e) i)) = Pi.map zb *ᵥ (fun j => zb (e' j)) - fun i => zb (e i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hX : (V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ (fun i => zb ((Pi *ᵥ e' - e) i)) =
      V *ᵥ (fun i => zb (e i)) - Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j)) := by
    rw [hE, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hA := h1 lam
  have hS1 : ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) =
      s * u (lam p) - ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
    rw [hX, ← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [_root_.Pi.sub_apply]
    ring
  have hS2 : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) =
      ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) - ∑ k, s * u (lam (c k * pv k)) := by
    have ha : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ i, zb (Pi i j) * u (lam (t i)) =
        ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
      generalize (V' *ᵥ fun i => zb (e' i)) = w
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ k, u (lam (c k * t' j k)) = ∑ k, s * u (lam (c k * pv k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => hk k
    rw [← ha, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_sum, hscal, mul_sub]
  have hS3 : s * u (lam (θ - ∑ k, c k * pv k)) = s * u (lam θ) - ∑ k, s * u (lam (c k * pv k)) := by
    simp only [map_sub, map_sum, mul_sub, Finset.mul_sum]
  rw [hS1, hS2, hS3, map_sub, map_sub, mul_sub]
  ring
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
end

section
namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkRec_holds : LinkRec := by
  intro R _ φ lr π v w N d d' α β Q α₁ β₁ β₁' Q₁ R₁ R₀ h1 h2 h3 h4 h5
  obtain ⟨u, hu_def⟩ : ∃ u : R, u = ((v ^ N * w ^ (2 * N))⁻¹ : Rˣ) := ⟨_, rfl⟩
  set s := (lr * (v : R)) ^ N with hs
  set t := (lr * (w : R)) ^ N with ht
  have hvw : u * ((v : R) ^ N * (w : R) ^ (2 * N)) = 1 := by
    rw [hu_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, Units.inv_mul]
  have hu : u * (s * (lr * (w : R)) ^ (2 * N)) = lr ^ (3 * N) := by
    calc u * (s * (lr * (w : R)) ^ (2 * N))
        = (u * ((v : R) ^ N * (w : R) ^ (2 * N))) * lr ^ (3 * N) := by
          rw [hs]
          ring
      _ = lr ^ (3 * N) := by rw [hvw, one_mul]
  refine ⟨(u * t) • α, β₁', ?_⟩
  set D4 := R₁ * α₁ - α * R₁.map φ with hD4def
  set D5 := R₀ * β₁ - β * R₀.map φ with hD5def
  have hD4 : α * R₁.map φ = R₁ * α₁ - D4 := by rw [hD4def, sub_sub_cancel]
  have hD5 : β * R₀.map φ = R₀ * β₁ - D5 := by rw [hD5def, sub_sub_cancel]
  have e1 : t • (α * R₁.map φ * Q₁.map φ) = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
    calc t • (α * R₁.map φ * Q₁.map φ) = t • ((R₁ * α₁ - D4) * Q₁.map φ) := by rw [hD4]
      _ = R₁ * (t • (α₁ * Q₁.map φ)) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.sub_mul, smul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = R₁ * (s • (Q₁ * β₁)) - t • (D4 * Q₁.map φ) := by rw [h3]
      _ = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have e2 : t • (α * Q.map φ * R₀.map φ) = s • (Q * R₀ * β₁) - s • (Q * D5) := by
    calc t • (α * Q.map φ * R₀.map φ) = (t • (α * Q.map φ)) * R₀.map φ := by rw [Matrix.smul_mul]
      _ = (s • (Q * β)) * R₀.map φ := by rw [h2]
      _ = s • (Q * (β * R₀.map φ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = s • (Q * (R₀ * β₁ - D5)) := by rw [hD5]
      _ = s • (Q * R₀ * β₁) - s • (Q * D5) := by
        simp only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
  have hmap : (R₁ * Q₁ - Q * R₀).map φ = R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul]
  have e3 : (u * t) • α * (R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ)
      = u • (t • (α * R₁.map φ * Q₁.map φ) - t • (α * Q.map φ * R₀.map φ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_sub, smul_sub, smul_smul, Matrix.mul_assoc]
  have key : lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - (u * t) • α * (R₁ * Q₁ - Q * R₀).map φ * β₁'
      = (u * t) • (D4 * (Q₁.map φ * β₁')) - (u * s) • (Q * (D5 * β₁')) := by
    rw [hmap, e3, e1, e2, ← hu]
    simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub]
    module
  intro i j
  rw [key, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    Matrix.mul_apply, Matrix.mul_apply]
  refine dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h4 i k) _) _)
    (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right ?_ _) _)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k' _ => dvd_mul_of_dvd_left (h5 k k') _

end UpperTheory.Gal.ClosedPhiFromClosedTrace
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixW_holds :
    FixW := by
  intro l _ K bk P AI T n hn s
  set x := f0 bk s with hx
  have hact := ActLaws.act_laws l
  have hσB : ∀ (g : GQ l) (y : Per.Acris l), Per.σB g (iB l y) = iB l (sigA g y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.1
  have hφB : ∀ y : Per.Acris l, Per.φB l (iB l y) = iB l (phiA l y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hfix : ∀ g : ↥(GK K), sigA (g : GQ l) x = x := by
    intro g
    have hxe : x = iA l (WittVector.frobenius (bk.ev (PowerSeries.C (PowerSeries.constantCoeff s)))) := by
      simp only [hx, f0, fA, RingHom.comp_apply, bk.ev_frob]
    rw [hxe, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g]
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  set b := T.eB.symm (iB l x) with hb
  have hbfix : ∀ g : ↥(GK K), (P.PD K).actB g b = b := by
    intro g
    apply T.eB.injective
    rw [P.PD_actB, T.actB, hb, RingEquiv.apply_symm_apply, hσB, hfix]
  obtain ⟨c, hc⟩ := (P.PD K).invB b hbfix
  have hc' : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ = b := hc
  have hit : ∀ (m : ℕ) (y : ↥(MaximalUnramifiedExtension l)), (fun z => P.φB z)^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B y) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((frobUr l ^ m) y) := by
    intro m y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, phiB_algebraMap, pow_succ', AlgHom.mul_apply]
  have hbn : (fun z => P.φB z)^[n] b = b := by
    rw [← hc', hit, hn ⟨c, c.2.2⟩ c.2.1]
  have htr : ∀ (m : ℕ) (y : P.R.B), T.eB ((fun z => P.φB z)^[m] y) = (Per.φB l)^[m] (T.eB y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hin : ∀ (m : ℕ) (y : Per.Acris l), (Per.φB l)^[m] (iB l y) = iB l ((phiA l)^[m] y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφB]
  apply hinj
  have h1 := htr n b
  rw [hbn, hb, RingEquiv.apply_symm_apply, hin] at h1
  rw [RingHom.coe_pow]
  exact h1.symm
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLin_holds :
    TrLin := by
  intro k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h
  classical
  let bW : Module.Basis (Fin a) k W := Module.finBasisOfFinrankEq k W ha
  have hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i := by
    intro y i
    conv_lhs => rw [← bW.sum_repr y]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ, Pi.smul_apply, smul_eq_mul]
  let X : Matrix (Fin a) (Fin a) B := Matrix.of fun i m => ψ (bW m) i
  let X' : Matrix (Fin a) (Fin a) B := Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)
  have hXX : X * X' = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h i i']
    simp only [X, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp (x j i') i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hXX' : X' * X = 1 := mul_eq_one_comm.mp hXX
  let Tm : Matrix (Fin a) (Fin a) B := (LinearMap.toMatrix bW bW T).map κ
  have hrepr : ∀ (y : W) (m : Fin a),
      bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m' := by
    intro y m
    rw [← LinearMap.toMatrix_mulVec_repr bW bW T y]
    rfl
  have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by
    intro i i'
    have hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m) := by
      intro y
      rw [hexp (T y) i]
      simp only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
    rw [Matrix.mul_apply]
    simp only [hTX, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
  have htr : Matrix.trace Tm = κ (LinearMap.trace k W T) := by
    rw [LinearMap.trace_eq_matrix_trace k bW T]
    simp [Matrix.trace, Tm, map_sum]
  calc ∑ i, ∑ j, w j * ψ (T (x j i)) i = Matrix.trace (X * Tm * X') := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry]
    _ = Matrix.trace (X' * X * Tm) := by
        rw [Matrix.trace_mul_cycle]
    _ = κ (LinearMap.trace k W T) := by
        rw [hXX', one_mul, htr]
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private def coordPair (P : LocPrime l) (L : FinExt l) (a : ℕ) :
    (Fin a → ↥L.1) →+ Bst P →+ (Fin a → OB P) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun b i => ((v i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] b)
      (fun b b' => by funext i; simp [TensorProduct.tmul_add]))
    (fun v v' => by
      ext b i
      simp [TensorProduct.add_tmul])

theorem coordEx_holds : CoordEx := by
  intro l _ P L a
  refine ⟨TensorProduct.liftAddHom (coordPair P L a) ?_, ?_⟩
  · intro r v b
    funext i
    simp only [coordPair, AddMonoidHom.mk'_apply, Pi.smul_apply]
    rw [show ((r • v i : ↥L.1) : Om l) = r • ((v i : ↥L.1) : Om l) from rfl]
    exact TensorProduct.smul_tmul r _ b
  · intro v b i
    rfl

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem actQ_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (g : GQ l)
    (y : Per.Bcris l) : P.actQ g (T.eB.symm y) = T.eB.symm (Per.σB g y) := by
  apply T.eB.injective
  rw [T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem phiB_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (y : Per.Bcris l) : P.φB (T.eB.symm y) = T.eB.symm (Per.φB l y) := by
  apply T.eB.injective
  rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • T.eB.symm y = T.eB.symm (Per.zB l z * y) := by
  apply T.eB.injective
  rw [Algebra.smul_def, map_mul, T.zB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • (Polynomial.C (T.eB.symm y) : Bst P) = Polynomial.C (T.eB.symm (Per.zB l z * y)) := by
  rw [← smul_symm T z y]
  exact Polynomial.smul_C (z : ℚ_[l]) (T.eB.symm y)

private theorem sum_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {ι : Type}
    (s : Finset ι) (f : ι → Per.Bcris l) :
    ∑ i ∈ s, (Polynomial.C (T.eB.symm (f i)) : Bst P) = Polynomial.C (T.eB.symm (∑ i ∈ s, f i)) := by
  rw [map_sum T.eB.symm]
  exact (map_sum (Polynomial.C : P.R.B →+* Polynomial P.R.B) _ _).symm

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.colInv_holds :
    ColInv := by
  intro l _ P AI T K L a d ρ R v hv U hU j
  refine ⟨?_, fun n => ?_⟩
  · rw [mem_Dst]
    intro g
    have hinv : ∀ i', ∑ i, Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j) = U i' j := fun i' => by
      have h := congrFun (congrFun (hU.inv g) i') j
      simpa [Matrix.mul_apply, Matrix.map_apply] using h
    rw [map_sum]
    have step : ∀ i, (stRep P R g) (v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) =
        ∑ i', v i' ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j))) : Bst P) := fun i => by
      rw [stRep_tmul, actSt_C, actQ_symm T, hv, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← smul_Cst T, TensorProduct.smul_tmul]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← TensorProduct.tmul_sum, sum_Cst T, hinv]
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [phiV_tmul, phiSt_C, phiB_symm T, pow_succ', RingHom.mul_def, RingHom.comp_apply]
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h
  rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective
    rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2
  simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end

section
noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkOp_holds : LinkOp2 := by
  intro R _ π s d d' W Z Zs W₁ Z₁ Zs₁ Pm R₀ h1 h2 hA hB i j
  have hl : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (X * A) i j := by
    intro m n p X A h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h k j).mul_left _
  have hr : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (A * Y) i j := by
    intro m n p A Y h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h i k).mul_right _
  have e1 : W * Zs * Pm * Z₁ * Zs₁ = s • (W * Zs * Pm) := by
    rw [Matrix.mul_assoc (W * Zs * Pm), h2, Matrix.mul_smul, Matrix.mul_one]
  have e2 : W * Zs * Z * R₀ * Zs₁ = s • (W * R₀ * Zs₁) := by
    rw [Matrix.mul_assoc W Zs Z, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_mul]
  have key : s • (W * Zs) * Pm - Pm * s • (W₁ * Zs₁) =
      W * Zs * (Pm * Z₁ - Z * R₀) * Zs₁ - s • ((Pm * W₁ - W * R₀) * Zs₁) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, smul_sub, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [e1, e2]
    abel
  rw [key, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_sub (hr _ _ (hl _ _ hA) i j) ((hr _ _ hB i j).mul_left s)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkZ_holds :
    LinkA → LinkQ → LinkZ := by
  intro hA hQ l _ K bk τ hτ N M
  obtain ⟨n, hn⟩ := hQ l K bk N M
  refine ⟨max n M, ?_⟩
  intro k d d' ρ ρ' F F' Y Y₁ hY hY₁ Q Q' Q₁ Q₁' hS hS₁ Pi R hL
  obtain ⟨h1, h2⟩ := hA l K bk τ hτ N d d' (max n M) ρ ρ' F F' Y Y₁ hY hY₁ Pi R hL
  have hfz : ∀ z : ℤ_[l], fI l (Per.zA l z) = zC l z := fun z => by
    have h := (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    simp only [fI, zC, RingHom.comp_apply]
    rw [← GlobalTheory.RingBasics.φA_apply, h]
  have hfe : ∀ s : bk.S, fI l (bk.ev s) = fA bk s := fun s => by
    simp only [fI, fA, RingHom.comp_apply, bk.ev_frob]
  have hlM : ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) i j := by
    intro i j
    have h := map_dvd (fI l) (h1 i j)
    simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hfz, hfe,
      map_pow, map_natCast] at h ⊢
    exact (pow_dvd_pow _ (le_max_right _ _)).trans h
  have h3 := hn k d d' F.A F'.A F'.A' Q Q' Q₁ Q₁' R F'.A_mul hS hS₁
    (fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (h2 i j))
  intro i j
  have e : Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk) =
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) * Q₁ +
        Y.map (fI l) * (R.map (fA bk) * Q₁ - Q * R.map (f0 bk)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact dvd_add (Finset.dvd_sum fun x _ => (hlM i x).mul_right _)
    (Finset.dvd_sum fun x _ => (h3 x j).mul_left _)
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem fix_aux {A S : Type} [CommSemiring A] [Semiring S] [Algebra A S] (φ : S →ₐ[A] S) (x y : ℕ) (c : S)
    (h : (φ ^ y) c = (φ ^ x) c) : (φ ^ ((x : ℤ) - y).natAbs) ((φ ^ y) c) = (φ ^ y) c := by
  rcases le_total x y with hxy | hxy
  · have e : ((x : ℤ) - y).natAbs = y - x := by omega
    rw [e, h, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]
  · have e : ((x : ℤ) - y).natAbs = x - y := by omega
    rw [e, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixOf_holds :
    FixOf := by
  intro l _ E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g c hc
  obtain ⟨a, b, hσ⟩ := g.2
  have hal : (alpha l g) = ((resDeg l w * a : ℕ) : ℤ) - ((resDeg l w * b : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c', rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * b))).2 c
  have h1 := weilToGK_frobUr hj g hσ c'
  rw [mem_GK.mp (weilToGK Bw h g).2 _ hc] at h1
  rw [hal]
  exact fix_aux _ _ _ _ (Subtype.ext h1)
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem weilPhi_core {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ)
    (hα : alpha l g = (n₂ : ℤ) - n₁) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (R : Representation LL ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
    (m : V ⊗[ℚ_[l]] Bst P) (hm : m ∈ Dst P R) :
    ∃ x : ↥(Dpst P R), (x : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n₁) m := by
  let m₀ : ↥(Dpst P R) := ⟨m, (mem_Dpst P R).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P R).mp hm g⟩⟩
  have hc : ∀ (n : ℕ) (y : ↥(Dpst P R)),
      (((phiD P R ^ n) y : ↥(Dpst P R)) : V ⊗[ℚ_[l]] Bst P) = (phiV P LL V ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  have hu : ∀ n : ℕ, ((phiU P R ^ (n : ℤ) : (Module.End LL ↥(Dpst P R))ˣ) :
      Module.End LL ↥(Dpst P R)) = phiD P R ^ n := by
    intro n
    rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU]
  have hmul : ((phiU P R ^ (-alpha l g) : (Module.End LL ↥(Dpst P R))ˣ) :
      Module.End LL ↥(Dpst P R)) * phiD P R ^ n₂ = phiD P R ^ n₁ := by
    rw [← hu n₂, ← hu n₁, ← Units.val_mul, ← _root_.zpow_add, hα]
    congr 2
    ring
  refine ⟨(phiD P R ^ n₂) m₀, hc n₂ m₀, ?_⟩
  have e : weilD Bw h P R g ((phiD P R ^ n₂) m₀) =
      actD P R (weilToGK Bw h g) ((phiD P R ^ n₁) m₀) := by
    rw [weilD_apply, Module.End.mul_apply, ← hmul, Module.End.mul_apply]
  rw [e, coe_actD, hc]
  have hcomm : Commute (phiV P LL V) (stRep P R (weilToGK Bw h g)) :=
    phiV_stRep P R (weilToGK Bw h g)
  have h2 := LinearMap.congr_fun (hcomm.pow_left n₁).eq m
  rw [Module.End.mul_apply, Module.End.mul_apply, (mem_Dst P R).mp hm] at h2
  exact h2.symm

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.weilPhi_holds :
    WeilPhi2 := by
  intro l _ P E Ω _ _ _ _ _ w A h O _ _ _ Bw g n₁ n₂ hα L a R _ m hm
  exact weilPhi_core P h Bw g n₁ n₂ hα R m hm
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.powTr_holds :
    PowTr := by
  intro E Ω _ _ _ _ _ w A h x σ n
  have h1 : (x.charPol (σ ^ n)).roots = Multiset.map (fun y => y ^ n) (x.charPol σ).roots :=
    GlobalTheory.AboveL.eig_pow_of_rep x σ n
  show (Multiset.map (fun y => y ^ n) (x.charPol σ).roots).sum = _
  rw [← h1, Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic (IsAlgClosed.splits _)
    (x.charPol_monic _), neg_neg]
end

section
namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem ClosedTr_holds : ClosedTr :=
  closedTr_of coverJ_holds frEx_holds
    (opEx_holds (secU_holds coreU_holds) invQ_holds invU_holds (linkZ_holds linkA_holds (linkQ_holds zeroAp_holds linkRec_holds))
      linkOp_holds fixW_holds opOne_holds)
    fixOf_holds
    (tie_holds (tieRep_holds trLin_holds coordEx_holds coordWD_holds colInv_holds weilPhi_holds testTr_holds))
    (trLim_holds (trStep_holds (func_holds intBasis_holds) trId_holds))

theorem congPhi_holds : GlobalTheory.CongPhi.ClosedPhi := congPhi_of_closedTr ClosedTr_holds powTr_holds

end UpperTheory.Gal.ClosedPhiFromClosedTrace
end
