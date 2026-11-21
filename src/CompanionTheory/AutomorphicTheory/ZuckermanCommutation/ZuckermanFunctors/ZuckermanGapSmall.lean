import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.MultOne
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem decomposition_of_injective : DecOfInj := by
  intro O N _ _ Hom C S _ X T hs hj hm hi
  classical
  choose i hi hi0 using hi
  have hp : ∀ s, ∃ p, Hom X (T s) p ∧ p ∘ₗ i s = LinearMap.id ∧ p ≠ 0 := by
    intro s
    obtain ⟨y, hy⟩ : ∃ y, i s y ≠ 0 := by
      by_contra hn
      exact hi0 s (LinearMap.ext fun y => not_not.1 fun h => hn ⟨y, h⟩)
    obtain ⟨t, p, hp, hpy⟩ : ∃ t p, Hom X (T t) p ∧ p (i s y) ≠ 0 := by
      by_contra hn
      exact hy (hj _ fun t p hp => not_not.1 fun h => hn ⟨t, p, hp, h⟩)
    obtain rfl : s = t := by
      by_contra hst
      exact hpy (LinearMap.congr_fun (hs.2.2 s t hst _ (C.comp _ _ _ _ _ (hi s) hp)) y)
    obtain ⟨c, hc⟩ := hs.2.1 s _ (C.comp _ _ _ _ _ (hi s) hp)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hpy (by simpa using LinearMap.congr_fun hc y)
    refine ⟨c⁻¹ • p, C.smul _ _ _ _ hp, ?_, fun h0 => hpy ?_⟩
    · rw [LinearMap.smul_comp, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rw [(smul_eq_zero.1 h0).resolve_left (inv_ne_zero hc0)]; rfl
  choose p hp hpi hp0 using hp
  have hne : ∀ s t, s ≠ t → p s ∘ₗ i t = 0 := fun s t hst =>
    hs.2.2 t s (Ne.symm hst) _ (C.comp _ _ _ _ _ (hi t) (hp s))
  refine ⟨i, p, hi, hp, LinearMap.ext fun x => ?_, hpi, hne⟩
  rw [LinearMap.id_apply, eq_comm, ← sub_eq_zero]
  refine hj _ fun t q hq => ?_
  have h0 : p t (x - (∑ s, i s ∘ₗ p s) x) = 0 := by
    rw [map_sub, LinearMap.sum_apply, map_sum, Finset.sum_eq_single t]
    · exact sub_eq_zero.2 (LinearMap.congr_fun (hpi t) (p t x)).symm
    · intro s _ hst
      exact LinearMap.congr_fun (hne t s (Ne.symm hst)) (p s x)
    · simp
  obtain ⟨α, β, hab, h1⟩ := hm t q (p t) hq (hp t)
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h1
    exact hp0 t ((smul_eq_zero.1 h1).resolve_left (hab.resolve_left (not_not.2 rfl)))
  have h2 := LinearMap.congr_fun h1 (x - (∑ s, i s ∘ₗ p s) x)
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, h0, smul_zero, add_zero] at h2
  exact (smul_eq_zero.1 h2).resolve_left hα

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trivial_rep_admissible : OKTriv := fun _ _ =>
  ⟨rfl, fun _ _ _ _ => (Matrix.one_mul _).symm,
    fun _ _ _ _ => ⟨Set.univ, _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    ⟨1, fun _ _ _ _ => by simp⟩⟩

theorem vector_rep_admissible : OKVr := by
  intro k r b
  cases b
  · refine ⟨rfl, fun _ _ _ _ => rfl, fun c d _ _ => ?_, ⟨1, fun g _ c d => ?_⟩⟩
    · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial,
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c d)).contDiff.contDiffOn, fun _ _ _ => rfl⟩
    · simpa using GlobalTheory.DualFRep.entry_le g c d
  · obtain ⟨-, -, h1, h2, -, -, h3, -⟩ := GlobalTheory.isFRep_dualM k r
    refine ⟨h1, h2, fun c d _ _ => ?_, h3⟩
    let A : Mx k r →ₗ[ℝ] ℂ :=
      { toFun := fun x => (PI.UpqRep.Hpk k r * xᴴ * PI.UpqRep.Hpk k r) d c
        map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun t a => by
          rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, star_trivial]; rfl }
    refine ⟨Set.univ, A, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap A).contDiff.contDiffOn,
      fun g _ hg => ?_⟩
    show g⁻¹ d c = _
    rw [PI.HwUniqW.inv_eq_UH hg]; rfl

end CompanionTheory.Zuck

end
end

section
open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cMT_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * Bᵀ = 1) :
    (cM n)ᵀ * (1 : Matrix Unit Unit ℂ) = (A ⊗ₖ B) * (cM n)ᵀ := by
  ext ⟨i, j⟩ u
  rw [Matrix.mul_one]
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cM, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [← hij]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem hpk_apply_lemma (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i l = if (l : ℕ) = (if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i) then
      (if (i : ℕ) = r + k then -1 else 1) else 0 := by
  have hi := i.2
  have hl := l.2
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | rfl | omega | norm_num

private theorem hpk_mul_self_lemma_2 (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [Matrix.mul_apply]
  simp only [hpk_apply_lemma]
  rw [Finset.sum_eq_single ⟨if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i, by split_ifs <;> omega⟩]
  · simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega | norm_num
  · intro l _ hl
    rw [if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_lemma_3 {k r : ℕ} {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ BranchingSupport.GG k r) : IsUnit g.det := by
  have hH : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_mul_self_lemma_2 k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hg' : g.conjTranspose * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hH
  rw [← hg', Matrix.det_mul, h0, mul_zero]

theorem cMT_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom (one B) ((vr k r b).tens (vr k r (!b)), B) (mAct (cM _)ᵀ) := by
  refine hM k r (triv k r) ((vr k r b).tens (vr k r (!b))) B (cM _)ᵀ (fun g hg => ?_)
  have hinv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_det_lemma_3 hg)
  have hAB : (vr k r b).ρ g * ((vr k r (!b)).ρ g)ᵀ = 1 := by
    cases b <;> simp [vr, BranchingSupport.dualM, hinv, ← Matrix.transpose_mul]
  exact cMT_mul hAB

def uR (ι : Type) [DecidableEq ι] : Matrix (ι × Unit) ι ℂ := fun p d => if p.1 = d then 1 else 0

theorem uR_int (F : FRep k r) (g : Mx k r) : uR F.ι * F.ρ g = (F.tens (triv k r)).ρ g * uR F.ι := by
  ext ⟨i, u⟩ d
  cases u
  simp [Matrix.mul_apply, uR, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem uMT_int (F : FRep k r) (g : Mx k r) : (uM F.ι)ᵀ * ((triv k r).tens F).ρ g = F.ρ g * (uM F.ι)ᵀ := by
  ext d ⟨u, e⟩
  cases u
  simp [Matrix.mul_apply, uM, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

section

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def adjTo (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) : (Unit → V) →ₗ[ℂ] (Fin n → V') :=
  mAct (uM (Fin n))ᵀ ∘ₗ (on1 p ∘ₗ mAct (cM n)ᵀ)

def adjFrom (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) : (Fin n → V) →ₗ[ℂ] (Unit → V') :=
  mAct (cM n) ∘ₗ (on2 i ∘ₗ mAct (uR (Fin n)))

theorem adjTo_apply (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) (x : Unit → V) (d : Fin n) :
    adjTo p x d = p (Pi.single d (x ())) () := by
  simp [adjTo, mAct_apply, uM, cM, on1, Fintype.sum_prod_type]
  have e : (LinearMap.funLeft ℂ V fun c => (c, d)) ((mAct (cM n)ᵀ) x) = Pi.single d (x ()) := by
    funext c
    simp [LinearMap.funLeft_apply, mAct_apply, cM, Matrix.transpose_apply, Pi.single_apply]
  rw [e]

theorem adjFrom_apply (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) (y : Fin n → V) (u : Unit) :
    adjFrom i y u = ∑ c, i (fun _ => y c) c := by
  simp [adjFrom, mAct_apply, uR, cM, on2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  have e : (LinearMap.funLeft ℂ V fun d => (c, d)) ((mAct (uR (Fin n))) y) = fun _ => y c := by
    funext u
    simp [LinearMap.funLeft_apply, mAct_apply, uR]
  rw [e]

def adjEquiv : ((Fin n → V) →ₗ[ℂ] (Unit → V')) ≃ₗ[ℂ] ((Unit → V) →ₗ[ℂ] (Fin n → V')) where
  toFun := adjTo
  invFun := adjFrom
  map_add' p q := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  map_smul' a p := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  left_inv p := LinearMap.ext fun y => funext fun u => by
    rw [adjFrom_apply]
    simp only [adjTo_apply]
    rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]
  right_inv i := LinearMap.ext fun x => funext fun d => by
    rw [adjTo_apply, adjFrom_apply, Finset.sum_eq_single d]
    · simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      exact congrFun (map_zero i) c
    · simp

end

theorem adj_of (hC : HomCat) (hM : MatHom) (hT : TensHom) : Adj := by
  intro k r b U U'
  refine ⟨adjEquiv, fun p => ⟨fun hp => ?_, fun hq => ?_⟩⟩
  · have h1 := cMT_hom hM b U
    have h2 := (hT k r (vr k r b) (triv k r) (vr k r (!b)) U U' p hp).1
    have h3 : IsHom ((triv k r).tens (vr k r (!b)), U') (vr k r (!b), U') (mAct (uM (vr k r (!b)).ι)ᵀ) :=
      hM k r _ _ U' _ (fun g _ => uMT_int (vr k r (!b)) g)
    exact (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
  · have h1 : IsHom (vr k r b, U) ((vr k r b).tens (triv k r), U) (mAct (uR (vr k r b).ι)) :=
      hM k r _ _ U _ (fun g _ => uR_int (vr k r b) g)
    have h2 := (hT k r (triv k r) (vr k r (!b)) (vr k r b) U U' (adjEquiv p) hq).2
    have h3 := cM_hom hM b U'
    have h4 := (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
    rw [← adjEquiv.left_inv p]
    exact h4

end CompanionTheory.Zuck

end
end

section
namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps where
  infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  decOfInj := decomposition_of_injective
  decOfTrace := GlobalTheory.T.DecompositionOfTrace
  homCat := GlobalTheory.T.HomCategory
  okTriv := trivial_rep_admissible
  okVr := vector_rep_admissible
  okWedge := GlobalTheory.T.ExteriorPowerIntegral
  okTens := GlobalTheory.T.TensorPowerIntegral
  matHom := GlobalTheory.T.MatrixHom
  uIso := GlobalTheory.T.UnitaryIso
  homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
  casSplit := GlobalTheory.T.CasimirSplitting
  casDS := GlobalTheory.T.CasimirDiagonalSum
  wedgeInt := GlobalTheory.T.ExteriorIntegrality
  wedgeQ := GlobalTheory.T.exterior_differential_sign_rule_quadratic GlobalTheory.T.StandardDifferential GlobalTheory.T.exterior_differential_matrix_unit_formula
  schur := CompanionTheory.D.gk.FinalFormK.schur'
  adj := adj_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom'
  multOne := multOne_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting GlobalTheory.T.StandardDifferential
    CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible GlobalTheory.T.TensorPowerIntegral
  inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
  occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
  zuckH := GlobalTheory.T.zuckerman_hypothesis
  decTens := GlobalTheory.T.decomposition_of_tensor_from_hom_laws GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
  toRaw := GlobalTheory.T.ToRawComplex
  count := GlobalTheory.T.CountingBound

end CompanionTheory.Zuck
end

section
open Matrix

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData ReciprocityTheory.ChartRestriction.DS

def thr (n : ℕ) (ε : Fin n → Bool) : ℝ := max (thrStar ε) (G2.thrS ε)

theorem thr_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thr n ε ≤ 43 * (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hq : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have h0 : S7.q0 ε ≤ n := by unfold S7.q0; omega
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have h4 : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h5 : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
  have h6 : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith

theorem dsigW_SK {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : ∀ (W : List (Mx k r)) (v : H),
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    change Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_SK σ W v]; rfl

theorem zuckerman_library_bounds : Lib thr where
  zg := fun n ε μ H _ _ _ σ hμ hσ h hg ht =>
    have ht' : G2.thrS ε + 1 < h := lt_of_le_of_lt (by unfold thr; linarith [le_max_right (thrStar ε) (G2.thrS ε)]) ht
    ⟨G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg ht', G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg ht'⟩
  dec := by
    intro k r ε μ U h m hU hg ht
    obtain ⟨C, Ws, hWs, hC⟩ := DecInf.decSm hU.1 hg m
      (lt_of_le_of_lt (by unfold thr; linarith [le_max_left (thrStar ε) (G2.thrS ε)]) ht) (σ := U.R.σ) hU.2
    refine ⟨C, Ws, fun W hW => (hWs W hW).2, fun u hu v hv g hg' => ?_⟩
    have h1 := hC u hu v hv g hg'
    simp only [dsigW_SK] at h1
    exact h1
  uniq := by
    intro k r ε μ R R' h hR hR' hg ht
    have h2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) < h :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right (thrStar ε) (G2.thrS ε))) ht
    obtain ⟨P, hP, hd⟩ := hR.2
    obtain ⟨P', hP', hd'⟩ := hR'.2
    have hU' := CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds hR'.2
    obtain ⟨e, he⟩ := (G2.discrete_series_props_large_gap _ ε μ hR.1 h hg h2 R.H (fun g => R.σ (P⁻¹ * g * P)) hd).2.2.2.2 R'.H
      (fun g => R'.σ (P'⁻¹ * g * P')) hd'
    have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
    have hPu' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det _).1 hP'.1.1
    have hb : P⁻¹ * P' ∈ GG k r := by
      have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one]
      show (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P') = PI.UpqRep.Hpk k r
      calc (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P')
          = P'ᴴ * (P⁻¹ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) * P' := by
            rw [← hP.1.2]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, Matrix.mul_one, hP'.1.2]
    obtain ⟨-, ha, hmul⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hb
    have hab : (P⁻¹ * P')⁻¹ = P'⁻¹ * P := by rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu]
    rw [hab] at ha
    have hba : P⁻¹ * P' * (P'⁻¹ * P) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu', Matrix.nonsing_inv_mul _ hPu]
    have hab' : P'⁻¹ * P * (P⁻¹ * P') = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.nonsing_inv_mul _ hPu']
    have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ x, R'.σ (a * b) x = R'.σ a (R'.σ b x) := fun a ha b hb x => by
      rw [hU'.1.2 a ha b hb]; rfl
    let f : R'.H ≃ₗᵢ[ℂ] R'.H := LinearIsometryEquiv.ofSurjective
      ⟨(R'.σ (P⁻¹ * P') : R'.H →ₗ[ℂ] R'.H), hU'.2.1 _ hb⟩ fun y => ⟨R'.σ (P'⁻¹ * P) y, by
        show R'.σ (P⁻¹ * P') (R'.σ (P'⁻¹ * P) y) = y
        rw [← hm _ hb _ ha, hba, hU'.1.1]; rfl⟩
    refine ⟨e.trans f, fun g hg x => ?_⟩
    have h3 := he _ (CompanionTheory.LimBd.SchurHpk.forth_mem hP.1 hg) x
    simp only [CompanionTheory.LimBd.SchurHpk.back_forth hP.1] at h3
    show R'.σ (P⁻¹ * P') (e (R.σ g x)) = R'.σ g (R'.σ (P⁻¹ * P') (e x))
    have hag := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ ha).2.2 _ hg
    have e1 : P'⁻¹ * (P * g * P⁻¹) * P' = P'⁻¹ * P * g * (P⁻¹ * P') := by simp only [Matrix.mul_assoc]
    rw [h3, e1, ← hm _ hb _ ((PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hag).2.2 _ hb), ← hm _ hg _ hb,
      ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P * g), ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P), hba, Matrix.one_mul]
  exist := by
    intro k r ε μ μ' R h hR hμ' hg ht
    obtain ⟨P, hP, -⟩ := hR.2
    have h1 : G2.thrS ε < h := lt_of_le_of_lt (le_max_right (thrStar ε) (G2.thrS ε)) ht
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
    obtain ⟨H, _, _, σ, hσ⟩ := G2.discrete_series_exists_large_gap _ ε μ' hμ' h hg (Or.inr (max_lt ((le_max_left _ _).trans_lt h1)
      (by have := (le_max_right _ _).trans_lt h1; linarith)))
    have := hσ.1
    refine ⟨{ H := H, σ := fun g => σ (P * g * P⁻¹) }, hμ', P, hP, ?_⟩
    have e : (fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)) = σ :=
      funext fun g => congrArg σ (CompanionTheory.LimBd.SchurHpk.forth_back hP.1 g)
    show PI.UpqRep.IsDS ε μ' fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)
    rw [e]
    exact hσ

end CompanionTheory.Zuck

end
end

section
open Matrix Finset

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

theorem n1_add_le' {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem n1_single_eq_natAbs {n : ℕ} (s : Fin n) (m : ℤ) : n1 (Pi.single s m) = m.natAbs := by
  unfold n1
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem n1_eZ_eq_card_finset {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

theorem zuckG_of_sm {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (ht : ∀ n, 1 ≤ n → ∀ ε, t n ε ≤ 43 * (n : ℝ) ^ 3)
    (hZ : ZuckSm t) : BranchingSupport.ZuckG := by
  intro k r ε lam q0 R hF ν
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := le_self_pow₀ hn1 (by norm_num)
  have h4 := ht (2 * r + k + 1) (by omega) ε
  constructor
  · intro l hl
    by_cases hln : l ≤ 2 * r + k + 1
    · have hR := hF ν (by omega)
      obtain ⟨h, hg, hok⟩ := hR.gap
      have hl' : (l : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hln
      refine (hZ k r ε _ (R ν) h hok.1 ⟨hR.hc, hR.ds⟩ hg).1 l _ (by linarith [hok.2.1]) (fun a c hac => ?_) fun I => ?_
      · have h5 := (hF (ν + Pi.single c (l : ℤ)) (by
          have := n1_add_le' ν (Pi.single c (l : ℤ))
          rw [n1_single_eq_natAbs, Int.natAbs_natCast] at this
          omega)).hc.1 hac
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hac.ne, add_zero, Int.cast_add,
          Int.cast_natCast] at h5
        obtain ⟨x, hx⟩ := hR.hc.2 a
        obtain ⟨y, hy⟩ := hR.hc.2 c
        have h6 : (l : ℝ) < (x : ℝ) - y := by linarith
        have h7 : (l : ℤ) + 1 ≤ x - y := by exact_mod_cast h6
        have h8 : (l : ℝ) + 1 ≤ (x : ℝ) - y := by exact_mod_cast h7
        linarith
      · have h5 := hF (ν + eZ I.1) (by
          have := n1_add_le' ν (eZ I.1)
          rw [n1_eZ_eq_card_finset, I.2] at this
          omega)
        have e : (fun a => lam a + (((ν + eZ I.1) a : ℤ) : ℝ)) = addSet (fun a => lam a + (ν a : ℝ)) I.1 := by
          funext a
          simp only [addSet, eZ, Pi.add_apply]
          split_ifs <;> push_cast <;> ring
        rw [e] at h5
        exact ⟨h5.hc, h5.ds⟩
    · have : IsEmpty (Sub (2 * r + k + 1) l) := ⟨fun I => hln (by
        rw [← I.2]; exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _))⟩
      exact ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, fun I => isEmptyElim I, fun I => isEmptyElim I,
        fun I => isEmptyElim I, fun I => isEmptyElim I, fun _ _ I => isEmptyElim I, fun I => isEmptyElim I,
        fun I => isEmptyElim I⟩
  · intro hl
    have hR := hF ν (by omega)
    obtain ⟨h, hg, hok⟩ := hR.gap
    refine (hZ k r ε _ (R ν) h hok.1 ⟨hR.hc, hR.ds⟩ hg).2 _ (by linarith [hok.2.1]) fun s => ?_
    have h5 := hF (ν - Pi.single s 1) (by
      have := n1_add_le' ν (Pi.single s (-1))
      rw [n1_single_eq_natAbs, Pi.single_neg, ← sub_eq_add_neg] at this
      exact this.trans hl)
    have e : (fun a => lam a + (((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
      funext a
      simp only [Pi.sub_apply, Pi.single_apply]
      split_ifs <;> push_cast <;> ring
    rw [e] at h5
    exact ⟨h5.hc, h5.ds⟩

end CompanionTheory.Zuck

end
end

section
namespace CompanionTheory.Zuck

theorem zuckerman_gap_small : ZuckSm thr := zuckSm_of zuckerman_ingredients zuckerman_library_bounds

theorem zuckerman_gap : BranchingSupport.ZuckG := zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small

end CompanionTheory.Zuck
end
