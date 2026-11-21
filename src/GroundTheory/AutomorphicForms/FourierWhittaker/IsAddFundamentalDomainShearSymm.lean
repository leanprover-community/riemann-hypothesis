import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff

section
open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

structure IsUSmooth (ϕ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  arch : IsArchSmooth ϕ
  fin : ∃ V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
    ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g
  left : IsLeftInvariant ϕ

theorem IsUSmooth.continuous {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) : Continuous ϕ := by
  obtain ⟨U, hU⟩ := hϕ.fin
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => ϕ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : ϕ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice ϕ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hϕ.arch g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice ϕ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))
      filter_upwards [hmem] with p hp
      exact hU _ p.2 hp.2
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

def rDeriv (Y : archLie K n) (ϕ : AdelicGLn.AdelicGL K n → ℂ) : AdelicGLn.AdelicGL K n → ℂ :=
  fun g => (isExpLieAlgebra K n).rightDeriv Y (archSlice ϕ g) 1

theorem rDeriv_eq_uActFun (Y : archLie K n) {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsArchSmooth ϕ) :
    rDeriv Y ϕ = uActFun (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie Y))
      ⟨ϕ, hϕ⟩ := by
  funext g
  rw [← coe_uAction, uAction_ι_apply]
  rfl

theorem archSlice_mul_finEmb {ϕ : AdelicGLn.AdelicGL K n → ℂ} {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) (g : AdelicGLn.AdelicGL K n) {v} (hv : v ∈ V) :
    archSlice ϕ (g * finEmb K n v) = archSlice ϕ g := by
  funext x
  simp only [archSlice_apply]
  rw [mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, hV _ v hv]

theorem IsUSmooth.rDeriv_smooth {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) (Y : archLie K n) :
    IsUSmooth (rDeriv Y ϕ) where
  arch := by
    rw [rDeriv_eq_uActFun Y hϕ.arch]
    exact uActFun_mem _ _
  fin := by
    obtain ⟨V, hV⟩ := hϕ.fin
    exact ⟨V, fun g v hv => by simp only [rDeriv, archSlice_mul_finEmb hV g hv]⟩
  left γ g := by
    simp only [rDeriv]
    congr 1
    funext x
    simp only [archSlice_apply, mul_assoc, hϕ.left γ]

def oneParam (Y : archLie K n) (s : ℝ) : AdelicGLn.AdelicGL K n :=
  infEmb K n ((isExpLieAlgebra K n).expG (s • Y))

theorem oneParam_add (Y : archLie K n) (s r : ℝ) :
    oneParam Y (s + r) = oneParam Y s * oneParam Y r := by
  rw [oneParam, oneParam, oneParam, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [IsExpLieAlgebra.coe_expG, Subgroup.coe_mul, Units.val_mul, add_smul,
    Submodule.coe_add, Submodule.coe_smul]
  exact exp_add_of_commute' ℝ ((Commute.refl (Y : ArchMatrix K n)).smul_left s |>.smul_right r)

theorem oneParam_zero (Y : archLie K n) : oneParam Y 0 = 1 := by
  simp [oneParam]

theorem continuous_oneParam (Y : archLie K n) : Continuous (oneParam Y) :=
  continuous_infEmb.comp ((isExpLieAlgebra K n).continuous_expG.comp
    (continuous_id.smul continuous_const))

theorem IsUSmooth.hasDerivAt {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    (Y : archLie K n) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s : ℝ => ϕ (g * oneParam Y s)) (rDeriv Y ϕ g) 0 := by
  have := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (hϕ.arch g) Y 1
  have h1 : (fun t : ℝ => archSlice ϕ g (1 * (isExpLieAlgebra K n).expG (t • Y))) =
      fun s => ϕ (g * oneParam Y s) := by
    funext s; simp only [one_mul, archSlice_apply, oneParam]
  rw [h1] at this
  exact this

theorem hasDerivAt_stepCoeff (k : ℕ) {F F' : AdelicGLn.AdelicGL K n → ℂ} (hF : Continuous F)
    (hF' : Continuous F') {e : ℝ → AdelicGLn.AdelicGL K n} (he : Continuous e)
    (hadd : ∀ s r, e (s + r) = e s * e r) (he0 : e 0 = 1)
    (hd : ∀ g, HasDerivAt (fun s => F (g * e s)) (F' g) 0) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s => stepCoeff k F (g * e s)) (stepCoeff k F' g) 0 := by
  set χ : (Fin k → 𝔸[K]) → ℂ := fun x => (GroundTheory.Global.adelicChar K (-pair (lastVec k) x) : ℂ)
  have hχ : Continuous χ := continuous_adelicChar_neg_pair _
  set μ := (vecMeasure K (Fin k)).restrict (vecDomain K (Fin k))
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hcF' : Continuous fun q : (Fin k → 𝔸[K]) × ℝ => F' (colGL k q.1 * (g * e q.2)) :=
    hF'.comp (((continuous_colGL k).comp continuous_fst).mul
      (continuous_const.mul (he.comp continuous_snd)))
  obtain ⟨M, hM⟩ := ((isCompact_closure_vecDomain (K := K) (ι := Fin k)).prod
    (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hcF'.continuousOn
  have hcs : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F (colGL k x * (g * e s)) * χ x :=
    fun s => (hF.comp ((continuous_colGL k).mul continuous_const)).mul hχ
  have hcs' : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F' (colGL k x * (g * e s)) * χ x :=
    fun s => (hF'.comp ((continuous_colGL k).mul continuous_const)).mul hχ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s x => F (colGL k x * (g * e s)) * χ x)
    (F' := fun s x => F' (colGL k x * (g * e s)) * χ x)
    (bound := fun _ => M) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => (hcs s).aestronglyMeasurable)
    (((hcs 0).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure)
    (hcs' 0).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_vecDomain).2 (ae_of_all _ fun x hx s hs => by
      simp only [norm_mul, χ, Circle.norm_coe, mul_one]
      exact hM (x, s) ⟨subset_closure hx, Metric.ball_subset_closedBall hs⟩))
    (integrable_const M)
    (ae_of_all _ fun x s _ => by
      have h0 := hd (colGL k x * (g * e s))
      have h0' : HasDerivAt (fun r : ℝ => F (colGL k x * (g * e s) * e r))
          (F' (colGL k x * (g * e s))) (s + -s) := by rw [add_neg_cancel]; exact h0
      have h1 := h0'.comp_add_const s (-s)
      have h2 : (fun r : ℝ => F (colGL k x * (g * e s) * e (r + -s))) =
          fun r => F (colGL k x * (g * e r)) := by
        funext r
        rw [mul_assoc, mul_assoc, ← hadd]
        congr 4
        ring
      rw [h2] at h1
      exact h1.mul_const (χ x))
  have h2 := hmain.2
  simp only [he0, mul_one] at h2
  exact h2

theorem partialWhittakerCoeff_continuous {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) (m : ℕ) :
    Continuous (partialWhittakerCoeff ϕ m) := by
  induction m with
  | zero => exact hϕ
  | succ m ih => exact continuous_stepCoeff _ ih

theorem hasDerivAt_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    (Y : archLie K n) (k : ℕ) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s => partialCoeff ϕ k (g * oneParam Y s)) (partialCoeff (rDeriv Y ϕ) k g) 0 := by
  unfold partialCoeff
  induction n - k generalizing g with
  | zero => exact hϕ.hasDerivAt Y g
  | succ m ih =>
    exact hasDerivAt_stepCoeff _ (partialWhittakerCoeff_continuous hϕ.continuous m)
      (partialWhittakerCoeff_continuous (hϕ.rDeriv_smooth Y).continuous m) (continuous_oneParam Y)
      (oneParam_add Y) (oneParam_zero Y) ih g

theorem exp_smul_of_mul_self_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {E : 𝔸} (hE : E * E = 0) (s : ℝ) :
    NormedSpace.exp (s • E) = 1 + s • E := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  simp only
  rw [tsum_eq_sum (s := Finset.range 2) (fun m hm => ?_)]
  · simp [Finset.sum_range_succ]
  · have h2 : 2 ≤ m := by simp at hm; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h2
    rw [pow_add, sq, smul_mul_smul_comm, hE, smul_zero, zero_mul, smul_zero]

def dirMat (k : ℕ) (p : Fin k × BIdx K) : ArchMatrix K n :=
  Matrix.of fun a b => if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0

theorem dirMat_apply (k : ℕ) (p : Fin k × BIdx K) (a b : Fin n) :
    (dirMat k p : Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
      if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0 := rfl

theorem dirMat_mul_self (k : ℕ) (p : Fin k × BIdx K) :
    dirMat (n := n) k p * dirMat k p = 0 := by
  let M : Matrix (Fin n) (Fin n) (mixedSpace K) :=
    Matrix.of fun a b => if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0
  have h : M * M = 0 := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [M, Matrix.of_apply]
    split_ifs with h1 h2 <;> first | (exfalso; have := p.1.2; omega) | simp
  exact h

def archPt (g : AdelicGLn.AdelicGL K n) : archGroup K n :=
  archEquiv K n (AdelicGLn.prodEquiv K n g).1

def dirY (k : ℕ) (g : AdelicGLn.AdelicGL K n) (p : Fin k × BIdx K) : archLie K n :=
  ⟨(((((archPt g)⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) * dirMat k p *
    (((archPt g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)), Submodule.mem_top⟩

theorem expG_smul_dirY (k : ℕ) (g : AdelicGLn.AdelicGL K n) (p : Fin k × BIdx K) (s : ℝ) :
    (isExpLieAlgebra K n).expG (s • dirY k g p) =
      (archPt g)⁻¹ * (isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩) *
        archPt g := by
  apply Subtype.ext
  apply Units.ext
  simp only [IsExpLieAlgebra.coe_expG, Submodule.coe_smul, dirY, Subgroup.coe_mul, Units.val_mul,
    Subgroup.coe_inv]
  set u : (ArchMatrix K n)ˣ := ((archPt g : archGroup K n) : (ArchMatrix K n)ˣ)
  set E := dirMat (n := n) k p
  have hE : E * E = 0 := dirMat_mul_self k p
  have hY : ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u *
      (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) = 0 := by
    rw [show ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u *
        (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) =
        ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * (E * (u * ((u⁻¹ : (ArchMatrix K n)ˣ) :
          ArchMatrix K n)) * E) * u by noncomm_ring, Units.mul_inv, mul_one, hE, mul_zero, zero_mul]
  rw [exp_smul_of_mul_self_eq_zero hY, exp_smul_of_mul_self_eq_zero hE, mul_add, add_mul, mul_one,
    Units.inv_mul, mul_smul_comm, smul_mul_assoc]

theorem infEmb_mul_eq (g : AdelicGLn.AdelicGL K n) (X : archGroup K n) :
    infEmb K n X * g = g * infEmb K n ((archPt g)⁻¹ * X * archPt g) := by
  have hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g :=
    infEmb_mul_finEmb g
  set a := archPt g
  set f := (AdelicGLn.prodEquiv K n g).2
  rw [← hg, mul_assoc (infEmb K n a) (finEmb K n f), ← infEmb_mul_finEmb_comm, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul, show a * (a⁻¹ * X * a) = X * a by group]

theorem infEmb_expG_dirMat (k : ℕ) (hk : k < n) (p : Fin k × BIdx K) (s : ℝ) :
    infEmb K n ((isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩)) =
      colGL k (torusPt (Pi.single p s)) := by
  set v : Fin k → 𝔸[K] := torusPt (Pi.single p s)
  have hv1 : ∀ i : Fin k, GroundTheory.Global.homeomorphMixedSpace K (v i).1 =
      if i = p.1 then s • latticeBasis K p.2 else 0 := by
    intro i
    show GroundTheory.Global.homeomorphMixedSpace K (ofCoord fun j => (Pi.single p s : Fin k × BIdx K → ℝ) (i, j)) = _
    rw [homeomorphMixedSpace_ofCoord]
    by_cases hi : i = p.1
    · subst hi
      rw [if_pos rfl, Finset.sum_eq_single p.2]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne (fun h => hj (by rw [← h])), zero_smul]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.single_eq_of_ne (fun h => hi (by rw [← h])), zero_smul]
  have hv2 : ∀ i : Fin k, (v i).2 = 0 := fun i => rfl
  have hfin : (AdelicGLn.prodEquiv K n (colGL k v)).2 = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_snd]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]
    split_ifs <;> first | rfl | simp_all
  have hinf : archEquiv K n (AdelicGLn.prodEquiv K n (colGL k v)).1 =
      (isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩) := by
    apply Subtype.ext
    apply Units.ext
    rw [IsExpLieAlgebra.coe_expG]
    simp only [Submodule.coe_smul]
    rw [exp_smul_of_mul_self_eq_zero (dirMat_mul_self k p)]
    have hentry : ∀ a b : Fin n, ((1 + s • dirMat k p : ArchMatrix K n) :
        Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
        (if a = b then 1 else 0) + s • (dirMat k p : Matrix (Fin n) (Fin n) (mixedSpace K)) a b :=
      fun a b => rfl
    refine Matrix.ext fun a b => ?_
    rw [hentry]
    show archMatrixEquiv K n ((AdelicGLn.prodEquiv K n (colGL k v)).1 :
      Matrix (Fin n) (Fin n) _) a b = _
    rw [archMatrixEquiv_apply, AdelicGLn.prodEquiv_apply_fst, dirMat_apply]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply]
    have hp := p.1.2
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, if_neg (by omega), smul_zero, add_zero]
      exact map_one _
    · rw [if_neg hab, if_neg hab, zero_add]
      by_cases hlt : a < b
      · rw [dif_pos hlt]
        by_cases hbk : b.val = k
        · rw [dif_pos hbk, ← GroundTheory.Global.homeomorphMixedSpace_apply, hv1]
          by_cases ha : a.val = p.1.val
          · rw [if_pos (Fin.ext ha), if_pos ⟨ha, hbk⟩]
          · rw [if_neg (fun h => ha (by rw [← h])), if_neg (fun h => ha h.1), smul_zero]
        · rw [dif_neg hbk, if_neg (fun h => hbk h.2), smul_zero]
          exact map_zero _
      · rw [dif_neg hlt, if_neg (fun h => hlt (by rw [Fin.lt_def]; omega)), smul_zero]
        exact map_zero _
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_infEmb, ← hinf, ContinuousMulEquiv.symm_apply_apply, ← hfin]

theorem colGL_torusPt_single_mul (k : ℕ) (hk : k < n) (g : AdelicGLn.AdelicGL K n)
    (p : Fin k × BIdx K) (s : ℝ) :
    colGL k (torusPt (Pi.single p s)) * g = g * oneParam (dirY k g p) s := by
  rw [oneParam, expG_smul_dirY, ← infEmb_expG_dirMat k hk, infEmb_mul_eq]

end FourierWhittaker

end

end GroundTheory.Automorphic
end

section
open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem stepCoeff_mul_right (k : ℕ) (F : AdelicGLn.AdelicGL K n → ℂ) (g h : AdelicGLn.AdelicGL K n) :
    stepCoeff k F (g * h) = stepCoeff k (fun y => F (y * h)) g := by
  simp only [stepCoeff, mul_assoc]

theorem partialCoeff_mul_right (ϕ : AdelicGLn.AdelicGL K n → ℂ) (k : ℕ) (g h : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (g * h) = partialCoeff (fun y => ϕ (y * h)) k g := by
  unfold partialCoeff
  induction n - k generalizing g with
  | zero => rfl
  | succ m ih =>
    simp only [partialWhittakerCoeff]
    rw [stepCoeff_mul_right]
    congr 1
    funext y
    exact ih y

theorem partialCoeff_mul_finEmb {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) (k : ℕ) (g : AdelicGLn.AdelicGL K n)
    {v : AdelicGLn.FiniteAdelicGL K n} (hv : v ∈ V) :
    partialCoeff ϕ k (g * finEmb K n v) = partialCoeff ϕ k g := by
  rw [partialCoeff_mul_right]
  congr 2
  funext y
  exact hV y v hv

def iterDeriv (k : ℕ) (g : AdelicGLn.AdelicGL K n) (ϕ : AdelicGLn.AdelicGL K n → ℂ) :
    List (Fin k × BIdx K) → AdelicGLn.AdelicGL K n → ℂ
  | [] => ϕ
  | p :: l => rDeriv (dirY k g p) (iterDeriv k g ϕ l)

theorem IsUSmooth.iterDeriv {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) (k : ℕ)
    (g : AdelicGLn.AdelicGL K n) : ∀ l, IsUSmooth (FourierWhittaker.iterDeriv k g ϕ l)
  | [] => hϕ
  | p :: l => (IsUSmooth.iterDeriv hϕ k g l).rDeriv_smooth _

theorem hasSum_vecCoeff_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n)
    (hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * g) =
          partialCoeff ϕ (k + 1) (colGL k x * g)) :
    HasSum (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) (partialCoeff ϕ (k + 1) g) := by
  classical
  set F : List (Fin k × BIdx K) → (Fin k → 𝔸[K]) → ℂ :=
    fun l x => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g)
  have hsm := hϕ.iterDeriv k g
  have hc : ∀ l, Continuous (F l) := fun l =>
    (continuous_partialCoeff (hsm l).continuous _).comp ((continuous_colGL k).mul continuous_const)
  have hper : ∀ l, ∀ ξ ∈ vecLattice K (Fin k), ∀ x, F l (ξ + x) = F l x := by
    intro l ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    simp only [F]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL (hsm l).left hk]
  have hd : ∀ l p x, HasDerivAt (fun s : ℝ => F l (x + torusPt (Pi.single p s))) (F (p :: l) x) 0 := by
    intro l p x
    have h := hasDerivAt_partialCoeff (hsm l) (dirY k g p) (k + 1) (colGL k x * g)
    have e : (fun s : ℝ => F l (x + torusPt (Pi.single p s))) =
        fun s => partialCoeff (iterDeriv k g ϕ l) (k + 1) (colGL k x * g * oneParam (dirY k g p) s) := by
      funext s
      simp only [F]
      rw [colGL_add, mul_assoc, colGL_torusPt_single_mul k hk, mul_assoc]
    rw [e]
    exact h
  have hsum := summable_vecCoeff_of_deriv F hc hper (fun x z hz => hfin x z hz) hd
  have hip : IsIntegralPeriodic (F []) := ⟨hc [], hper [], fun x z hz => hfin x z hz⟩
  have := hip.hasSum_vecCoeff hsum 0
  simp only [pair_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at this
  convert this using 1
  · rfl
  · show partialCoeff ϕ (k + 1) g = partialCoeff ϕ (k + 1) (colGL k 0 * g)
    rw [colGL_zero, one_mul]

theorem exists_lastRow_eq {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin k) K, Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) = ξ := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push Not at h; exact hξ (funext h)
  have hk : 0 < k := Fin.pos i0
  set last : Fin k := ⟨k - 1, by omega⟩
  set σ := Equiv.swap i0 last
  set M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun r c => if r = last then ξ (σ c) else if r = c then 1 else 0
  have hM : M.IsLowerTriangular := by
    intro r c hrc
    have hrc' : r < c := hrc
    have hr : r ≠ last := by
      intro h; subst h; have := c.2; rw [Fin.lt_def] at hrc'; simp [last] at hrc'; omega
    simp only [M, Matrix.of_apply, if_neg hr, if_neg (ne_of_lt hrc')]
  have hdetM : M.det = ξ i0 := by
    rw [Matrix.det_of_isLowerTriangular _ hM, Finset.prod_eq_single last]
    · simp [M, σ]
    · intro r _ hr
      simp [M, hr]
    · simp
  set γM := M.submatrix id σ
  have hdet : γM.det ≠ 0 := by
    rw [Matrix.det_permute', hdetM]
    exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]) hi0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γM hdet, funext fun c => ?_⟩
  rw [vecMul_lastVec _ _ hk]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, γM, M, last, σ]

def rowCompletion {k : ℕ} (ξ : Fin k → K) : GL (Fin k) K :=
  haveI := Classical.propDecidable (ξ ≠ 0)
  if h : ξ ≠ 0 then (exists_lastRow_eq h).choose else 1

theorem vecMul_rowCompletion {k : ℕ} {ξ : Fin k → K} (hξ : ξ ≠ 0) :
    Matrix.vecMul (lastVec k) ((rowCompletion ξ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = ξ := by
  unfold rowCompletion
  rw [dif_pos hξ]
  exact (exists_lastRow_eq hξ).choose_spec

theorem partialCoeff_blockGL_eq_of_vecMul_eq {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsLeftInvariant ϕ) {k : ℕ} (hk : k ≤ n) {γ γ' : GL (Fin k) K}
    (h : Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K) =
      Matrix.vecMul (lastVec k) (γ' : Matrix (Fin k) (Fin k) K)) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ') * g) =
      partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk γ) * g) := by
  have hl : IsLastRowUnit (((γ' * γ⁻¹ : GL (Fin k) K)) : Matrix (Fin k) (Fin k) K) := by
    unfold IsLastRowUnit
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h, Matrix.vecMul_vecMul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have : γ' = (γ' * γ⁻¹) * γ := by group
  rw [this, map_mul, map_mul, mul_assoc]
  exact partialCoeff_diagonal_blockGL hϕ _ k rfl hk _ (Or.inl hl) _

def scalarGL (k : ℕ) : Kˣ →* GL (Fin k) K := Units.map (Matrix.scalar (Fin k) : K →+* _).toMonoidHom

theorem coe_scalarGL (k : ℕ) (u : Kˣ) :
    ((scalarGL k u : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = Matrix.scalar (Fin k) (u : K) := rfl

theorem matVec_scalar {k : ℕ} (u : K) (x : Fin k → 𝔸[K]) :
    matVec (Matrix.scalar (Fin k) u) x = fun i => algebraMap K 𝔸[K] u * x i := by
  funext i
  rw [matVec_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

theorem vecMul_scalar {k : ℕ} (ξ : Fin k → K) (u : K) :
    Matrix.vecMul ξ (Matrix.scalar (Fin k) u) = u • ξ := by
  funext c
  simp [Matrix.vecMul, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

theorem colGL_finiteAdeleInr (k : ℕ) (w : Fin k → FiniteAdeleRing (𝓞 K) K) :
    colGL (n := n) k (fun i => GroundTheory.Global.finiteAdeleInr (w i)) = finEmb K n (colGL k w) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]
    split_ifs <;> rfl
  · apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_snd]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs <;> rfl

theorem finEmb_mul_eq (g : AdelicGLn.AdelicGL K n) (c : AdelicGLn.FiniteAdelicGL K n) :
    finEmb K n c * g = g * finEmb K n ((AdelicGLn.prodEquiv K n g).2⁻¹ * c *
      (AdelicGLn.prodEquiv K n g).2) := by
  have hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g :=
    infEmb_mul_finEmb g
  set a := archPt g
  set f := (AdelicGLn.prodEquiv K n g).2
  rw [← hg, ← mul_assoc, ← infEmb_mul_finEmb_comm, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
    show c * f = f * (f⁻¹ * c * f) by group]

theorem continuous_colGL_fin (k : ℕ) :
    Continuous fun w : Fin k → FiniteAdeleRing (𝓞 K) K => (colGL (n := n) k w : GL (Fin n) _) := by
  have hc : ∀ (a b : Fin n), Continuous fun x : Fin k → FiniteAdeleRing (𝓞 K) K =>
      uMat (colX (n := n) k x) a b := by
    intro a b
    simp only [uMat_apply, colX_apply]
    by_cases h1 : a = b
    · simp only [h1, if_true]; exact continuous_const
    · simp only [h1, if_false]
      by_cases h2 : a < b
      · simp only [h2, dite_true]
        by_cases h3 : b.val = k
        · simp only [h3, dite_true]; exact continuous_apply _
        · simp only [h3, dite_false]; exact continuous_const
      · simp only [h2, dite_false]; exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => hc a b, ?_⟩
  have : (fun x : Fin k → FiniteAdeleRing (𝓞 K) K => (((colGL (n := n) k x)⁻¹ : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _)) = fun x => uMat (colX (n := n) k (-x)) := by
    funext x; rw [← colGL_neg]; rfl
  rw [this]
  exact continuous_pi fun a => continuous_pi fun b => (hc a b).comp continuous_neg

theorem exists_integer_colGL_mem (k : ℕ) (V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n))
    (f : AdelicGLn.FiniteAdelicGL K n) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∀ z : Fin k → FiniteAdeleRing (𝓞 K) K,
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        f⁻¹ * colGL k (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K δ) *
          z i) * f ∈ V := by
  set Θ : (Fin k → FiniteAdeleRing (𝓞 K) K) → AdelicGLn.FiniteAdelicGL K n :=
    fun w => f⁻¹ * colGL k w * f
  have hΘ : Continuous Θ := (continuous_const.mul (continuous_colGL_fin k)).mul continuous_const
  have h0 : Θ 0 = 1 := by simp [Θ, colGL_zero]
  have hW : Θ ⁻¹' (V : Set _) ∈ 𝓝 (0 : Fin k → FiniteAdeleRing (𝓞 K) K) :=
    hΘ.continuousAt.preimage_mem_nhds (by rw [h0]; exact V.isOpen.mem_nhds (one_mem V))
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := Filter.iInter_mem.2 ht
  obtain ⟨δ, hδ, hδU⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hU
  refine ⟨δ, hδ, fun z hz => hIt fun i _ => ?_⟩
  exact Set.mem_iInter.1 (hδU (z i) (hz i)) i

theorem hasSum_partialCoeff_of_vecCoeff_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    {k : ℕ} (hk : k < n)
    (hcusp : ∀ g, vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0)
    (g : AdelicGLn.AdelicGL K n) :
    HasSum (fun ξ : {ξ : Fin k → K // ξ ≠ 0} =>
        partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion ξ.1)) * g))
      (partialCoeff ϕ (k + 1) g) := by
  classical
  obtain ⟨V, hV⟩ := hϕ.fin
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) =
      AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) *
        colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  have hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) *
          (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) =
          partialCoeff ϕ (k + 1) (colGL k x *
            (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)) := by
    intro x z hz
    have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
          (algebraMap (𝓞 K) K δ) * z i) := by
      funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
    rw [colGL_add, mul_assoc (colGL k x),
      ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
      colGL_finiteAdeleInr, mul_assoc (AdelicGLn.diagonal K n _), finEmb_mul_eq, ← mul_assoc,
      ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have H := hasSum_vecCoeff_partialCoeff hϕ hk _ hfin
  rw [partialCoeff_succ_diagonal_blockGL hϕ.left hk] at H
  have hsupp : Function.support (vecCoeff fun x => partialCoeff ϕ (k + 1) (colGL k x *
      (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g))) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    by_contra h0
    apply hξ
    have : ξ = 0 := by simpa using h0
    rw [this]
    exact hcusp _
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at H
  set e : {ξ : Fin k → K // ξ ≠ 0} ≃ {ξ : Fin k → K // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(u⁻¹ : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u : Kˣ) • ·) h)⟩
      invFun := fun ξ => ⟨(u : Kˣ) • ξ.1, fun h => ξ.2 (by simpa using congrArg ((u⁻¹ : Kˣ) • ·) h)⟩
      left_inv := fun ξ => Subtype.ext (by simp)
      right_inv := fun ξ => Subtype.ext (by simp) }
  rw [← e.hasSum_iff]
  refine H.congr_fun fun ξ => ?_
  show partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le (rowCompletion (e ξ).1)) * g) = _
  have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hϕ.left hk (rowCompletion ξ.1)
    (AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) * g)
  rw [vecMul_rowCompletion ξ.2] at h1
  rw [Function.comp_apply, ← h1, ← mul_assoc, ← map_mul, ← map_mul]
  refine partialCoeff_blockGL_eq_of_vecMul_eq hϕ.left hk.le ?_ g
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_rowCompletion ξ.2, coe_scalarGL, vecMul_scalar,
    vecMul_rowCompletion (e ξ).2]
  rfl

end FourierWhittaker

end

end GroundTheory.Automorphic
end

section
open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem setIntegral_vecDomain_sum {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]
    (e : ι ≃ ι₁ ⊕ ι₂) {h : (ι → 𝔸[K]) → ℂ} (hc : Continuous h) :
    ∫ z in vecDomain K ι, h z ∂vecMeasure K ι =
      ∫ x in vecDomain K ι₁, ∫ y in vecDomain K ι₂, h (fun i => Sum.elim x y (e i))
        ∂vecMeasure K ι₂ ∂vecMeasure K ι₁ := by
  let E : (ι → 𝔸[K]) ≃ᵐ (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) :=
    (MeasurableEquiv.piCongrLeft (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]) e).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => 𝔸[K]))
  have hE : MeasurePreserving E (vecMeasure K ι) ((vecMeasure K ι₁).prod (vecMeasure K ι₂)) :=
    (measurePreserving_piCongrLeft (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K) e).trans
      (measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => GroundTheory.Global.adeleMeasure K))
  have hEsymm : ∀ p, E.symm p = fun i => Sum.elim p.1 p.2 (e i) := by
    intro p
    funext i
    simp [E, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft,
      Equiv.sumPiEquivProdPi]
    generalize e i = j
    cases j <;> rfl
  have hpre : E ⁻¹' (vecDomain K ι₁ ×ˢ vecDomain K ι₂) = vecDomain K ι := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ i
      have hz : z = E.symm (E z) := (E.symm_apply_apply z).symm
      rw [hz, hEsymm]
      show ((E z).1 ⊕ᵥ (E z).2) (e i) ∈ _
      rcases e i with a | b
      · exact h1 a
      · exact h2 b
    · intro h
      refine ⟨fun a => ?_, fun b => ?_⟩
      · have := h (e.symm (Sum.inl a)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
      · have := h (e.symm (Sum.inr b)); simpa [E, MeasurableEquiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft, Equiv.sumPiEquivProdPi] using this
  rw [← hpre]
  have h1 := hE.setIntegral_preimage_emb E.measurableEmbedding (fun p => h (E.symm p))
    (vecDomain K ι₁ ×ˢ vecDomain K ι₂)
  simp only [E.symm_apply_apply] at h1
  rw [h1, setIntegral_prod]
  · simp only [hEsymm]
  · have hcont : Continuous fun p : (ι₁ → 𝔸[K]) × (ι₂ → 𝔸[K]) => h (E.symm p) := by
      simp_rw [hEsymm]
      refine hc.comp (continuous_pi fun i => ?_)
      rcases e i with a | b
      · exact (continuous_apply a).comp continuous_fst
      · exact (continuous_apply b).comp continuous_snd
    exact (hcont.continuousOn.integrableOn_compact ((isCompact_closure_vecDomain (K := K)
      (ι := ι₁)).prod (isCompact_closure_vecDomain (K := K) (ι := ι₂)))).mono_set
      (Set.prod_mono subset_closure subset_closure)

variable {n : ℕ}

abbrev GePos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.2.val}

def extGe {R : Type*} [Zero R] {k : ℕ} (Z : GePos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.2.val then Z ⟨p, h⟩ else 0

def supSum (m : ℕ) (X : Pos n → 𝔸[K]) : 𝔸[K] :=
  ∑ p ∈ Finset.univ.filter (fun p : Pos n => p.1.2.val = p.1.1.val + 1 ∧ m ≤ p.1.2.val), X p

theorem supSum_add (m : ℕ) (X Y : Pos n → 𝔸[K]) : supSum m (X + Y) = supSum m X + supSum m Y := by
  simp [supSum, Finset.sum_add_distrib]

theorem supSum_zero (m : ℕ) : supSum m (0 : Pos n → 𝔸[K]) = 0 := by simp [supSum]

theorem supSum_colX_succ (k : ℕ) (x : Fin k → 𝔸[K]) : supSum (k + 1) (colX (n := n) k x) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [colX_apply, dif_neg (by omega)]

theorem supSum_colX (k : ℕ) (hk : k < n) (x : Fin k → 𝔸[K]) :
    supSum k (colX (n := n) k x) = pair (lastVec k) x := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [supSum]
    simp only [pair, Finset.univ_eq_empty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [colX_apply, dif_neg]
    have := p.2
    rw [Fin.lt_def] at this
    omega
  · have hmem : ∀ p : Pos n, (p.1.2.val = p.1.1.val + 1 ∧ k ≤ p.1.2.val) → p.1.2.val = k →
        p = ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩ := by
      intro p h1 h2
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
    rw [supSum, Finset.sum_eq_single ⟨(⟨k - 1, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; simp; omega⟩]
    · rw [colX_apply, dif_pos rfl, pair, Finset.sum_eq_single ⟨k - 1, by omega⟩]
      · simp [lastVec]; congr 1; omega
      · intro i _ hi
        rw [lastVec, if_neg (fun h => hi (Fin.ext (by show i.val = k - 1; omega))), map_zero, zero_mul]
      · simp
    · intro p hp hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [colX_apply, dif_neg (fun h => hne (hmem p hp h))]
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> (try simp) <;> omega

theorem extGe_eq_zero {R : Type*} [Zero R] {k : ℕ} (Z : GePos n (k + 1) → R) (p : Pos n)
    (hp : p.1.2.val ≤ k) : extGe Z p = 0 := by
  rw [extGe, dif_neg (by omega)]

def colSplit (k : ℕ) (hk : k < n) : GePos n k ≃ Fin k ⊕ GePos n (k + 1) where
  toFun p := if h : p.1.1.2.val = k then
      Sum.inl ⟨p.1.1.1.val, by have := p.1.2; rw [Fin.lt_def] at this; omega⟩
    else Sum.inr ⟨p.1, by have := p.2; omega⟩
  invFun := Sum.elim (fun a => ⟨⟨(⟨a.val, by omega⟩, ⟨k, hk⟩), by rw [Fin.lt_def]; exact a.2⟩,
    le_refl k⟩) (fun q => ⟨q.1, by have := q.2; omega⟩)
  left_inv p := by
    by_cases h : p.1.1.2.val = k
    · simp only [dif_pos h, Sum.elim_inl]
      apply Subtype.ext; apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp [h]
    · simp only [dif_neg h, Sum.elim_inr]
  right_inv q := by
    rcases q with a | q
    · simp
    · have := q.2
      show (if h : q.1.1.2.val = k then _ else _) = _
      rw [dif_neg (show ¬ q.1.1.2.val = k by omega)]
      rfl

theorem extGe_colSplit {R : Type*} [CommRing R] (k : ℕ) (hk : k < n) (x : Fin k → R)
    (y : GePos n (k + 1) → R) :
    extGe (fun i => Sum.elim x y (colSplit k hk i)) = extGe y + colX k x := by
  funext p
  simp only [extGe, colX_apply, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dif_pos h1]
    by_cases h2 : p.1.2.val = k
    · rw [dif_neg (by omega), dif_pos h2, zero_add]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dif_pos h2, Sum.elim_inl]
    · rw [dif_pos (by omega), dif_neg h2, add_zero]
      show Sum.elim x y (colSplit k hk ⟨p, h1⟩) = _
      simp only [colSplit, Equiv.coe_fn_mk, dif_neg h2, Sum.elim_inr]
  · rw [dif_neg h1, dif_neg (by omega), dif_neg (by omega), add_zero]

theorem continuous_extGe {k : ℕ} : Continuous (extGe (n := n) (k := k) (R := 𝔸[K])) := by
  refine continuous_pi fun p => ?_
  simp only [extGe]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_supSum (m : ℕ) : Continuous (supSum (K := K) (n := n) m) :=
  continuous_finsetSum _ fun p _ => continuous_apply p

theorem coe_uGL_inv (X : Pos n → 𝔸[K]) :
    (((uGL X)⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) = (uMat X).adjugate := by
  rw [Matrix.coe_units_inv, coe_uGL, Matrix.inv_def, det_uMat, Ring.inverse_one, one_smul]

theorem continuous_uGL : Continuous fun X : Pos n → 𝔸[K] => (uGL X : GL (Fin n) 𝔸[K]) := by
  have hc : Continuous fun X : Pos n → 𝔸[K] => uMat X := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [uMat_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  simp only [coe_uGL_inv]
  exact hc.matrix_adjugate

def wInt (m : ℕ) (ϕ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) (X : Pos n → 𝔸[K]) : ℂ :=
  ϕ (uGL X * g) * (GroundTheory.Global.adelicChar K (-supSum m X) : ℂ)

theorem continuous_wInt (m : ℕ) {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    (g : AdelicGLn.AdelicGL K n) : Continuous (wInt m ϕ g) :=
  (hϕ.comp (continuous_uGL.mul continuous_const)).mul
    (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum m).neg))

theorem setIntegral_geCols (k : ℕ) (hk : k < n) {H : (Pos n → 𝔸[K]) → ℂ} (hH : Continuous H) :
    ∫ Z in vecDomain K (GePos n k), H (extGe Z) ∂vecMeasure K (GePos n k) =
      ∫ x in vecDomain K (Fin k), ∫ Y in vecDomain K (GePos n (k + 1)),
        H (extGe Y + colX k x) ∂vecMeasure K (GePos n (k + 1)) ∂vecMeasure K (Fin k) := by
  have := setIntegral_vecDomain_sum (colSplit k hk) (hH.comp continuous_extGe)
  simp only [Function.comp_apply, extGe_colSplit] at this
  exact this

theorem partialCoeff_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) :
    ∀ (m k : ℕ), n - k = m → k ≤ n → ∀ g, partialCoeff ϕ k g =
      ∫ Z in vecDomain K (GePos n k), wInt k ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  intro m
  induction m with
  | zero =>
    intro k hkm hk g
    obtain rfl : k = n := by omega
    rw [partialCoeff_self]
    have hz : ∀ Z : GePos k k → 𝔸[K], extGe Z = 0 := fun Z => by
      funext p; rw [extGe, dif_neg (by have := p.1.2.2; omega)]; rfl
    simp only [hz, wInt, uGL_zero, one_mul, supSum_zero, neg_zero, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one]
    rw [setIntegral_const, measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]
  | succ m ih =>
    intro k hkm hk g
    have hkn : k < n := by omega
    rw [setIntegral_geCols k hkn (continuous_wInt k hϕ g), partialCoeff_of_lt ϕ hkn, stepCoeff,
      vecCoeff]
    refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
    rw [ih (k + 1) (by omega) hkn, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun Y => ?_)
    simp only [wInt]
    have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
    have hsup : supSum k (extGe Y) = supSum (k + 1) (extGe Y) := by
      unfold supSum
      refine (Finset.sum_subset (fun p hp => ?_) fun p hp hp' => ?_).symm
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
        exact hY p (by omega)
    have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
      rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
    rw [← mul_assoc (uGL _), hmul, supSum_add, hsup, supSum_colX k hkn x, neg_add,
      AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

theorem vecCoeff_zero_eq_setIntegral {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) {k : ℕ}
    (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ Z in vecDomain K (GePos n k), wInt (k + 1) ϕ g (extGe Z) ∂vecMeasure K (GePos n k) := by
  rw [setIntegral_geCols k hk (continuous_wInt (k + 1) hϕ g), vecCoeff]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [pair, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [partialCoeff_eq_setIntegral hϕ _ (k + 1) rfl hk]
  refine integral_congr_ae (ae_of_all _ fun Y => ?_)
  simp only [wInt]
  have hY : ∀ p : Pos n, p.1.2.val ≤ k → extGe Y p = 0 := fun p hp => extGe_eq_zero Y p hp
  have hmul : uGL (extGe Y) * colGL k x = uGL (extGe Y + colX k x) := Units.ext (by
    rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL]; exact uMat_mul_uMat_colX hY x)
  rw [← mul_assoc (uGL _), hmul, supSum_add, supSum_colX_succ, add_zero]

abbrev LowPos (n k : ℕ) : Type := {p : Pos n // k ≤ p.1.1.val}

def lowSplit (k : ℕ) : GePos n k ≃ LowPos n k ⊕ AutomorphicForm.UPos n k where
  toFun p := if h : k ≤ p.1.1.1.val then Sum.inl ⟨p.1, h⟩
    else Sum.inr ⟨p.1.1, by have := p.2; omega, p.2⟩
  invFun := Sum.elim (fun q => ⟨q.1, by have := q.1.2; have := q.2; rw [Fin.lt_def] at *; omega⟩)
    (fun u => ⟨⟨u.1, by have := u.2; rw [Fin.lt_def]; omega⟩, u.2.2⟩)
  left_inv p := by
    by_cases h : k ≤ p.1.1.1.val
    · simp only [dif_pos h, Sum.elim_inl]
    · simp only [dif_neg h, Sum.elim_inr]
  right_inv q := by
    rcases q with q | u
    · show (if h : k ≤ q.1.1.1.val then _ else _) = _
      rw [dif_pos q.2]
      rfl
    · show (if h : k ≤ u.1.1.val then _ else _) = _
      rw [dif_neg (by have := u.2; omega)]
      rfl

def extLow {R : Type*} [Zero R] {k : ℕ} (B : LowPos n k → R) : Pos n → R :=
  fun p => if h : k ≤ p.1.1.val then B ⟨p, h⟩ else 0

def extU {R : Type*} [Zero R] {k : ℕ} (A : AutomorphicForm.UPos n k → R) : Pos n → R :=
  fun p => if h : p.1.1.val < k ∧ k ≤ p.1.2.val then A ⟨p.1, h⟩ else 0

theorem extGe_lowSplit {R : Type*} [AddCommGroup R] (k : ℕ) (B : LowPos n k → R)
    (A : AutomorphicForm.UPos n k → R) :
    extGe (fun i => Sum.elim B A (lowSplit k i)) = extLow B + extU A := by
  funext p
  simp only [extGe, extLow, extU, Pi.add_apply]
  by_cases h1 : k ≤ p.1.2.val
  · rw [dif_pos h1]
    by_cases h2 : k ≤ p.1.1.val
    · rw [dif_pos h2, dif_neg (by omega), add_zero]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dif_pos h2, Sum.elim_inl]
    · rw [dif_neg h2, dif_pos ⟨by omega, h1⟩, zero_add]
      show Sum.elim B A (lowSplit k ⟨p, h1⟩) = _
      simp only [lowSplit, Equiv.coe_fn_mk, dif_neg h2, Sum.elim_inr]
  · have hp := p.2
    rw [Fin.lt_def] at hp
    rw [dif_neg h1, dif_neg (by omega), dif_neg (by omega), add_zero]

theorem supSum_extU (k : ℕ) (A : AutomorphicForm.UPos n k → 𝔸[K]) :
    supSum (k + 1) (extU A) = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rw [extU, dif_neg (by omega)]

theorem vecCoeff_zero_eq_setIntegral_low {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ)
    {k : ℕ} (hk : k < n) (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 =
      ∫ B in vecDomain K (LowPos n k), (GroundTheory.Global.adelicChar K (-supSum (k + 1) (extLow B)) : ℂ) *
        ∫ A in vecDomain K (AutomorphicForm.UPos n k), ϕ (uGL (extLow B + extU A) * g)
          ∂vecMeasure K (AutomorphicForm.UPos n k) ∂vecMeasure K (LowPos n k) := by
  rw [vecCoeff_zero_eq_setIntegral hϕ hk g]
  have := setIntegral_vecDomain_sum (lowSplit k) ((continuous_wInt (k + 1) hϕ g).comp
    (continuous_extGe (K := K) (n := n) (k := k)))
  simp only [Function.comp_apply, extGe_lowSplit] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_
  simp only [wInt, supSum_add, supSum_extU, add_zero]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun A => ?_)
  ring

end FourierWhittaker

end

end GroundTheory.Automorphic
end

section
open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem existsUnique_triangular {ι : Type*} [Fintype ι] (ord : ι → ℕ)
    {S : (ι → 𝔸[K]) → (ι → 𝔸[K])} (s : ι → (ι → 𝔸[K]) → 𝔸[K]) (hS : ∀ z i, S z i = z i + s i z)
    (hs : ∀ i z z', (∀ j, ord j < ord i → z j = z' j) → s i z = s i z') (y : ι → 𝔸[K]) :
    ∃! g : vecLattice K ι, S (g +ᵥ y) ∈ vecDomain K ι := by
  classical
  set F := GroundTheory.Global.fundamentalSet K
  set A : (ι → K) → ι → 𝔸[K] := fun l i => algebraMap K 𝔸[K] (l i)

  have hex : ∀ N : ℕ, ∃ l : ι → K, ∀ i, ord i < N → S (A l + y) i ∈ F := by
    intro N
    induction N with
    | zero => exact ⟨0, fun i h => absurd h (Nat.not_lt_zero _)⟩
    | succ N ih =>
      obtain ⟨l, hl⟩ := ih
      choose c hc _ using fun i => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (S (A l + y) i)
      set l' : ι → K := fun i => if ord i = N then l i - c i else l i
      have hagree : ∀ i j, ord j < ord i → ord i ≤ N → l' j = l j := by
        intro i j hj hi
        simp only [l', if_neg (show ord j ≠ N by omega)]
      refine ⟨l', fun i hi => ?_⟩
      have hsi : s i (A l' + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, hagree i j hj (by omega)]
      rw [hS, hsi]
      by_cases hN : ord i = N
      · simp only [A, Pi.add_apply, l', if_pos hN, map_sub]
        have := hc i
        rw [hS] at this
        convert this using 1
        simp only [A, Pi.add_apply]
        ring
      · simp only [A, Pi.add_apply, l', if_neg hN]
        have := hl i (by omega)
        rwa [hS] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, ord i < N :=
    ⟨Finset.univ.sup ord + 1, fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  obtain ⟨l, hl⟩ := hex N
  refine ⟨⟨A l, l, rfl⟩, fun i _ => hl i (hN i), ?_⟩

  rintro ⟨_, m, rfl⟩ hm
  have key : ∀ M i, ord i < M → m i = l i := by
    intro M
    induction M with
    | zero => intro i h; exact absurd h (Nat.not_lt_zero _)
    | succ M ih =>
      intro i hi
      have hsi : s i (A m + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, ih j (by omega)]
      have h1 := hm i (mem_univ i)
      have h2 := hl i (hN i)
      change S ((fun i => algebraMap K 𝔸[K] (m i)) + y) i ∈ F at h1
      rw [hS] at h1 h2
      rw [show ((fun i => algebraMap K 𝔸[K] (m i)) + y) = A m + y from rfl, hsi] at h1
      obtain ⟨c, -, hcu⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (y i + s i (A l + y))
      have e1 : -m i = -l i := by
        have a1 := hcu (-m i) (by
          simp only [A, Pi.add_apply] at h1
          convert h1 using 1; rw [map_neg]; ring)
        have a2 := hcu (-l i) (by
          simp only [A, Pi.add_apply] at h2
          convert h2 using 1; rw [map_neg]; ring)
        rw [a1, a2]
      exact neg_injective e1
  refine Subtype.ext (funext fun i => ?_)
  show algebraMap K 𝔸[K] (m i) = algebraMap K 𝔸[K] (l i)
  rw [key N i (hN i)]

variable {n : ℕ}

section Shear

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem blockEntry_eq_of_vanishing {X : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hX : ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → X i j = 0) :
    blockEntry (fun u : UPos n k => X u.1.1 u.1.2) = X := by
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · exact (hX i j h).symm

theorem uMat_extLow_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    uMat (extLow B) i j = 0 := by
  rw [uMat_apply, if_neg (fun h => by subst h; omega), dif_neg (fun h => by rw [Fin.lt_def] at h; omega)]

theorem uMat_extLow_inv_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 := by
  letI : Invertible (uMat (extLow B)) := Units.invertible (uGL (extLow B))
  have hT : (uMat (extLow B)).BlockTriangular (fun c : Fin n => if (c : ℕ) < k then 0 else 1) := by
    intro a b hab
    by_cases ha : (a : ℕ) < k
    · simp only [ha, if_true] at hab
      split_ifs at hab <;> omega
    · by_cases hb : (b : ℕ) < k
      · exact uMat_extLow_apply_of_lt B a b hb (by omega)
      · simp only [ha, hb, if_false] at hab
        omega
  have hTi := Matrix.blockTriangular_inv_of_blockTriangular hT
  rw [Matrix.coe_units_inv, coe_uGL]
  exact hTi (by simp only; rw [if_pos hj, if_neg (by omega)]; norm_num)

theorem blockEntry_mul_vanishing {M : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hM : ∀ i j : Fin n, (j : ℕ) < k → k ≤ (i : ℕ) → M i j = 0) (A : UPos n k → 𝔸[K]) :
    ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → (blockEntry A * M) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [blockEntry_apply]
  split_ifs with h
  · rw [hM c j (by omega) h.2, mul_zero]
  · rw [zero_mul]

def shear : (UPos n k → 𝔸[K]) ≃+ (UPos n k → 𝔸[K]) where
  toFun A u := (blockEntry A * uMat (extLow B)) u.1.1 u.1.2
  invFun Z u := (blockEntry Z * (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) 𝔸[K])) u.1.1 u.1.2
  left_inv A := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dif_pos u.2]
  right_inv Z := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_inv_apply_of_lt B) Z),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dif_pos u.2]
  map_add' A A' := by
    funext u
    simp [blockEntry_add, Matrix.add_mul]

end Shear

section Shear2

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem unipMatrix_mul_uMat_extLow (A : UPos n k → 𝔸[K]) :
    unipMatrix A * uMat (extLow B) = uMat (extLow B + extU (shear B A)) := by
  rw [unipMatrix, Matrix.add_mul, Matrix.one_mul]
  ext i j
  have hv := blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A i j
  rw [Matrix.add_apply, uMat_apply, uMat_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, hv (by omega), add_zero]
  · rw [if_neg hij, if_neg hij]
    by_cases hlt : i < j
    · rw [dif_pos hlt, dif_pos hlt, Pi.add_apply, extU]
      congr 1
      split_ifs with h
      · rfl
      · exact hv h
    · rw [dif_neg hlt, dif_neg hlt, zero_add]
      exact hv (fun h => hlt (by rw [Fin.lt_def]; omega))

theorem continuous_blockEntry :
    Continuous (blockEntry (n := n) (r := k) (R := 𝔸[K])) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_shear : Continuous (shear B) :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem continuous_shear_symm : Continuous (shear B).symm :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem isAddFundamentalDomain_shear_symm :
    IsAddFundamentalDomain (vecLattice K (UPos n k)) ((shear B).symm '' vecDomain K (UPos n k))
      (vecMeasure K (UPos n k)) := by
  classical
  have himg : (shear B).symm '' vecDomain K (UPos n k) = (shear B) ⁻¹' vecDomain K (UPos n k) := by
    ext A
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      simpa using hZ
    · intro h
      exact ⟨shear B A, h, by simp⟩
  rw [himg]
  refine IsAddFundamentalDomain.mk' ((measurableSet_vecDomain.preimage
    (continuous_shear B).measurable).nullMeasurableSet) fun y => ?_
  refine existsUnique_triangular (fun u : UPos n k => u.1.2.val)
    (fun u z => ∑ c ∈ Finset.univ.erase u.1.2, blockEntry z u.1.1 c * uMat (extLow B) c u.1.2)
    (fun z u => ?_) (fun u z z' hzz' => ?_) y
  · show (blockEntry z * uMat (extLow B)) u.1.1 u.1.2 = _
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ u.1.2), blockEntry_apply,
      dif_pos u.2, uMat_apply, if_pos rfl, mul_one]
  · refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hcu : c < u.1.2
    · rw [blockEntry_apply, blockEntry_apply]
      split_ifs with h
      · rw [hzz' ⟨(u.1.1, c), h⟩ (by rw [Fin.lt_def] at hcu; exact hcu)]
      · rfl
    · have hne : c ≠ u.1.2 := Finset.ne_of_mem_erase hc
      have : uMat (extLow B) c u.1.2 = 0 := by
        rw [uMat_apply, if_neg hne, dif_neg (fun h => hcu (by
          rw [Fin.lt_def] at h ⊢; have := Fin.val_injective.ne hne; omega))]
      rw [this, mul_zero, mul_zero]

theorem setIntegral_uGL_extLow_extU {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsLeftInvariant ϕ)
    (g : AdelicGLn.AdelicGL K n) :
    ∫ A in vecDomain K (UPos n k), ϕ (uGL (extLow B + extU A) * g) ∂vecMeasure K (UPos n k) =
      constantTerm k ϕ (uGL (extLow B) * g) := by
  have hrepr : ∀ A, uGL (extLow B + extU A) = unipGL ((shear B).symm A) * uGL (extLow B) := by
    intro A
    refine Units.ext ?_
    rw [Units.val_mul, coe_unipGL, coe_uGL, coe_uGL, unipMatrix_mul_uMat_extLow,
      AddEquiv.apply_symm_apply]
  simp_rw [hrepr, mul_assoc]
  rw [setIntegral_comp_addEquiv (shear B).symm (continuous_shear_symm B) (continuous_shear B)
    (isAddFundamentalDomain_shear_symm B) (f := fun A => ϕ (unipGL A * (uGL (extLow B) * g)))
    fun ξ hξ x => hϕ.unipGL_vadd _ ⟨ξ, hξ⟩ x]
  rfl

end Shear2

theorem vecCoeff_zero_of_isCuspidal {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0 := by
  rw [vecCoeff_zero_eq_setIntegral_low hc hk g]
  refine (setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_).trans (integral_zero _ _)
  rw [setIntegral_uGL_extLow_extU B hl g, hcusp k hk0 hk, mul_zero]

end FourierWhittaker

end

end GroundTheory.Automorphic
end
