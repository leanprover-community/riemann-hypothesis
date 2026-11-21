import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import GroundTheory.AutomorphicForms.CuspidalDiscreteness

section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem mul_centralSection_inv_mem (g : AdelicGLn.AdelicGL K n) :
    g * (centralSection K n (detModule K n g))⁻¹ ∈ normOneGL K n := by
  rw [mem_normOneGL_iff_detModule, map_mul, map_inv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim g 1, Subsingleton.elim (centralSection K 0 _) 1]
    simp
  · rw [detModule_centralSection hn, mul_inv_cancel]

def retract (g : AdelicGLn.AdelicGL K n) : normOneGL K n :=
  ⟨g * (centralSection K n (detModule K n g))⁻¹, mul_centralSection_inv_mem g⟩

theorem coe_retract (g : AdelicGLn.AdelicGL K n) :
    (retract g : AdelicGLn.AdelicGL K n) = g * (centralSection K n (detModule K n g))⁻¹ := rfl

theorem retract_coe (x : normOneGL K n) : retract (x : AdelicGLn.AdelicGL K n) = x := by
  ext1
  rw [coe_retract, (mem_normOneGL_iff_detModule).1 x.2, map_one, inv_one, mul_one]

theorem retract_mul_left (x : normOneGL K n) (g : AdelicGLn.AdelicGL K n) :
    retract ((x : AdelicGLn.AdelicGL K n) * g) = x * retract g := by
  ext1
  rw [coe_retract, Subgroup.coe_mul, coe_retract, map_mul, (mem_normOneGL_iff_detModule).1 x.2,
    one_mul, mul_assoc]

theorem continuous_retract : Continuous (retract (K := K) (n := n)) :=
  continuous_induced_rng.2 (continuous_id.mul
    ((continuous_centralSection.comp continuous_detModule).inv))

theorem retract_mul_finEmb (g : AdelicGLn.AdelicGL K n) {u : AdelicGLn.FiniteAdelicGL K n}
    (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    retract (g * finEmb K n u) = retract g * finOne K n ⟨u, hu⟩ := by
  have h1 : detModule K n (finEmb K n u) = 1 :=
    (mem_normOneGL_iff_detModule).1 (finOne K n ⟨u, hu⟩).2
  ext1
  rw [coe_retract, Subgroup.coe_mul, coe_retract, coe_finOne, map_mul, h1, mul_one, mul_assoc,
    ← centralSection_inv_mul_comm, ← mul_assoc]

def lift (ϕ : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ := ϕ (retract g)

theorem lift_coe (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) :
    lift ϕ (x : AdelicGLn.AdelicGL K n) = ϕ x := by
  rw [lift, retract_coe]

theorem continuous_lift {ϕ : normOneGL K n → ℂ} (hϕ : Continuous ϕ) : Continuous (lift ϕ) :=
  hϕ.comp continuous_retract

theorem isLeftInvariant_lift {ϕ : normOneGL K n → ℂ}
    (hϕ : ∀ γ ∈ Γ₁, ∀ x, ϕ (γ * x) = ϕ x) : IsLeftInvariant (lift ϕ) := by
  intro γ g
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  set γ₁ : normOneGL K n := ⟨AdelicGLn.diagonal K n γ, hγ1⟩
  have hγΓ : γ₁ ∈ Γ₁ := ⟨γ, rfl⟩
  show ϕ (retract ((γ₁ : AdelicGLn.AdelicGL K n) * g)) = ϕ (retract g)
  rw [retract_mul_left, hϕ γ₁ hγΓ]

theorem isCuspidal_lift {ϕ : normOneGL K n → ℂ}
    (hϕ : ∀ r : ℕ, 0 < r → r < n → ∀ x : normOneGL K n,
      ∫ X in unipFundamentalDomain K n r, ϕ (unipOne K n r X * x) ∂unipMeasure K n r = 0) :
    IsCuspidal (lift ϕ) := by
  intro r hr hrn g
  rw [← hϕ r hr hrn (retract g)]
  unfold constantTerm
  refine setIntegral_congr_fun (measurableSet_unipFundamentalDomain (K := K) (n := n) (r := r))
    fun X _ => ?_
  show ϕ (retract ((unipOne K n r X : AdelicGLn.AdelicGL K n) * g)) = _
  rw [retract_mul_left]

def openSubgroupOf (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    OpenSubgroup (AdelicGLn.FiniteAdelicGL K n) where
  toSubgroup := U.map (AdelicGLn.integralFiniteGL K n).subtype
  isOpen' := by
    change IsOpen ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
      Set (AdelicGLn.FiniteAdelicGL K n))
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU

theorem lift_mul_finEmb {ϕ : normOneGL K n → ℂ} {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (hϕ : ∀ u ∈ U, ∀ x, ϕ (x * finOne K n u) = ϕ x) (g : AdelicGLn.AdelicGL K n)
    (v : AdelicGLn.FiniteAdelicGL K n) (hv : v ∈ openSubgroupOf U hU) :
    lift ϕ (g * finEmb K n v) = lift ϕ g := by
  obtain ⟨u, hu, rfl⟩ := hv
  show ϕ (retract (g * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n))) = ϕ (retract g)
  rw [retract_mul_finEmb g u.2]
  exact hϕ u hu _

theorem uGL_mem_normOneGL (X : Pos n → 𝔸[K]) :
    (uGL X : AdelicGLn.AdelicGL K n) ∈ normOneGL K n := by
  have h1 : AdelicGLn.det K n (uGL X) = 1 :=
    Units.ext (by rw [AdelicGLn.coe_det, coe_uGL, det_uMat, Units.val_one])
  rw [mem_normOneGL, h1, map_one]
  rfl

def uOne (X : Pos n → 𝔸[K]) : normOneGL K n := ⟨uGL X, uGL_mem_normOneGL X⟩

@[simp] theorem coe_uOne (X : Pos n → 𝔸[K]) :
    (uOne X : AdelicGLn.AdelicGL K n) = uGL X := rfl

def whittakerOne (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) : ℂ :=
  ∫ X in vecDomain K (Pos n), ϕ (uOne X * x) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ)
    ∂vecMeasure K (Pos n)

theorem whittaker_lift (ϕ : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    whittaker (lift ϕ) g = whittakerOne ϕ (retract g) := by
  unfold whittaker whittakerOne
  refine setIntegral_congr_fun measurableSet_vecDomain fun X _ => ?_
  show ϕ (retract ((uOne X : AdelicGLn.AdelicGL K n) * g)) * _ = _
  rw [retract_mul_left]

def IsSmoothTest (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) : Prop :=
  ∃ (ν : Measure (ArchUnits K n)) (_ : ν.IsHaarMeasure) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (β : ArchMatrix K n → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ),
    f = archConv ν hβ.continuous hβc hβu (finAvg U hU g)

theorem IsSmoothTest.exists_finOne_mul {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsSmoothTest f) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      ∀ u ∈ U, ∀ x, f (finOne K n u * x) = f x := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  refine ⟨U, hU, fun u hu x => ?_⟩
  rw [archConv_apply, archConv_apply]
  exact archConvFun_finOne_mul _ _ u (fun y => finAvgFun_finOne_mul U hU g ⟨u, hu⟩ y) x

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rconv_mul_finOne {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    {u : AdelicGLn.integralFiniteGL K n} (hf : ∀ x, f (finOne K n u * x) = f x)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) :
    rconv Γ₁ μ f φ (x * finOne K n u) = rconv Γ₁ μ f φ x := by
  unfold rconv
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, ← hf ((finOne K n u)⁻¹ * (x⁻¹ * y)), mul_inv_cancel_left]

theorem rconv_eq_zero_of_whittakerOne {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f)
    (h : ∀ x, whittakerOne (rconv Γ₁ μ f φ) x = 0) (x : normOneGL K n) :
    rconv Γ₁ μ f φ x = 0 := by
  obtain ⟨U, hU, hfU⟩ := hf.exists_finOne_mul
  have key := eq_zero_of_whittaker_eq_zero (ϕ := lift (rconv Γ₁ μ f φ))
    (continuous_lift (continuous_rconv Γ₁ μ f φ))
    (isLeftInvariant_lift fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y)
    (isCuspidal_lift fun r hr hrn y => integral_rconv_unip_eq_zero μ f hφ hr hrn y)
    ⟨openSubgroupOf U hU, lift_mul_finEmb hU fun u hu y => rconv_mul_finOne μ (hfU u hu) φ y⟩
    (fun g => by rw [whittaker_lift]; exact h _)
  have := congrFun key (x : AdelicGLn.AdelicGL K n)
  rwa [lift_coe] at this

theorem integrated_eq_zero_of_rconv_eq_zero {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (h : ∀ x, rconv Γ₁ μ f φ x = 0) :
    (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ = 0 := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine (Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f φ] with q hq
  rw [hq]
  obtain ⟨x, rfl⟩ := mk_surjective Γ₁ q
  rw [rconvQ_mk, h x]
  rfl

theorem exists_isSmoothTest_near (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      IsSmoothTest f ∧ ∫ x, ‖g x - f x‖ ∂μ ≤ ε := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ArchUnits K n), ν.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨U, hU, β, hβ, hβc, hβu, -, hclose⟩ := exists_smooth_approx μ ν g hε
  exact ⟨_, ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩,
    le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)) hclose⟩

theorem _root_.GroundTheory.Automorphic.UnitaryRep.integrated_eq_zero_of_dense {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (P : CompactlySupportedContinuousMap G ℂ → Prop)
    (hP : ∀ (g : CompactlySupportedContinuousMap G ℂ) (ε : ℝ), 0 < ε →
      ∃ f, P f ∧ ∫ x, ‖g x - f x‖ ∂ν ≤ ε)
    {v : H} (h : ∀ f, P f → π.integrated ν (UnitaryRep.ccToL1 ν f) v = 0)
    (g : CompactlySupportedContinuousMap G ℂ) : π.integrated ν (UnitaryRep.ccToL1 ν g) v = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hε' : 0 < ε / (‖v‖ + 1) := div_pos hε (by positivity)
  obtain ⟨f, hfs, hclose⟩ := hP g _ hε'
  have hf0 := h f hfs
  have hd := π.dist_integrated_ccToL1_le ν g f
  have hv1 : ‖v‖ / (‖v‖ + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [dist_eq_norm] at hd
  calc ‖π.integrated ν (UnitaryRep.ccToL1 ν g) v‖
      = ‖(π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)) v‖ := by
        rw [sub_apply, hf0, sub_zero]
    _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ v
    _ ≤ (ε / (‖v‖ + 1)) * ‖v‖ := by gcongr; exact hd.trans hclose
    _ = ε * (‖v‖ / (‖v‖ + 1)) := by ring
    _ ≤ ε * 1 := by gcongr
    _ = 0 + ε := by ring

theorem eq_zero_of_forall_whittakerOne_rconv_eq_zero {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hφ : φ ∈ cuspidalL2 μ)
    (h : ∀ f, IsSmoothTest f → ∀ x, whittakerOne (rconv Γ₁ μ f φ) x = 0) : φ = 0 := by
  by_contra hne
  obtain ⟨g, hg⟩ := UnitaryRep.exists_integrated_ne_zero (rightRegularRep Γ₁ μ) μ hne
  exact hg (UnitaryRep.integrated_eq_zero_of_dense (rightRegularRep Γ₁ μ) μ IsSmoothTest
    (fun g ε hε => exists_isSmoothTest_near μ g hε) (fun f hf =>
      integrated_eq_zero_of_rconv_eq_zero μ (rconv_eq_zero_of_whittakerOne μ hφ hf (h f hf))) g)

end MultiplicityOne

end

end GroundTheory.Automorphic
end

section
open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open AutomorphicForm FourierWhittaker

section Columns

variable {n : ℕ} {R : Type*} [CommRing R]

def colShift {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) : Fin j → R :=
  fun i => if h : i.val < k then y ⟨k, hkj⟩ * x ⟨i.val, h⟩ else 0

theorem uN_colX_mul_uN_colX_of_lt {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) :
    uN (colX (n := n) k x) * uN (colX j y) = uN (colX j (colShift hkj x y)) := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hb : b.val = j
  · by_cases ha : a.val < k
    · have hk : k < n := by have := b.2; omega
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · have hab : a < b := by rw [Fin.lt_def]; omega
        have hak : a < (⟨k, hk⟩ : Fin n) := by rw [Fin.lt_def]; exact ha
        have hkb : (⟨k, hk⟩ : Fin n) < b := by rw [Fin.lt_def]; simp only; omega
        rw [uN_apply, uN_apply, uN_apply, dif_pos hak, dif_pos hkb, dif_pos hab, colX_apply,
          colX_apply, colX_apply, dif_pos rfl, dif_pos hb, dif_pos hb]
        simp only [colShift, dif_pos ha]
        ring
      · intro c _ hc
        rw [uN_apply, uN_apply]
        by_cases hac : a < c
        · rw [dif_pos hac, colX_apply, dif_neg (fun h => hc (Fin.ext h)), zero_mul]
        · rw [dif_neg hac, zero_mul]
      · simp
    · rw [uN_apply]
      have h0 : ∀ c : Fin n, uN (colX (n := n) k x) a c * uN (colX j y) c b = 0 := by
        intro c
        rw [uN_apply]
        by_cases hac : a < c
        · rw [dif_pos hac, colX_apply]
          by_cases hck : c.val = k
          · rw [Fin.lt_def] at hac; omega
          · rw [dif_neg hck, zero_mul]
        · rw [dif_neg hac, zero_mul]
      rw [Finset.sum_eq_zero fun c _ => h0 c]
      split_ifs with hab
      · rw [colX_apply, dif_pos hb]
        simp only [colShift]
        rw [dif_neg (by simpa using ha)]
      · rfl
  · have h0 : ∀ c : Fin n, uN (colX (n := n) k x) a c * uN (colX j y) c b = 0 := by
      intro c
      rw [uN_apply (colX j y)]
      by_cases hcb : c < b
      · rw [dif_pos hcb, colX_apply, dif_neg hb, mul_zero]
      · rw [dif_neg hcb, mul_zero]
    rw [Finset.sum_eq_zero fun c _ => h0 c, uN_apply]
    split_ifs with hab
    · rw [colX_apply, dif_neg hb]
    · rfl

theorem colGL_mul_colGL_of_lt {k j : ℕ} (hkj : k < j) (x : Fin k → R) (y : Fin j → R) :
    (colGL k x : GL (Fin n) R) * colGL j y = colGL j (y + colShift hkj x y) * colGL k x := by
  refine Units.ext ?_
  have hz : ∀ w : Fin j → R, uN (colX (n := n) j w) * uN (colX k x) = 0 := by
    intro w
    refine uN_mul_uN_colX (fun p hp => colX_le j w p (Or.inl (by omega))) x
  simp only [colGL, Units.val_mul, coe_uGL, uMat, colX_add, uN_add, mul_add, add_mul, one_mul,
    mul_one, hz, uN_colX_mul_uN_colX_of_lt hkj, add_zero]
  abel

theorem pair_lastVec_colShift {K : Type*} [Field K] [NumberField K] {k j : ℕ} (hkj : k < j)
    (x : Fin k → 𝔸[K]) (y : Fin j → 𝔸[K]) :
    pair (lastVec (K := K) j) (colShift hkj x y) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val + 1 = j
  · rw [colShift, dif_neg (by omega), mul_zero]
  · rw [lastVec, if_neg hi, map_zero, zero_mul]

end Columns

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem partialCoeff_colGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hl : IsLeftInvariant ϕ) :
    ∀ (m k : ℕ), n - k = m → ∀ j, k ≤ j → j < n → ∀ (y : Fin j → 𝔸[K]) (g : AdelicGLn.AdelicGL K n),
      partialCoeff ϕ k (colGL j y * g) =
        (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) * partialCoeff ϕ k g := by
  intro m
  induction m with
  | zero => intro k hk j hkj hj; omega
  | succ m ih =>
    intro k hkm j hkj hj y g
    have hk : k < n := by omega
    rw [partialCoeff_of_lt ϕ hk, stepCoeff, stepCoeff]
    have hper : ∀ g', ∀ ξ ∈ vecLattice K (Fin k), ∀ x,
        partialCoeff ϕ (k + 1) (colGL k (ξ + x) * g') = partialCoeff ϕ (k + 1) (colGL k x * g') := by
      intro g' ξ hξ x
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    rcases eq_or_lt_of_le hkj with rfl | hlt
    · have e : (fun x : Fin k → 𝔸[K] => partialCoeff ϕ (k + 1) (colGL k x * (colGL k y * g))) =
          fun x => partialCoeff ϕ (k + 1) (colGL k (x + y) * g) := by
        funext x
        rw [colGL_add, mul_assoc]
      rw [e]
      exact vecCoeff_translate (f := fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) (hper g) y
        (lastVec k)
    · have e : (fun x : Fin k → 𝔸[K] => partialCoeff ϕ (k + 1) (colGL k x * (colGL j y * g))) =
          fun x => (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) *
            partialCoeff ϕ (k + 1) (colGL k x * g) := by
        funext x
        rw [← mul_assoc, colGL_mul_colGL_of_lt hlt, mul_assoc,
          ih (k + 1) (by omega) j hlt hj, FourierWhittaker.pair_add, pair_lastVec_colShift, add_zero]
      rw [e]
      unfold vecCoeff
      simp_rw [mul_assoc]
      rw [integral_const_mul]

theorem whittaker_colGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) {j : ℕ} (hj : j < n) (y : Fin j → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    whittaker ϕ (colGL j y * g) =
      (GroundTheory.Global.adelicChar K (pair (lastVec j) y) : ℂ) * whittaker ϕ g := by
  rw [whittaker_eq_partialCoeff_zero hc, whittaker_eq_partialCoeff_zero hc]
  exact partialCoeff_colGL_mul hl _ 0 rfl j (Nat.zero_le j) hj y g

theorem supSum_zero_eq_of_vanish {m : ℕ} {X : Pos n → 𝔸[K]}
    (hX : ∀ p : Pos n, p.1.2.val < m → X p = 0) : supSum 0 X = supSum m X := by
  classical
  unfold supSum
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun p : Pos n => p.1.2.val = p.1.1.val + 1 ∧ 0 ≤ p.1.2.val))
    (fun p : Pos n => m ≤ p.1.2.val)]
  rw [Finset.sum_eq_zero (s := Finset.filter (fun p : Pos n => ¬ m ≤ p.1.2.val) _)
    fun p hp => hX p (by simp only [Finset.mem_filter] at hp; omega), add_zero]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem whittaker_uGL_mul {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (X : Pos n → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    whittaker ϕ (uGL X * g) = (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * whittaker ϕ g := by
  classical
  suffices H : ∀ (d m : ℕ), n - m = d → ∀ X : Pos n → 𝔸[K], (∀ p : Pos n, p.1.2.val < m → X p = 0) →
      ∀ g, whittaker ϕ (uGL X * g) = (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * whittaker ϕ g from
    H n 0 (Nat.sub_zero n) X (fun p hp => absurd hp (Nat.not_lt_zero _)) g
  intro d
  induction d with
  | zero =>
    intro m hm X hX g
    have hX0 : X = 0 := funext fun p => hX p (by have := p.1.2.2; omega)
    rw [hX0, uGL_zero, one_mul, supSum_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  | succ d ih =>
    intro m hm X hX g
    have hmn : m < n := by omega
    set c : Fin m → 𝔸[K] := fun i => X ⟨(⟨i.val, by omega⟩, ⟨m, hmn⟩), by
      rw [Fin.lt_def]; exact i.2⟩
    set X' : Pos n → 𝔸[K] := fun p => if p.1.2.val = m then 0 else X p
    have hcol : colX m c = fun p : Pos n => if p.1.2.val = m then X p else 0 := by
      funext p
      rw [colX_apply]
      by_cases h : p.1.2.val = m
      · rw [dif_pos h, if_pos h]
        show X _ = X p
        congr 1
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> simp [h]
      · rw [dif_neg h, if_neg h]
    have hsplit : X = X' + colX m c := by
      funext p
      rw [hcol, Pi.add_apply]
      by_cases h : p.1.2.val = m
      · simp [X', h]
      · simp [X', h]
    have hX' : ∀ p : Pos n, p.1.2.val < m + 1 → X' p = 0 := by
      intro p hp
      by_cases h : p.1.2.val = m
      · simp [X', h]
      · simp only [X', if_neg h]; exact hX p (by omega)
    have hu : uGL X = uGL X' * colGL m c := by
      refine Units.ext ?_
      rw [Units.val_mul, colGL, coe_uGL, coe_uGL, coe_uGL,
        uMat_mul_uMat_colX (fun p hp => hX' p (by omega)) c, ← hsplit]
    have hs : supSum 0 X = supSum 0 X' + pair (lastVec m) c := by
      rw [hsplit, supSum_add, ← supSum_colX m hmn c,
        ← supSum_zero_eq_of_vanish (m := m) (X := colX m c) fun p hp => colX_le m c p (Or.inl (by omega))]
    rw [hu, mul_assoc, ih (m + 1) (by omega) X' hX', whittaker_colGL_mul hc hl hmn, hs,
      AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

end MultiplicityOne

end

end GroundTheory.Automorphic
end
