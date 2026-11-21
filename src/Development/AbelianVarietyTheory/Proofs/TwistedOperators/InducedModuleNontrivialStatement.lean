import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.LeviProj

theorem exists_proj_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (P N M A : Subgroup G) (cP : IsClosed (P : Set G))
    (cN : IsClosed (N : Set G)) (cM : IsClosed (M : Set G)) (cA : IsClosed (A : Set G)) (hN : N ≤ P) (hM : M ≤ P)
    (hA : A ≤ P) (norm : ∀ p ∈ P, ∀ u ∈ N, p * u * p⁻¹ ∈ N) (comm : ∀ m ∈ M, ∀ t ∈ A, m * t = t * m)
    (inj : ∀ m ∈ M, ∀ t ∈ A, m * t ∈ N → m = 1 ∧ t = 1)
    (surj : ∀ p ∈ P, ∃ u ∈ N, ∃ m ∈ M, ∃ t ∈ A, p = u * m * t) :
    ∃ μ : G → G, ContinuousOn μ (P : Set G) ∧ (∀ p ∈ P, μ p ∈ M) ∧ (∀ p ∈ P, ∀ q ∈ P, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ N, ∀ m ∈ M, ∀ t ∈ A, μ (u * m * t) = m := by
  classical
  haveI : LocallyCompactSpace P := cP.locallyCompactSpace
  haveI : LocallyCompactSpace M := cM.locallyCompactSpace
  haveI : LocallyCompactSpace A := cA.locallyCompactSpace
  let N' : Subgroup P := N.subgroupOf P
  haveI : N'.Normal := ⟨fun u hu p => norm p p.2 u hu⟩
  haveI : IsClosed (N' : Set P) := cN.preimage continuous_subtype_val
  let ψ : M × A →* P := (Subgroup.inclusion hM).noncommCoprod (Subgroup.inclusion hA)
    fun m t => Subtype.ext (comm m m.2 t t.2)
  have hψ : ∀ z : M × A, (ψ z : G) = z.1 * z.2 := fun z => rfl
  let φ : M × A →* P ⧸ N' := (QuotientGroup.mk' N').comp ψ
  have cφ : Continuous φ := by
    refine QuotientGroup.continuous_mk.comp (Continuous.subtype_mk ?_ _)
    change Continuous fun z : M × A => (z.1 : G) * z.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have key : ∀ u ∈ N, ∀ (m : M) (t : A) (h : u * m * t ∈ P), φ (m, t) = (⟨_, h⟩ : P) := fun u hu m t h => by
    refine QuotientGroup.eq.2 ?_
    change ((m : G) * t)⁻¹ * (u * m * t) ∈ N
    have := norm _ (P.inv_mem (P.mul_mem (hM m.2) (hA t.2))) u hu
    rwa [inv_inv, mul_assoc, ← mul_assoc u] at this
  have sφ : Function.Surjective φ := fun q => by
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, m, hm, t, ht, rfl⟩ := surj p hp
    exact ⟨_, key u hu ⟨m, hm⟩ ⟨t, ht⟩ hp⟩
  have iφ : Function.Injective φ := (injective_iff_map_eq_one φ).2 fun z hz => by
    have := inj z.1 z.1.2 z.2 z.2.2 ((QuotientGroup.eq_one_iff (N := N') (ψ z)).1 hz)
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  let e := MulEquiv.ofBijective φ ⟨iφ, sφ⟩
  have ce : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousOpen cφ (φ.isOpenMap_of_sigmaCompact sφ cφ)).symm.continuous
  refine ⟨fun g => if h : g ∈ P then (e.symm (⟨g, h⟩ : P)).1 else 1, ?_, fun p hp => ?_, fun p hp q hq => ?_,
    fun u hu m hm t ht => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Continuous fun p : P => ((e.symm p).1 : G) :=
      continuous_subtype_val.comp (continuous_fst.comp (ce.comp QuotientGroup.continuous_mk))
    exact this.congr fun p => by simp
  · simp only [dif_pos hp, SetLike.coe_mem]
  · simp only [dif_pos hp, dif_pos hq, dif_pos (P.mul_mem hp hq)]
    rw [← Subgroup.coe_mul, ← Prod.fst_mul, ← map_mul]
    rfl
  · have h : u * m * t ∈ P := P.mul_mem (P.mul_mem (hN hu) (hM hm)) (hA ht)
    simp only [dif_pos h]
    rw [e.symm_apply_eq.2 (key u hu ⟨m, hm⟩ ⟨t, ht⟩ h).symm]

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}

theorem conj_scalar {p g : UJ ε} {U' : Submodule ℂ (Fin n → ℂ)} {c : ℂ} {y : Fin n → ℂ}
    (hp : ∀ y ∈ U', uMat p *ᵥ y ∈ U') (h : uMat g *ᵥ (uMat p⁻¹ *ᵥ y) - c • (uMat p⁻¹ *ᵥ y) ∈ U') :
    uMat (p * g * p⁻¹) *ᵥ y - c • y ∈ U' := by
  have := hp _ h
  rwa [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv,
    one_mulVec] at this

theorem keeps_orth {p : UJ ε} {U : Submodule ℂ (Fin n → ℂ)} (hp : ∀ y ∈ U, uMat p *ᵥ y ∈ U) {y : Fin n → ℂ}
    (hy : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ y) = 0) : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ (uMat p⁻¹ *ᵥ y)) = 0 := fun z hz => by
  have e := conjTranspose_inv_mul_Jm p⁻¹
  rw [inv_inv] at e
  rw [mulVec_mulVec, ← e, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hp z hz)

theorem conj_mem_flagN {p u : UJ ε} (hp : p ∈ parab ε W) (hu : u ∈ flagN ε W) : p * u * p⁻¹ ∈ flagN ε W := by
  have hq := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.1 i _ (hq _ y hy))
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.2 _ (keeps_orth (hp _) hy))

theorem comm_of_isSplit (hW : IsIsoFlag ε j W) {l t : UJ ε} {x : Fin a → ℝ} (hl : l ∈ flagM ε W)
    (ht : IsSplit ε W x t) : l * t = t * l := by
  have hp : l ∈ parab ε W := fun i y hy => (hl i y hy).1
  have hq := (parab ε W).inv_mem hp
  have : IsSplit ε W x (l * t * l⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hl ht.1) ((leviSub ε W).inv_mem hl), fun i y hy => ?_,
      fun y hy => ?_⟩
    · exact conj_scalar (hp _) (ht.2.1 i _ (hq _ y hy))
    · simpa using conj_scalar (c := 1) (hp _) (by simpa using ht.2.2 _ (keeps_orth (hp _) hy))
  exact mul_inv_eq_iff_eq_mul.1 ((existsUnique_isSplit hW x).unique this ht)

theorem exists_leviOne_part : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  intro n a ε j W hW hj
  obtain ⟨⟨N, eN⟩, cN, kN⟩ := UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  have mN : ∀ {u}, u ∈ N ↔ u ∈ flagN ε W := fun {u} => by rw [← eN]; rfl
  obtain ⟨h, hc, h1, -, hh⟩ := exists_height hW hj
  have hx : ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → h (m * t) = x := fun m hm x t ht => by
    simpa [h1] using hh 1 (mN.1 N.one_mem) m hm x t ht 1
  let A : Subgroup (UJ ε) :=
    { carrier := {t | ∃ x, IsSplit ε W x t}
      one_mem' := ⟨0, isSplit_one⟩
      mul_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.mul h'⟩
      inv_mem' := fun {t} ⟨x, h⟩ => by
        obtain ⟨t', h', -⟩ := existsUnique_isSplit hW (-x)
        have := h.mul h'
        rw [add_neg_cancel] at this
        exact ⟨_, inv_eq_of_mul_eq_one_right ((existsUnique_isSplit hW 0).unique this isSplit_one) ▸ h'⟩ }
  have cA : IsClosed (A : Set (UJ ε)) := by
    have : (A : Set (UJ ε)) = {t | IsSplit ε W (h t) t} := by
      ext t
      refine ⟨fun ⟨x, ht⟩ => ?_, fun ht => ⟨_, ht⟩⟩
      have := hx 1 (one_mem _) x t ht
      rw [one_mul] at this
      rwa [Set.mem_ofPred_eq, this]
    rw [this]
    simp only [IsSplit, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_flagM W).inter (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub (by fun_prop))
    · exact isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub continuous_const)
  have hN : N ≤ parab ε W := fun u hu => kN u (mN.1 hu)
  have hM : leviOne ε W ≤ parab ε W := fun m hm i y hy => (hm.1 i y hy).1
  have hA : A ≤ parab ε W := fun t ⟨_, ht⟩ i y hy => (ht.1 i y hy).1
  obtain ⟨μ, c, m1, m2, m3⟩ := exists_proj_of_closed (parab ε W) N (leviOne ε W) A isClosed_parab (eN ▸ cN)
    (isClosed_leviOne hW hj) cA hN hM hA (fun p hp u hu => mN.2 (conj_mem_flagN hp (mN.1 hu)))
    (fun m hm t ⟨_, ht⟩ => comm_of_isSplit hW hm.1 ht)
    (fun m hm t ⟨x, ht⟩ hu => by
      have e : m * t = 1 := GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW _ (mN.1 hu) _
        ((leviSub ε W).inv_mem ((leviSub ε W).mul_mem hm.1 ht.1))
        (by rw [mul_inv_cancel]; exact (compactSub ε).one_mem)
      have := hx m hm x t ht
      rw [e, h1] at this
      have e' : t = 1 := (existsUnique_isSplit hW x).unique ht (this ▸ isSplit_one)
      exact ⟨by simpa [e'] using e, e'⟩)
    (fun p hp => by
      obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
      exact ⟨u, mN.2 hu, m, hm, t, ⟨x, ht⟩, rfl⟩)
  exact ⟨μ, c, m1, m2, fun u hu m hm x t ht => ⟨mul_mem (mul_mem (hN (mN.2 hu)) (hM hm)) (hA ⟨x, ht⟩),
    m3 u (mN.2 hu) m hm t ⟨x, ht⟩⟩⟩

end GlobalTheory.LeviProj
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_projection_to_levi : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  atlas_forward_decl GlobalTheory.LeviProj.exists_leviOne_part
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.RealInd

theorem exists_kLevi_equivariant_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V,
    Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  intro n ε D
  obtain ⟨hnt, -, hU, -⟩ := D.temp
  let C : Subgroup (UJ ε) := KG ε ⊓ leviOne ε D.W
  have hC : IsCompact (C : Set (UJ ε)) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne D.flag D.pos)
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let μ : Measure C := Measure.haarMeasure ⊤
  obtain ⟨v, hv⟩ := exists_ne (0 : D.V)
  have hmat : ∀ c : C, uMat (c : UJ ε) ∈ mats (leviOne ε D.W) := fun c => ⟨c, c.2.2, rfl⟩
  have hsc : Continuous fun c : C => D.σ (uMat (c : UJ ε)) v :=
    (hU.2.2 v).comp_continuous (continuous_uMat.comp continuous_subtype_val) hmat
  have hσ1 : D.σ (uMat (1 : UJ ε)) v = v := by rw [uMat_one, hU.1.1]; rfl

  have hS : IsOpen {c : C | 0 < RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ} :=
    isOpen_lt continuous_const (RCLike.continuous_re.comp (continuous_const.inner hsc))
  obtain ⟨U, hUo, hUS⟩ := isOpen_induced_iff.1 hS
  have h1U : (1 : UJ ε) ∈ U := by
    have : (1 : C) ∈ Subtype.val ⁻¹' U := by
      rw [hUS]
      change 0 < RCLike.re ⟪v, D.σ (uMat (1 : UJ ε)) v⟫_ℂ
      rw [hσ1, inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.2 hv) 2
    exact this
  obtain ⟨f, hf, hf1, hfK⟩ := CompletelyRegularSpace.completely_regular (1 : UJ ε) Uᶜ hUo.isClosed_compl
    (fun h => h h1U)
  let b : UJ ε → ℝ := fun g => 1 - (f g : ℝ)
  have hb : Continuous b := continuous_const.sub (continuous_subtype_val.comp hf)
  have hb0 : ∀ g, 0 ≤ b g := fun g => sub_nonneg.2 (f g).2.2
  have hb1 : b 1 = 1 := by simp [b, hf1]
  have hbU : ∀ g, b g ≠ 0 → g ∈ U := fun g hg => by
    by_contra h
    exact hg (by simp [b, hfK h])
  let F : UJ ε → C → D.V := fun g c => ((b (g⁻¹ * c) : ℝ) : ℂ) • D.σ (uMat (c : UJ ε)) v
  have hF : Continuous (Function.uncurry F) :=
    (Complex.continuous_ofReal.comp (hb.comp (continuous_fst.inv.mul
      (continuous_subtype_val.comp continuous_snd)))).smul (hsc.comp continuous_snd)
  have hFi : ∀ g, Integrable (F g) μ := fun g =>
    (hF.comp (Continuous.prodMk_right g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨fun g => ∫ c, F g c ∂μ, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := μ) hF (isCompact_univ (X := C))
    simpa only [Measure.restrict_univ] using this
  · intro h0
    beta_reduce at h0
    have e1 : ∫ c, ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by rw [integral_inner (hFi 1), h0, inner_zero_right]
    have e2 : ∫ c, RCLike.re ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by
      rw [integral_re ((hFi 1).const_inner v), e1, map_zero]
    let G : C → ℝ := fun c => b c * RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ
    have eG : ∀ c, RCLike.re ⟪v, F 1 c⟫_ℂ = G c := fun c => by
      simp only [F, G, inv_one, one_mul, inner_smul_right]
      simp
    have hG : Continuous G :=
      (hb.comp continuous_subtype_val).mul (RCLike.continuous_re.comp (continuous_const.inner hsc))
    have hG0 : 0 ≤ G := fun c => by
      by_cases h : b c = 0
      · simp [G, h]
      · have hc : c ∈ Subtype.val ⁻¹' U := hbU _ h
        rw [hUS] at hc
        exact mul_nonneg (hb0 _) hc.le
    have hG1 : G 1 ≠ 0 := by
      have : G 1 = ‖v‖ ^ 2 := by
        simp only [G]
        rw [show ((1 : C) : UJ ε) = 1 from rfl, hb1, hσ1, inner_self_eq_norm_sq, one_mul]
      rw [this]
      exact (pow_pos (norm_pos_iff.2 hv) 2).ne'
    have := hG.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (HasCompactSupport.of_compactSpace _) hG0 hG1
    rw [← integral_congr_ae (Filter.Eventually.of_forall eG), e2] at this
    exact lt_irrefl _ this
  · intro m hmM hmK g
    let m' : C := ⟨m, hmK, hmM⟩
    beta_reduce
    have e := integral_mul_left_eq_self (μ := μ) (F (m * g)) m'
    rw [← e, ← ContinuousLinearMap.integral_comp_comm _ (hFi g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [F]
    have h1 : (m * g)⁻¹ * ((m' * c : C) : UJ ε) = g⁻¹ * (c : UJ ε) := by
      change (m * g)⁻¹ * (m * (c : UJ ε)) = _
      group
    have h2 : D.σ (uMat ((m' * c : C) : UJ ε)) = D.σ (uMat m) ∘SL D.σ (uMat (c : UJ ε)) := by
      change D.σ (uMat (m * (c : UJ ε))) = _
      rw [uMat_mul]
      exact hU.1.2 _ ⟨m, hmM, rfl⟩ _ (hmat c)
    rw [h1, h2, map_smul]
    rfl

end GlobalTheory.RealInd
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_section_levi_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V, Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  atlas_forward_decl GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.ParabCompact

theorem continuous_of_continuous_mul : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    ∀ (Y : Type) [TopologicalSpace Y] (F : UJ ε → Y),
      Continuous (fun q : parab ε W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) → Continuous F := by
  intro n a ε j W hW Y _ F hF
  let q : parab ε W × KG ε → UJ ε := fun x => (x.1 : UJ ε) * (x.2 : UJ ε)
  have hqc : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective q := by
    intro g
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    have hk' : k ∈ KG ε := ((KG_eq ε).symm ▸ hk :)
    exact ⟨(⟨g * k⁻¹, hp⟩, ⟨k, hk'⟩), by simp [q]⟩
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : parab ε W → UJ ε) (id : KG ε → KG ε)) :=
    (isClosed_parab.isClosedEmbedding_subtypeVal).prodMap Topology.IsClosedEmbedding.id
  let e : UJ ε × KG ε ≃ₜ UJ ε × KG ε :=
    { toFun := fun x => (x.1 * (x.2 : UJ ε), x.2)
      invFun := fun x => (x.1 * (x.2 : UJ ε)⁻¹, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := by
        exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk continuous_snd
      continuous_invFun := by
        exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd).inv).prodMk continuous_snd }
  have hcl : IsClosedMap q := by
    have : q = Prod.fst ∘ e ∘ Prod.map Subtype.val id := by funext x; rfl
    rw [this]
    exact isClosedMap_fst_of_compactSpace.comp (e.isClosedMap.comp hι.isClosedMap)
  have hQ : Topology.IsQuotientMap q := hcl.isQuotientMap hqc hsurj
  exact hQ.continuous_iff.2 hF

end GlobalTheory.ParabCompact
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_iwasawa_continuous : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    ∀ (Y : Type) [TopologicalSpace Y] (F : UJ ε → Y),
      Continuous (fun q : parab ε W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) → Continuous F := by
  atlas_forward_decl GlobalTheory.ParabCompact.continuous_of_continuous_mul
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.RealInd

theorem integral_norm_sq_pos_of_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns →
    ∀ g, f g ≠ 0 → 0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  intro n ε D f hf g hg
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, hpe⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by
    have : k ∈ (KG ε : Set (UJ ε)) := (KG_eq ε).symm ▸ hk
    exact this
  have hfk : f k ≠ 0 := by
    intro h0
    apply hg
    have e := (mem_indFun_top.1 hf).2 u hu m hm x t ht k
    rw [← hpe, inv_mul_cancel_right, h0, map_zero, smul_zero] at e
    exact e
  have hcont : Continuous fun k : KG ε => ‖f k‖ ^ 2 :=
    ((mem_indFun_top.1 hf).1.comp continuous_subtype_val).norm.pow 2
  haveI : (muK ε).IsOpenPosMeasure := by unfold muK; infer_instance
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ⟨k, hkK⟩)
    (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) (by simpa using hfk)

end GlobalTheory.RealInd
end
end

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_function_l2_positive : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns → ∀ g, f g ≠ 0 →
    0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  atlas_forward_decl GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.IndNonzero

theorem mem_leviOne_of_mem_parab_KG {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) {p : UJ ε} (hp : p ∈ parab ε W) (hk : p ∈ KG ε) :
    p ∈ leviOne ε W := by
  obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
  obtain ⟨h, -, h1, hK, hh⟩ := exists_height hW hj
  have hx : x = 0 := by
    have e1 := hh u hu m hm x t ht 1
    have e2 := hK 1 _ hk
    rw [mul_one] at e1
    rw [one_mul] at e2
    rw [e2, h1, add_zero] at e1
    exact e1.symm
  subst hx
  have ht1 : t = 1 := (existsUnique_isSplit hW 0).unique ht isSplit_one
  subst ht1
  rw [mul_one] at hk ⊢
  have hk' : u * m ∈ maxK ε := by rw [← KG_eq]; exact hk
  rw [GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW u hu m hm.1 hk', one_mul]
  exact hm

theorem continuous_apply_of_isURepOn {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℂ)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}
    (hσ : IsURepOn S σ) {X : Type} [TopologicalSpace X] {mf : X → Matrix (Fin n) (Fin n) ℂ} {wf : X → V}
    (hm : Continuous mf) (hS : ∀ x, mf x ∈ S) (hw : Continuous wf) : Continuous fun x => σ (mf x) (wf x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have h1 : ContinuousAt (fun x => σ (mf x) (wf x0)) x0 :=
    ((hσ.2.2 (wf x0)).comp_continuous hm hS).continuousAt
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
  have h2 : Filter.Tendsto (fun x => ‖wf x - wf x0‖) (nhds x0) (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hw.continuousAt
  refine squeeze_zero (g := fun x => ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ + ‖wf x - wf x0‖)
    (fun _ => norm_nonneg _) (fun x => ?_) (by have := h1.add h2; rwa [add_zero] at this)
  calc ‖σ (mf x) (wf x) - σ (mf x0) (wf x0)‖
      = ‖σ (mf x) (wf x - wf x0) + (σ (mf x) (wf x0) - σ (mf x0) (wf x0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖σ (mf x) (wf x - wf x0)‖ + ‖σ (mf x) (wf x0) - σ (mf x0) (wf x0)‖ := norm_add_le _ _
    _ = _ := by rw [hσ.2.1 _ (hS x)]; ring

end GlobalTheory.IndNonzero

namespace GlobalTheory.IndNonzero

theorem exists_equivariant {n : ℕ} {ε : Fin n → Bool} (D : Datum ε) :
    ∃ F : UJ ε → D.V, Continuous F ∧ F 1 ≠ 0 ∧ ∀ u ∈ flagN ε D.W, ∀ m ∈ leviOne ε D.W, ∀ x t,
      IsSplit ε D.W x t → ∀ g, F (u * m * t * g) = D.σ (uMat m) (F g) := by
  classical
  obtain ⟨hU, -⟩ := D.temp.2.2
  have hW := D.flag
  have hj := D.pos
  obtain ⟨φ, hφc, hφ1, hφm⟩ := GlobalTheory.T.continuous_section_levi_equivariant n ε D
  obtain ⟨μ, hμc, hμM, hμmul, hμs⟩ := GlobalTheory.T.parabolic_projection_to_levi n D.a ε D.j D.W hW hj
  have hPK := fun p hp hk => mem_leviOne_of_mem_parab_KG hW hj (p := p) hp hk
  have hσmul : ∀ m ∈ leviOne ε D.W, ∀ m' ∈ leviOne ε D.W, ∀ w,
      D.σ (uMat (m * m')) w = D.σ (uMat m) (D.σ (uMat m') w) := by
    intro m hm m' hm' w
    rw [uMat_mul, hU.1.2 _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩]
    rfl
  have h1N : (1 : UJ ε) ∈ flagN ε D.W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  have hμid : ∀ m ∈ leviOne ε D.W, μ m = m := fun m hm => by
    simpa using (hμs 1 h1N m hm 0 1 isSplit_one).2
  have dec : ∀ g : UJ ε, ∃ p ∈ parab ε D.W, ∃ k ∈ KG ε, g = p * k := fun g => by
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    refine ⟨g * k⁻¹, hp, k, ?_, by group⟩
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have wd : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, ∀ p' ∈ parab ε D.W, ∀ k' ∈ KG ε, p * k = p' * k' →
      D.σ (uMat (μ p)) (φ k) = D.σ (uMat (μ p')) (φ k') := by
    intro p hp k hk p' hp' k' hk' e
    have hck : p'⁻¹ * p = k' * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hcP : p'⁻¹ * p ∈ parab ε D.W := mul_mem (inv_mem hp') hp
    have hcK : p'⁻¹ * p ∈ KG ε := hck ▸ mul_mem hk' (inv_mem hk)
    have hcM := hPK _ hcP hcK
    have h1 : μ p = μ p' * (p'⁻¹ * p) := by
      conv_lhs => rw [show p = p' * (p'⁻¹ * p) by group]
      rw [hμmul p' hp' _ hcP, hμid _ hcM]
    have h2 : φ k' = D.σ (uMat (p'⁻¹ * p)) (φ k) := by
      rw [← hφm _ hcM hcK, hck, inv_mul_cancel_right]
    rw [h1, hσmul _ (hμM p' hp') _ hcM, h2]
  choose pp hpp kk hkk hpk using dec
  let F : UJ ε → D.V := fun g => D.σ (uMat (μ (pp g))) (φ (kk g))
  have hF : ∀ p ∈ parab ε D.W, ∀ k ∈ KG ε, F (p * k) = D.σ (uMat (μ p)) (φ k) := fun p hp k hk =>
    wd _ (hpp _) _ (hkk _) p hp k hk (hpk (p * k)).symm
  have hFc : Continuous F := by
    refine GlobalTheory.T.continuous_of_iwasawa_continuous n D.a ε D.j D.W hW D.V F ?_
    have : (fun q : parab ε D.W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) =
        fun q => D.σ (uMat (μ q.1)) (φ q.2) := funext fun q => hF _ q.1.2 _ q.2.2
    rw [this]
    refine continuous_apply_of_isURepOn hU (mf := fun q : parab ε D.W × KG ε => uMat (μ q.1)) (wf := fun q => φ q.2) ?_ ?_ ?_
    · exact continuous_uMat.comp ((hμc.comp_continuous continuous_subtype_val fun p => p.2).comp continuous_fst)
    · exact fun q => ⟨μ q.1, hμM _ q.1.2, rfl⟩
    · exact hφc.comp (continuous_subtype_val.comp continuous_snd)
  refine ⟨F, hFc, ?_, fun u hu m hm x t ht g => ?_⟩
  · have := hF 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    rw [this, hμid 1 (one_mem _), uMat_one, hU.1.1, ContinuousLinearMap.one_apply]
    exact hφ1
  · obtain ⟨hP, hμ⟩ := hμs u hu m hm x t ht
    have e : u * m * t * pp g * kk g = u * m * t * g := by rw [mul_assoc (u * m * t), ← hpk g]
    rw [← e, hF _ (mul_mem hP (hpp g)) _ (hkk g), hμmul _ hP _ (hpp g), hμ, hσmul _ hm _ (hμM _ (hpp g))]

theorem indModule_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  intro n ε I
  obtain ⟨F, hFc, hF1, hFl⟩ := exists_equivariant I.toDatum
  obtain ⟨e, he, he1, -⟩ := exists_spherical I.flag I.pos I.s
  have hf : (fun g => e g • F g) ∈ I.fns := by
    rw [mem_indFun_top]
    refine ⟨(mem_indFun_top.1 he).1.smul hFc, fun u hu m hm x t ht g => ?_⟩
    have := (mem_indFun_top.1 he).2 u hu m hm x t ht g
    simp only [ContinuousLinearMap.one_apply, smul_eq_mul] at this
    rw [this, hFl u hu m hm x t ht g, map_smul, smul_smul]
  have hpos := GlobalTheory.T.induced_function_l2_positive n ε I.toDatum _ hf 1 (by simpa [he1] using hF1)
  have hι : I.ι ⟨_, hf⟩ ≠ 0 := by
    intro h0
    have := I.model.norm_sq ⟨_, hf⟩
    rw [h0, norm_zero, zero_pow two_ne_zero] at this
    exact hpos.ne this
  exact nontrivial_of_ne _ _ hι

end GlobalTheory.IndNonzero
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_module_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  atlas_forward_decl GlobalTheory.IndNonzero.indModule_nontrivial
end
