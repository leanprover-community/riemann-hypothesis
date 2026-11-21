import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem blockSphereProb_isProbabilityMeasure {B n : ℕ} (hn : 0 < n) :
    MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb B n) := by
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.sphereProb n) := by
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb
    have hne : ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 :=
      ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr hne
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
      exact_mod_cast hdim.ne'
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (MeasureTheory.measure_ball_lt_top).ne
  infer_instance

theorem height_const_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : K) :
    ReciprocityTheory.MultiplicativeHeights.h0 (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  unfold ReciprocityTheory.MultiplicativeHeights.h0
  haveI := blockSphereProb_isProbabilityMeasure (B := B) hn
  have hmean : ∀ σ : K →+* ℂ,
      ReciprocityTheory.MultiplicativeHeights.blockSphereMean B n (MvPolynomial.map σ (MvPolynomial.C a)) = Real.log ‖σ a‖ := by
    intro σ
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  have hgauss : ∀ w : FinitePlace K,
      ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = w a := by
    intro w
    unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
    by_cases ha : a = 0
    · simp [ha]
    · rw [MvPolynomial.support_C, if_neg ha, Finset.sup_singleton, MvPolynomial.coeff_C, if_pos rfl,
        Real.coe_toNNReal (w a) (by exact w.1.nonneg a)]
  simp_rw [hgauss, hmean]
  by_cases ha : a = 0
  · simp [ha]
  rw [div_eq_zero_iff]
  left
  have hfin : (Function.mulSupport fun w : FinitePlace K => w a).Finite :=
    NumberField.FinitePlace.mulSupport_finite ha
  have hsub : (Function.support fun w : FinitePlace K => Real.log (w a)) ⊆ hfin.toFinset := by
    intro w hw
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    show Real.log (w a) = 0
    rw [h1, Real.log_one]
  rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun w _ => w.1.ne_zero ha),
    ← finprod_eq_prod_of_mulSupport_subset _ (by rw [Set.Finite.coe_toFinset]),
    NumberField.FinitePlace.prod_eq_inv_abs_norm ha,
    ← Real.log_prod (fun σ _ => by simpa using ha), ← norm_prod]
  have hN : ∏ σ : K →+* ℂ, σ a = ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ a) (fun σ => σ a) (fun σ => rfl),
      ← Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    simp
  rw [hN]
  push_cast
  rw [Real.log_inv]
  simp

theorem not_injective_of_trdeg_lt {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {σ τ : Type}
    [Fintype σ] [Fintype τ] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ Ω) (n : ℕ)
    (hn : Algebra.trdeg K Ω = n) (hlt : n + Fintype.card τ < Fintype.card σ) :
    ¬ Function.Injective φ := by
  intro hinj
  have hai : AlgebraicIndependent K (φ ∘ fun i : σ => (MvPolynomial.X i : MvPolynomial σ K)) :=
    (MvPolynomial.algebraicIndependent_X σ K).map' hinj
  have hle := hai.cardinalMk_le_trdeg
  have h1 : Algebra.trdeg Ω (MvPolynomial τ Ω) = Cardinal.mk τ := by
    first
    | simpa using (MvPolynomial.trdeg_of_isDomain (R := Ω) (σ := τ))
    | simpa using (MvPolynomial.trdeg_of_isDomain Ω τ)
    | simpa using (MvPolynomial.trdeg (R := Ω) (σ := τ))
    | simpa using (Algebra.trdeg_mvPolynomial (R := Ω) (σ := τ))
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).lift_cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.algebraicIndependent_X τ Ω).isTranscendenceBasis_iff_isAlgebraic.mpr
        inferInstance).lift_cardinalMk_eq_trdeg.symm
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial τ Ω) =
      Algebra.trdeg K (MvPolynomial τ Ω) := by
    first
    | exact trdeg_add_eq K Ω
    | exact Algebra.trdeg_add_eq K Ω
  rw [← h2, hn, h1, Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
  have hc : Fintype.card σ ≤ n + Fintype.card τ := by exact_mod_cast hle
  omega

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_one_prime_eq_span_gen (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) :
    p = Ideal.span {d.gen p} := by
  haveI := hp.1
  have hpr : p.IsPrincipal := by
    obtain ⟨g, _, hg⟩ := ValUFD.heightOne_principal p hp.2
    exact ⟨⟨g, hg⟩⟩
  unfold Data.gen
  rw [dif_pos hpr]
  exact (Ideal.span_singleton_generator p).symm

theorem fZ_factor_positive_places (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ (κ : K) (T : Finset (Ideal (KTp K d.D d.N))) (e : Ideal (KTp K d.D d.N) → ℕ),
      κ ≠ 0 ∧ (↑T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne ∧
      F = MvPolynomial.C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, 0 < e p → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hOfin, hrest⟩ := d.norm_by_places hd h c
  obtain ⟨hP0fin, κ, hκ, hnorm⟩ := hrest (d.rationalBaseRow c) hy
  obtain ⟨E, hE⟩ : ∃ E : Ideal (KTp K d.D d.N) → ℤ, ∀ p, E p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Ideal (KTp K d.D d.N) → ℤ, ∀ p, Nn p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p \ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  simp only [← hE] at hnorm

  have htriv : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := by
    rintro p w ⟨hO, hG⟩ a ha
    by_contra hne
    exact hG ⟨hO, a, ha, hne⟩
  have hwy : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → 0 ≤ w (d.rationalBaseRow c) :=
    fun p w hw => d.lineRatio_val_nonneg c p w hw.1 (htriv p w hw)
  have hNn0 : ∀ p, 0 ≤ Nn p := by
    intro p
    rw [hNn]
    exact finsum_nonneg fun w => finsum_nonneg fun hw =>
      mul_nonneg (Nat.cast_nonneg _) (untopD_nonneg (hwy p w hw))

  have hsplit : ∀ p ∈ d.HtOne, E p + d.nPMM h c (d.w (d.jc c) c) p = Nn p := by
    intro p hp
    have hGsub : d.GoodP c p ⊆ d.OverP c p := fun w hw => hw.1
    have hGfin : (d.GoodP c p).Finite := (hOfin p hp).subset hGsub
    have hgood : d.nPMM h c (d.w (d.jc c) c) p =
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) := by
      unfold Data.nPMM
      refine finsum_mem_congr rfl fun w hw => ?_
      have h1 := d.good_valuation_balance hd h c p hp w hw
      rw [show d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = -WithTop.untopD 0 (w (d.rationalBaseRow c)) by linarith]
      ring
    have hsum : (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) +
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) = 0 := by
      rw [← finsum_mem_add_distrib' (hGfin.inter_of_left _) (hGfin.inter_of_left _)]
      simp
    have hO := finsum_mem_union
      (f := fun w => (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)))
      (Set.disjoint_sdiff_right : Disjoint (d.GoodP c p) (d.OverP c p \ d.GoodP c p)) hGfin
      ((hOfin p hp).subset Set.diff_subset)
    rw [Set.union_diff_cancel hGsub] at hO
    beta_reduce at hO
    rw [hE, hNn, hgood, hO]
    linarith

  have hout : ∀ p ∈ d.HtOne, p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} →
      E p = 0 ∧ Nn p = 0 := by
    intro p hp hpP
    have hz : ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
      intro w hw
      by_contra hne
      exact hpP ⟨hp, w, hw, hne⟩
    constructor
    · rw [hE]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw]
      simp
    · rw [hNn]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw.1]
      simp
  have hTS : (↑hP0fin.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro p hp
    rw [Set.Finite.coe_toFinset] at hp
    exact hp.1
  have hnotT : ∀ p ∈ d.HtOne, p ∉ hP0fin.toFinset →
      p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} := by
    intro p _ hpT hpP
    exact hpT ((Set.Finite.mem_toFinset hP0fin).mpr hpP)
  have hgen0 : ∀ p ∈ d.HtOne, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)
  have hprodE : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p) =
      ∏ p ∈ hP0fin.toFinset, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p = 1
    rw [(hout p hpS (hnotT p hpS hpT)).1, zpow_zero]
  have hprodM : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p) =
      ∏ p ∈ hP0fin.toFinset,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p = 1
    have h1 := hout p hpS (hnotT p hpS hpT)
    have h2 := hsplit p hpS
    rw [show d.nPMM h c (d.w (d.jc c) c) p = 0 by linarith [h1.1, h1.2], zpow_zero]
  have hF' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.C κ * ∏ p ∈ hP0fin.toFinset, d.gen p ^ (Nn p).toNat) := by
    rw [hF]
    simp only [Data.fZ]
    rw [hnorm, hprodE, hprodM, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod]
    rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) κ, MvPolynomial.algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpS := hTS (Finset.mem_coe.mpr hp)
    rw [← zpow_add₀ (hgen0 p hpS), hsplit p hpS, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (hNn0 p)]
  refine ⟨κ, hP0fin.toFinset, fun p => (Nn p).toNat, hκ, hTS,
    IsFractionRing.injective _ _ hF', ?_⟩
  intro p hpT hpos
  by_contra hne
  push_neg at hne
  have hz : Nn p = 0 := by
    rw [hNn]
    refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
    have h0 : w (d.rationalBaseRow c) = 0 := le_antisymm (hne w hw.1 (htriv p w hw)) (hwy p w hw)
    rw [h0]
    simp
  simp [hz] at hpos

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def relationEliminateColumn (c : ι) : KTp K d.D d.N →ₐ[K] MvPolynomial (TVar d.D d.N) (Ω c) :=
  MvPolynomial.aeval fun t =>
    if t.2 = d.jc c then
      -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (t.1, k) *
        MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
    else MvPolynomial.X t

theorem relation_section_identity (hd : d.AxH 𝒜) (c : ι) (i : Fin (d.D + 1)) :
    d.sH c (MvPolynomial.X (i, d.jc c)) + ∑ k ∈ Finset.univ.erase (d.jc c),
      d.sH c (MvPolynomial.X (i, k)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
      if i = 0 then d.rationalBaseRow c else 0 := by
  have h1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := ratio_self_height (hd.w_base c)
  split_ifs with hi
  · subst hi
    unfold Data.rationalBaseRow
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c))]
    simp only [h1, map_one, mul_one]
  · have hsum : ∑ k ∈ Finset.univ.erase (d.jc c), d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
        ∑ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
      have e1 := Finset.add_sum_erase Finset.univ (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
          (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))) (d.jc c)
      exact add_left_cancel (e1.trans e2)
    have hX : ∀ j, d.sH c (MvPolynomial.X (i, j)) = sImg (d.jc c) (d.x c) (i, j) :=
      fun j => MvPolynomial.aeval_X _ _
    have hS0 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
        Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q (d.jc c) = y :=
      fun y q => Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
    have hS1 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c))
        (k : Fin d.N), Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
          ((d.jc c).succAbove k) = q k :=
      fun y q k => Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q k
    have hA : d.sH c (MvPolynomial.X (i, d.jc c)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k)) := by
      rw [hX]
      simp only [sImg, hS0, if_neg hi]
    have hB : ∀ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (MvPolynomial.X (Sum.inr (i, k))) := by
      intro k
      rw [hX]
      simp only [sImg, hS1]
    rw [hsum, hA]
    simp only [hB]
    rw [map_neg, map_sum, neg_add_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq]

theorem relation_ker_le_valuation_prime (hd : d.AxH 𝒜) (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hpos : 0 < w (d.rationalBaseRow c))
    (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) : Q ∈ p := by
  set Ψ : MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] OmS (Ω c) d.D d.N :=
    MvPolynomial.aeval (sImg (d.jc c) (d.x c)) with hΨ
  have htop : (0 : WithTop ℤ) < ⊤ := WithTop.coe_lt_top 0
  have hsHX : ∀ n : TVar d.D d.N, d.sH c (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨX : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨs : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = d.sH c (MvPolynomial.X n) :=
    fun n => (hΨX n).trans (hsHX n).symm
  have hΨC : ∀ r : Ω c, Ψ (MvPolynomial.C r) = algebraMap (Ω c) (OmS (Ω c) d.D d.N) r :=
    fun r => MvPolynomial.aeval_C _ _
  have hnn : ∀ x : KTp K d.D d.N, 0 ≤ w (d.sH c x) := fun x => (hw.2 x).1
  have key : ∀ R : KTp K d.D d.N, 0 < w (d.sH c R - Ψ (d.relationEliminateColumn c R)) := by
    intro R
    induction R using MvPolynomial.induction_on
    next a =>
      have e1 : d.sH c (MvPolynomial.C a) = algebraMap K (OmS (Ω c) d.D d.N) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.sH c).commutes a
      have e2 : d.relationEliminateColumn c (MvPolynomial.C a) =
          algebraMap K (MvPolynomial (TVar d.D d.N) (Ω c)) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.relationEliminateColumn c).commutes a
      rw [e1, e2, IsScalarTower.algebraMap_apply K (Ω c) (MvPolynomial (TVar d.D d.N) (Ω c)) a,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) a, sub_self,
        AddValuation.map_zero]
      exact htop
    next P₁ P₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_sub_add_comm]
      exact lt_of_lt_of_le (lt_min h₁ h₂) (AddValuation.map_add _ _ _)
    next P n hP =>
      have hXn : 0 < w (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        obtain ⟨i, j⟩ := n
        have hr : d.relationEliminateColumn c (MvPolynomial.X (i, j)) = if j = d.jc c then
            -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (i, k) *
              MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
            else MvPolynomial.X (i, j) := MvPolynomial.aeval_X _ _
        rw [hr]
        split_ifs with hj
        · subst hj
          rw [map_neg, map_sum, sub_neg_eq_add]
          simp only [map_mul, hΨs, hΨC]
          rw [relation_section_identity d hd c i]
          split_ifs with hi
          · exact hpos
          · rw [AddValuation.map_zero]
            exact htop
        · rw [hΨs, sub_self, AddValuation.map_zero]
          exact htop
      simp only [map_mul]
      have e : d.sH c P * d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c P) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) =
          d.sH c P * (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) +
            (d.sH c P - Ψ (d.relationEliminateColumn c P)) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) := by ring
      rw [e]
      have hb : 0 ≤ w (Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        have h3 := AddValuation.map_sub w (d.sH c (MvPolynomial.X n))
          (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n)))
        rw [sub_sub_cancel] at h3
        exact le_trans (le_min (hnn _) hXn.le) h3
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hXn (le_add_of_nonneg_left (hnn P))
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hP (le_add_of_nonneg_right hb)
  have h := key Q
  rw [hQ, map_zero, sub_zero] at h
  exact ((hw.2 Q).2).1 h

theorem ker_relation_map_ne_bot (hd : d.AxH 𝒜) (c : ι) : RingHom.ker (d.relationEliminateColumn c) ≠ ⊥ := by
  intro hker
  have hinj : Function.Injective (d.relationEliminateColumn c) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  let g : Fin (d.D + 1) × Fin d.N → TVar d.D d.N := fun t => (t.1, (d.jc c).succAbove t.2)
  let φ : KTp K d.D d.N →ₐ[K] MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c) :=
    MvPolynomial.aeval fun t : TVar d.D d.N =>
      Fin.insertNth (α := fun _ => MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (t.1, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (t.1, k)) t.2
  have hfac : d.relationEliminateColumn c = ((MvPolynomial.rename g).restrictScalars K).comp φ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [Data.relationEliminateColumn, φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, MvPolynomial.aeval_X]
    by_cases hj : j = d.jc c
    · subst hj
      simp only [if_true, Fin.insertNth_apply_same, map_neg, map_sum, map_mul, MvPolynomial.rename_X,
        MvPolynomial.rename_C, g]
      congr 1
      have e1 := Finset.add_sum_erase Finset.univ (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (d.jc c)
      exact add_left_cancel (e1.trans e2)
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [if_neg hj, Fin.insertNth_apply_succAbove, MvPolynomial.rename_X, g]
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hinj
    rw [hfac, AlgHom.comp_apply, AlgHom.comp_apply, hab]
  refine not_injective_of_trdeg_lt φ d.D (hd.trdeg c) ?_ hφ
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

theorem fZ_eq_const_mul_irreducible_pow (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 F) :
    ∃ (F0 : KTp K d.D d.N) (κ : K) (m : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ Irreducible F0 ∧
      F = MvPolynomial.C κ * F0 ^ m ∧
      ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q := by
  obtain ⟨κ, T, e, hκ, hT, hFe, hpl⟩ := fZ_factor_positive_places (d := d) hd h c F hF
  set I : Ideal (KTp K d.D d.N) := RingHom.ker (d.relationEliminateColumn c) with hIdef
  have hIp : I.IsPrime := RingHom.ker_isPrime _
  have hIb : I ≠ ⊥ := ker_relation_map_ne_bot (d := d) hd c
  obtain ⟨q, hqI, hq⟩ := hIp.exists_mem_prime_of_ne_bot hIb
  have hprime : ∀ p ∈ d.HtOne, q ∈ p → Prime (d.gen p) := by
    intro p hp1 hqp
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgq : d.gen p ∣ q := by
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    have hg0 : d.gen p ≠ 0 := by
      intro h0
      rw [h0] at hgq
      exact hq.ne_zero (zero_dvd_iff.1 hgq)
    have hpr : (Ideal.span {d.gen p}).IsPrime := by
      rw [← hsp]
      exact hp1.1
    exact (Ideal.span_singleton_prime hg0).1 hpr
  have hcont : ∀ p ∈ T, 0 < e p → p = I := by
    intro p hpT hep
    obtain ⟨w, hw, htriv, hpos'⟩ := hpl p hpT hep
    have hIle : I ≤ p := fun Q hQ => relation_ker_le_valuation_prime (d := d) hd c p w hw htriv hpos' Q (RingHom.mem_ker.1 hQ)
    have hp1 : p ∈ d.HtOne := hT hpT
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgp := hprime p hp1 (hIle hqI)
    have hgq : d.gen p ∣ q := by
      have hqp := hIle hqI
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    obtain ⟨v, hv⟩ := hgp.irreducible.dvd_symm hq.irreducible hgq
    have hgI : d.gen p ∈ I := by
      rw [hv]
      exact I.mul_mem_right v hqI
    refine le_antisymm ?_ hIle
    rw [hsp]
    exact (Ideal.span_singleton_le_iff_mem I).2 hgI
  by_cases hIT : I ∈ T ∧ 0 < e I
  · obtain ⟨hIT, heI⟩ := hIT
    have hI1 : I ∈ d.HtOne := hT hIT
    have hsp := height_one_prime_eq_span_gen (d := d) I hI1
    refine ⟨d.gen I, κ, e I, hκ, heI, (hprime I hI1 hqI).irreducible, ?_, ?_⟩
    · rw [hFe, Finset.prod_eq_single I (fun b hb hbI => ?_) (fun hn => absurd hIT hn)]
      rcases Nat.eq_zero_or_pos (e b) with h0 | h0
      · rw [h0, pow_zero]
      · exact absurd (hcont b hb h0) hbI
    · intro Q
      rw [← Ideal.mem_span_singleton, ← hsp]
      exact RingHom.mem_ker.symm
  · exfalso
    have hone : ∏ p ∈ T, d.gen p ^ e p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      rcases Nat.eq_zero_or_pos (e p) with h0 | h0
      · rw [h0, pow_zero]
      · have hpI := hcont p hp h0
        subst hpI
        exact absurd ⟨hp, h0⟩ hIT
    rw [hFe, hone, mul_one, height_const_eq_zero (Nat.succ_pos _)] at hpos
    exact lt_irrefl _ hpos

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

noncomputable def trv {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) :
    MvPolynomial (TVar D N) R →ₐ[R] Polynomial (MvPolynomial (TVar D N) R) :=
  aeval fun t => if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2)) else Polynomial.C (X t)

theorem trv_X {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) (t : TVar D N) :
    trv i k e (X t) = if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2))
      else Polynomial.C (X t) := by
  unfold trv
  rw [MvPolynomial.aeval_X]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem relation_map_comm_transvection (c : ι) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    (Polynomial.mapRingHom (d.relationEliminateColumn c).toRingHom).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := Ω c) i k Polynomial.X).toRingHom.comp (d.relationEliminateColumn c).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [trv, Data.relationEliminateColumn]
  · rintro ⟨a, b⟩
    have hC : ∀ x : Ω c, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (C x) = Polynomial.C (C x) := by
      intro x
      simp [trv, Polynomial.algebraMap_apply]
    have hX : ∀ r l, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all
    have hXK : ∀ r l, trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all

    set φ : Fin (d.D + 1) → MvPolynomial (TVar d.D d.N) (Ω c) := fun r => d.relationEliminateColumn c (X (r, b)) with hφ
    have hφtrv : ∀ r, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ r) =
        Polynomial.C (φ r) + (if r = i then Polynomial.X * Polynomial.C (φ k) else 0) := by
      intro r
      by_cases h2 : b = d.jc c
      · have e1 : ∀ r', φ r' = -∑ l ∈ Finset.univ.erase (d.jc c),
            X (r', l) * C (ratio (Ω := Ω c) (d.w l c) (d.w (d.jc c) c)) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, eq_self_iff_true, if_true]
        rw [e1 r, e1 k, map_neg, map_sum]
        by_cases h1 : r = i
        · simp only [h1, eq_self_iff_true, if_true, map_mul, hX, hC, map_neg, map_sum, add_mul,
            Finset.sum_add_distrib, mul_neg, Finset.mul_sum, mul_assoc, neg_add]
        · simp only [h1, if_false, add_zero, map_mul, hX, hC, map_neg, map_sum]
      · have e1 : ∀ r', φ r' = X (r', b) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, if_false]
        rw [e1 r, e1 k, hX]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_mapRingHom]
    rw [hXK a b]
    change _ = trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ a)
    rw [hφtrv a]
    by_cases h1 : a = i
    · simp only [h1, eq_self_iff_true, if_true, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X]
      rfl
    · simp only [h1, if_false, add_zero, Polynomial.map_C]
      rfl

theorem transvection_fix_generator (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    trv i k Polynomial.X F0 = Polynomial.C F0 := by
  classical
  have h1 : ∀ n, F0 ∣ (trv i k Polynomial.X F0).coeff n := fun n => (hker _).1 (by
    have h2 := congrArg (fun p => Polynomial.coeff p n)
      (congrArg (fun f => f F0) (d.relation_map_comm_transvection c i k hik))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h2
    rw [h2, (hker F0).2 dvd_rfl, map_zero, Polynomial.coeff_zero])
  obtain ⟨R, hR⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 h1
  let Ψ : Polynomial (KTp K d.D d.N) →+* Polynomial (KTp K d.D d.N) :=
    Polynomial.eval₂RingHom (trv i k (-Polynomial.X)).toRingHom Polynomial.X
  have hΨ : Ψ.comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [Ψ, trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X, Ψ]
      split_ifs with h
      · simp [trv_X, h, Ne.symm hik]
      · simp [trv_X, h]
  have hneg : (Polynomial.compRingHom (-Polynomial.X)).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := K) (D := d.D) (N := d.N) i k (-Polynomial.X)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
      split_ifs <;> simp
  have hC0 : (Polynomial.C F0 : Polynomial (KTp K d.D d.N)) ≠ 0 := by simpa using hF0
  have h3 : Polynomial.C F0 = Polynomial.C F0 * (R.comp (-Polynomial.X) * Ψ R) := by
    have e1 := congrArg (fun f => f F0) hΨ
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e1
    rw [hR, map_mul] at e1
    have e2 : Ψ (Polynomial.C F0) = trv i k (-Polynomial.X) F0 := by simp [Ψ]
    have e3 := congrArg (fun f => f F0) hneg
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_compRingHom_apply, hR, Polynomial.mul_comp, Polynomial.C_comp] at e3
    rw [e2, ← e3] at e1
    rw [← mul_assoc]; exact e1.symm
  have h4 : R.comp (-Polynomial.X) * Ψ R = 1 := (mul_left_cancel₀ hC0 (h3.symm.trans (mul_one _).symm))
  obtain ⟨u, hu, hu'⟩ := Polynomial.isUnit_iff.1 (isUnit_iff_exists_inv.2 ⟨_, h4⟩)
  have hRu : R = Polynomial.C u := by
    have e : (R.comp (-Polynomial.X)).comp (-Polynomial.X) = R := by
      rw [Polynomial.comp_assoc]; simp
    rw [← e, ← hu', Polynomial.C_comp]
  have h5 : (trv (R := K) i k Polynomial.X F0).eval 0 = F0 := by
    have : (Polynomial.evalRingHom 0).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [trv, MvPolynomial.algebraMap_eq]
      · rintro ⟨i', j⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
        split_ifs <;> simp
    exact congrArg (fun f => f F0) this
  rw [hR, hRu, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C] at h5
  have hu1 : u = 1 := mul_left_cancel₀ hF0 (h5.trans (mul_one F0).symm)
  rw [hR, hRu, hu1, map_one, mul_one]

theorem aeval_trv (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : S) :
    aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) F0 = aeval r F0 := by

  set ev : Polynomial (MvPolynomial (TVar d.D d.N) K) →+* S :=
    Polynomial.eval₂RingHom (aeval r : MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom b with hev
  have hcomp : ev.comp (trv (R := K) i k Polynomial.X).toRingHom =
      (aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) :
        MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hev, trv]
    · intro t
      by_cases h1 : t.1 = i <;> simp [hev, trv, h1] <;> ring
  have h := congrArg (fun φ => φ F0) hcomp
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [← h, transvection_fix_generator d c F0 hF0 hker i k hik]
  simp [hev]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by
  classical
  revert hks
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hks
  have hik : i ≠ k := fun h => hks (h ▸ Finset.mem_insert_self _ _)
  have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
  rw [← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik
    (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]
  congr 2
  funext t
  by_cases h1 : t.1 = i
  · simp [h1, hi, hks']
  · simp [h1, Finset.mem_insert]

theorem pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by
  classical
  let S := FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
  let φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S :=
    IsScalarTower.toAlgHom K _ S
  have hφ : Function.Injective φ := IsFractionRing.injective _ S
  let x : Fin (d.D + 2) → S := fun i => φ (X (Sum.inr i))
  let U : Fin (d.D + 2) → Fin (d.N + 1) → S := fun a j => φ (X (Sum.inl (a, j)))
  have hx : ∀ i, x i ≠ 0 := fun i h0 => X_ne_zero (R := K)
    (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))
  have hx1 := hx 1
  let r : TVar d.D d.N → S := fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2
  have hG : φ (bilinearSubstitution F0) = aeval r F0 := by
    rw [bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t; simp [r, x, U]
  let s : Finset (Fin (d.D + 1)) := Finset.univ.erase 0
  have hs : s.card = d.D := by simp [s, Finset.card_erase_of_mem]
  let W : TVar d.D d.N → S := fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2
  have e1 := d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))
  have hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) =
      fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t)
        else (if t.1 ∈ s then W t else r t) := by
    funext t
    split_ifs
    · simp only [r, W, Fin.succ_zero_eq_one]
      linear_combination (x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1
    · rfl
  rw [hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs] at e1
  have e2 := aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)
  rw [hs] at e2
  let P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K := fun t =>
    if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2))
    else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))
  have hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t)
      else (if t.1 ∈ s then W t else r t)) F0 := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t
    simp only [P]
    split_ifs
    · simp only [map_sub, map_mul, W, x, U]
      simp only [x] at hx1
      linear_combination (φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1
    · simp [r, x, U]
  have key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)
    rw [hG, ← e1, hP, e2]; ring
  have key' := hφ key
  have hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :=
    MvPolynomial.X_prime
  have hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣
      X (Sum.inr 1) ^ (d.D * d0) := by
    intro h
    obtain ⟨q, hq⟩ := hp.dvd_of_dvd_pow h
    have := congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq
    simp at this
  exact hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Finsupp.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (coeff s f))
      = Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  simp only [psiP_monomial]

private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (coeff s f) := by
  rw [psiP_eq_sum_monomial, Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.coeff s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    rw [coeff_monomial, if_pos rfl, coeff_zero] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, if_neg hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, if_neg hne]

theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution

open MvPolynomial

variable {K : Type} [Field K] {D N : ℕ}

abbrev V (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

noncomputable def ev1 : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => if v = Sum.inr 0 then 1 else X v

noncomputable def thetaS (sgn : K) : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => match v with
    | Sum.inl (a, j) => if a = 0 then X (Sum.inl (a, j))
        else X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j))
    | Sum.inr i => X (Sum.inr i)

private theorem thetaS_X_inr (sgn : K) (i : Fin (D + 2)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [thetaS]

private theorem thetaS_X_inl_zero (sgn : K) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (0, j))) = X (Sum.inl (0, j)) := by
  simp [thetaS]

private theorem thetaS_X_inl_of_ne_zero (sgn : K) {a : Fin (D + 2)} (ha : a ≠ 0) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (a, j))) =
      X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j)) := by
  simp [thetaS, ha]

theorem thetaS_comp (s t : K) (hst : s + t = 0) :
    (thetaS (D := D) (N := N) s).comp (thetaS t) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (⟨a, j⟩ | i)
  · by_cases ha : a = 0
    · subst ha
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_zero]
    · have hC : (C s + C t : MvPolynomial (V D N) K) = 0 := by
        rw [← C_add, hst, C_0]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_of_ne_zero _ ha, map_add, map_mul,
        thetaS_X_inr, thetaS_X_inl_zero, algHom_C, algebraMap_eq]
      linear_combination
        (X (Sum.inr a) * X (Sum.inl (0, j)) : MvPolynomial (V D N) K) * hC
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inr]

noncomputable def theta : MvPolynomial (V D N) K ≃ₐ[K] MvPolynomial (V D N) K :=
  AlgEquiv.ofAlgHom (thetaS (-1)) (thetaS 1) (thetaS_comp _ _ (by ring)) (thetaS_comp _ _ (by ring))

def iota (p : TVar D N) : V D N := Sum.inl (p.1.succ, p.2)

theorem iota_injective : Function.Injective (iota (D := D) (N := N)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  simp only [iota, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ev1_X_inr_zero :
    ev1 (K := K) (D := D) (N := N) (X (Sum.inr 0)) = 1 := by
  simp [ev1]

private theorem ev1_X_of_ne_inr_zero {v : V D N} (hv : v ≠ Sum.inr 0) :
    ev1 (K := K) (X v) = X v := by
  simp [ev1, hv]

theorem evalOne_bilinearSubstitution (F : KTp K D N) : ev1 (bilinearSubstitution F) = theta (rename iota F) := by
  have key : (ev1 (K := K) (D := D) (N := N)).comp
      (aeval fun t : ReciprocityTheory.ChartRestriction.G.T0.TVar D N =>
        (X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2)) :
          MvPolynomial (V D N) K)) =
      (thetaS (-1)).comp (rename iota) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, j⟩
    have h1 : (Sum.inl (a.succ, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    have h2 : (Sum.inr a.succ : V D N) ≠ Sum.inr 0 :=
      fun h => Fin.succ_ne_zero a (Sum.inr_injective h)
    have h3 : (Sum.inl (0, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, ev1_X_inr_zero, ev1_X_of_ne_inr_zero h1,
      ev1_X_of_ne_inr_zero h2, ev1_X_of_ne_inr_zero h3, rename_X, iota,
      thetaS_X_inl_of_ne_zero _ (Fin.succ_ne_zero a), map_neg, map_one]
    ring
  exact DFunLike.congr_fun key F

private theorem irreducible_rename_of_injective_height {α β : Type} [Fintype α] {f : α → β}
    (hf : Function.Injective f) {F : MvPolynomial α K} (hF : Irreducible F) :
    Irreducible (rename f F) := by
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have h1 : rename f F = rename ((↑) : Set.range f → β) (renameEquiv K (Equiv.ofInjective f hf) F) := by
    rw [renameEquiv_apply, rename_rename]
    congr 1
  have h2 : Prime (renameEquiv K (Equiv.ofInjective f hf) F) := (MulEquiv.prime_iff _).mpr hP
  rw [h1]
  exact ((prime_rename_iff (Set.range f)).mpr h2).irreducible

theorem irreducible_theta_rename (F : KTp K D N) (hF : Irreducible F) :
    Irreducible (theta (rename (iota (D := D) (N := N)) F)) :=
  (MulEquiv.irreducible_iff (theta (K := K) (D := D) (N := N))).mpr
    (irreducible_rename_of_injective_height iota_injective hF)

end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

namespace LinearSubstitution

variable {K : Type} [Field K] {D N : ℕ}

abbrev isX (v : V D N) : Prop := v.isRight = true

abbrev isU (v : V D N) : Prop := v.isLeft = true

theorem wt_isX (s : V D N →₀ ℕ) : WH.wt isX s = ∑ i, s (Sum.inr i) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isX]

theorem wt_isU (s : V D N →₀ ℕ) : WH.wt isU s = ∑ p, s (Sum.inl p) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isU]

noncomputable def gImg (t : TVar D N) : MvPolynomial (V D N) K :=
  X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))

theorem weightGrading_substitution (p : V D N → Prop) [DecidablePred p]
    (hp : ∀ t : TVar D N, WH.psiP p (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X)
    (F : KTp K D N) (d0 : ℕ) (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F) :
    WH.psiP p (bilinearSubstitution F) = Polynomial.C (bilinearSubstitution F) * Polynomial.X ^ ((D + 1) * d0) := by
  classical
  have hw : ∀ s ∈ F.support, WH.wt (fun _ : TVar D N => True) s = (D + 1) * d0 := by
    intro s hs
    simp only [WH.wt, ↓reduceIte]
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hmh s hs b]
    simp
  have e := WH.psiP_eq_of_isWeightedHomogeneous (K := K) (fun _ : TVar D N => True) ((D + 1) * d0) F hw
  have e2 := congrArg (Polynomial.mapAlgHom (aeval fun t : TVar D N => gImg (K := K) t)) e
  have h1 : WH.psiP p (bilinearSubstitution F) =
      aeval (fun t => Polynomial.C (gImg (K := K) t) * Polynomial.X) F := by
    rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl, MvPolynomial.comp_aeval_apply]
    simp only [hp]
  rw [h1]
  unfold WH.psiP at e2
  rw [MvPolynomial.comp_aeval_apply] at e2
  convert e2 using 1
  · refine congrArg (fun f => aeval f F) (funext fun t => ?_)
    simp
  · rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl]
    simp

theorem psiX_g (t : TVar D N) :
    WH.psiP isX (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isX]
  try ring

theorem psiU_g (t : TVar D N) :
    WH.psiP isU (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isU]
  try ring

theorem eq_monomial_of_dehomog_const (A : MvPolynomial (V D N) K) (m : ℕ) (hA : ∀ s ∈ A.support, WH.wt isX s = m)
    (k : K) (h1 : ev1 A = C k) : A = C k * X (Sum.inr 0) ^ m := by
  classical
  have hev1x0 : ev1 (X (Sum.inr 0) : MvPolynomial (V D N) K) = 1 := by simp [ev1]
  have hmono : ∀ (s : V D N →₀ ℕ) (a : K),
      ev1 (monomial s a) = monomial (s.erase (Sum.inr 0)) a := by
    intro s a
    have hs : monomial s a =
        monomial (s.erase (Sum.inr 0)) a * X (Sum.inr 0) ^ (s (Sum.inr 0)) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [hs, map_mul, map_pow, hev1x0, one_pow, mul_one, ev1, aeval_monomial, monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    apply Finsupp.prod_congr
    intro v hv
    rw [if_neg]
    rintro rfl
    simp at hv
  have hcoeff : ∀ u, coeff u (ev1 A) =
      ∑ s ∈ A.support, if s.erase (Sum.inr 0) = u then coeff s A else 0 := by
    intro u
    conv_lhs => rw [A.as_sum]
    rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hmono, coeff_monomial]
  have hwt : ∀ s : V D N →₀ ℕ,
      WH.wt isX s = WH.wt isX (s.erase (Sum.inr 0)) + s (Sum.inr 0) := by
    intro s
    conv_lhs => rw [← Finsupp.erase_add_single (Sum.inr 0) s]
    rw [WH.wt_add, WH.wt_single, if_pos (show isX (Sum.inr 0 : V D N) from rfl)]
  have hwt0 : WH.wt isX (0 : V D N →₀ ℕ) = 0 := by simp [WH.wt]
  have hinj : ∀ s ∈ A.support, ∀ s' ∈ A.support,
      s.erase (Sum.inr 0) = s'.erase (Sum.inr 0) → s = s' := by
    intro s hs s' hs' he
    have h2 := hwt s
    have h3 := hwt s'
    rw [hA s hs] at h2
    rw [hA s' hs', ← he] at h3
    have h4 : s (Sum.inr 0) = s' (Sum.inr 0) := by omega
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, ← Finsupp.erase_add_single (Sum.inr 0) s', he, h4]
  have hsingle : ∀ s ∈ A.support, s.erase (Sum.inr 0) = 0 → s = Finsupp.single (Sum.inr 0) m := by
    intro s hs hs0
    have h2 := hwt s
    rw [hA s hs, hs0, hwt0, zero_add] at h2
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, hs0, zero_add, ← h2]
  ext u
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hu : u ∈ A.support
  · have e := hcoeff (u.erase (Sum.inr 0))
    rw [Finset.sum_eq_single u (fun s hs hne => if_neg (fun h => hne (hinj s hs u hu h)))
      (fun h => absurd hu h), if_pos rfl, h1, coeff_C] at e
    rw [← e]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · have h0 : 0 = u.erase (Sum.inr 0) := by
        rw [← h]
        simp
      rw [if_pos h0, if_pos h, mul_one]
    · have h0 : ¬ 0 = u.erase (Sum.inr 0) := fun h0 => h (hsingle u hu h0.symm).symm
      rw [if_neg h0, if_neg h, mul_zero]
  · have hu0 : coeff u A = 0 := by simpa using hu
    rw [hu0]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · rw [if_pos h, mul_one]
      have e := hcoeff 0
      rw [h1, coeff_C, if_pos rfl] at e
      rw [e]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      intro hs0
      apply hu
      rw [← h, ← hsingle s hs hs0]
      exact hs
    · rw [if_neg h, mul_zero]

end LinearSubstitution

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem substitution_split_irreducible_of (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := by
  classical
  have hF0 : F0 ≠ 0 := hirr.ne_zero
  have hirr1 : Irreducible (LinearSubstitution.ev1 (bilinearSubstitution F0)) := by
    rw [LinearSubstitution.evalOne_bilinearSubstitution]
    exact LinearSubstitution.irreducible_theta_rename F0 hirr
  have hg0 : bilinearSubstitution F0 ≠ 0 := fun h => hirr1.ne_zero (by rw [h, map_zero])
  have hX : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isX s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isX _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isX LinearSubstitution.psiX_g F0 d0 hmh)
  have hU : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isU s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isU _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isU LinearSubstitution.psiU_g F0 d0 hmh)
  have hev : LinearSubstitution.ev1 (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) = 1 := by simp [LinearSubstitution.ev1]
  have hbound : ∀ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 →
      a ≤ (bilinearSubstitution F0).totalDegree := by
    rintro a ⟨h, hh⟩
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hh, mul_zero])
    rw [hh, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) hh0, totalDegree_X_pow]
    omega
  obtain ⟨a, hPa, hle, hnot⟩ : ∃ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 ∧
      d.D * d0 ≤ a ∧ ¬ (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ (a + 1) ∣ bilinearSubstitution F0 := by
    have hP0 := d.pow_first_var_dvd_substitution c F0 hF0 hker d0 hmh
    exact ⟨Nat.findGreatest (fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
      (bilinearSubstitution F0).totalDegree,
      Nat.findGreatest_spec (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      Nat.le_findGreatest (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      fun h => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h⟩
  obtain ⟨F1, hF1⟩ := hPa
  have hF10 : F1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hF1, mul_zero])
  have hev1 : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 F1 := by
    rw [hF1, map_mul, map_pow, hev, one_pow, one_mul]
  have hdvdF1 : F1 ∣ bilinearSubstitution F0 := ⟨X (Sum.inr 0) ^ a, by rw [hF1, mul_comm]⟩
  obtain ⟨deF, hdeF⟩ := WH.hom_of_dvd LinearSubstitution.isX ((d.D + 1) * d0) (bilinearSubstitution F0) F1 hg0 hX hdvdF1
  have hshift : ∀ s ∈ F1.support, s + Finsupp.single (Sum.inr 0) a ∈ (bilinearSubstitution F0).support := by
    intro s hs
    rw [mem_support_iff, hF1, mul_comm, X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    exact mem_support_iff.1 hs
  refine ⟨a, F1, deF, hF1, ⟨fun hu => ?_, fun G H hGH => ?_⟩, ?_, ?_, ?_⟩
  · exact hirr1.not_isUnit (by rw [hev1]; exact hu.map _)
  · have hmul : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 G * LinearSubstitution.ev1 H := by rw [hev1, hGH, map_mul]
    have key : ∀ G' : MvPolynomial (LinearSubstitution.V d.D d.N) K, G' ∣ F1 → IsUnit (LinearSubstitution.ev1 G') → IsUnit G' := by
      intro G' hG' hu
      obtain ⟨k, hk, hkG⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
      obtain ⟨m, hm⟩ := WH.hom_of_dvd LinearSubstitution.isX _ (bilinearSubstitution F0) G' hg0 hX (hG'.trans hdvdF1)
      have hG'eq := LinearSubstitution.eq_monomial_of_dehomog_const G' m hm k hkG
      cases m with
      | zero =>
        rw [hG'eq, pow_zero, mul_one]
        exact hk.map C
      | succ m =>
        exfalso
        apply hnot
        obtain ⟨Q, hQ⟩ := hG'
        refine ⟨C k * X (Sum.inr 0) ^ m * Q, ?_⟩
        rw [hF1, hQ, hG'eq]
        ring
    rcases hirr1.isUnit_or_isUnit hmul with h | h
    · exact Or.inl (key G ⟨H, hGH⟩ h)
    · exact Or.inr (key H ⟨G, by rw [hGH, mul_comm]⟩ h)
  · intro s hs
    rw [← LinearSubstitution.wt_isX]
    exact hdeF s hs
  · obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hF10
    have hs' : s ∈ F1.support := mem_support_iff.2 hs
    have h := hX _ (hshift s hs')
    rw [WH.wt_add, WH.wt_single, if_pos (show LinearSubstitution.isX (Sum.inr 0 : LinearSubstitution.V d.D d.N) from rfl),
      hdeF s hs'] at h
    have h2 : (d.D + 1) * d0 = d.D * d0 + d0 := by ring
    linarith
  · intro s hs
    have h := hU _ (hshift s hs)
    rw [WH.wt_add, WH.wt_single, if_neg (by simp [LinearSubstitution.isU]), add_zero] at h
    rw [← LinearSubstitution.wt_isU]
    exact h.le

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem ratio_self' {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have hex : ∃ a : Ω, f = a • f := ⟨1, (one_smul Ω f).symm⟩
  unfold ratio
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • f = 0 := by rw [sub_smul, ← hs, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineRowCombination (c : ι) (a : Fin (d.D + 2)) : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  ∑ k, X (a, k) * C (d.affineCoord c k)

noncomputable def pluckerSubstitution (c : ι) :
    MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  aeval fun t => d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2)

theorem substitution_comp_relation (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by
  have hy : d.affineCoord c (d.jc c) = 1 := ratio_self' (hd.w_base c)
  have hs : ∀ a, d.affineRowCombination c a = ∑ k, X (a, k) * C (d.affineCoord c k) := fun a => rfl
  have hphi_inl : ∀ p, d.linearSubstitution c (X (Sum.inl p)) = X p := by
    intro p
    simp [Data.linearSubstitution]
  have hphi_inr : ∀ i, d.linearSubstitution c (X (Sum.inr i)) = d.affineRowCombination c i := by
    intro i
    simp [Data.linearSubstitution, Data.affineRowCombination]
  have hrho : ∀ t : TVar d.D d.N, d.pluckerSubstitution c (X t) =
      d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2) := by
    intro t
    simp [Data.pluckerSubstitution]
  apply MvPolynomial.algHom_ext
  intro t
  simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, hphi_inl, hphi_inr,
    AlgHom.restrictScalars_apply]
  simp only [Data.relationEliminateColumn, aeval_X]
  split_ifs with ht
  · rw [map_neg, map_sum]
    simp only [map_mul, hrho, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

    have htot : ∑ k, (d.affineRowCombination c 0 * X (t.1.succ, k) - d.affineRowCombination c t.1.succ * X (0, k)) *
        C (d.affineCoord c k) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hs]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c)), hy, map_one, mul_one] at htot
    have hC : ∀ r, d.pluckerSubstitution c (C r) = C r := fun r => by simp [Data.pluckerSubstitution]
    have hyd : ∀ k, ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c) = d.affineCoord c k := fun k => rfl
    simp only [hC, hyd]
    rw [ht]
    linear_combination htot
  · rw [hrho]

theorem substitution_vanishes_of_relation (hd : d.AxH 𝒜) (c : ι) (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) :
    d.linearSubstitution c (bilinearSubstitution Q) = 0 := by
  have h := congrArg (fun φ => φ Q) (d.substitution_comp_relation hd c)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hQ, map_zero] at h
  exact h

theorem substitution_split_irreducible (hd : d.AxH 𝒜) (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := d.substitution_split_irreducible_of c F0 hirr d0 hmh hker

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF

open MvPolynomial ReciprocityTheory.MultiplicativeHeights

variable {K : Type*} [Field K] {B n : ℕ}

def bw (b : Fin B) (s : Fin B × Fin n →₀ ℕ) : ℕ := ∑ j, s (b, j)

theorem bw_add (b : Fin B) (s t : Fin B × Fin n →₀ ℕ) : bw b (s + t) = bw b s + bw b t := by
  simp [bw, Finset.sum_add_distrib]

theorem bw_single (b : Fin B) (v : Fin B × Fin n) (e : ℕ) :
    bw b (Finsupp.single v e) = if v.1 = b then e else 0 := by
  obtain ⟨i, j⟩ := v
  by_cases h : i = b
  · subst h; simp [bw, Finsupp.single_apply]
  · simp [bw, Finsupp.single_apply, h]

noncomputable def psiB (b : Fin B) :
    MvPolynomial (Fin B × Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin B × Fin n) K) :=
  aeval fun v => if v.1 = b then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiB_X (b : Fin B) (v : Fin B × Fin n) :
    psiB (K := K) b (X v) = Polynomial.C (X v) * Polynomial.X ^ (if v.1 = b then 1 else 0) := by
  simp only [psiB, aeval_X]; split_ifs <;> simp

theorem psiB_monomial (b : Fin B) (s : Fin B × Fin n →₀ ℕ) (a : K) :
    psiB b (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ bw b s := by
  induction s using Finsupp.induction generalizing a
  · simp [psiB, bw, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  · rename_i v e f _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, psiB_X, bw_add, bw_single]
    split_ifs <;> simp only [map_mul, map_pow, mul_pow, ← pow_mul, pow_add, mul_one, mul_zero,
      pow_zero, add_zero, zero_add] <;> ring

theorem psiB_eq_of_hom (b : Fin B) (δ : ℕ) (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ∀ s ∈ f.support, bw b s = δ) : psiB b f = Polynomial.C f * Polynomial.X ^ δ := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by rw [psiB_monomial, hf s hs]

theorem coeff_psiB_ne_zero (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.coeff s) h0
  conv at h1 => lhs; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h1
  simp only [psiB_monomial, Polynomial.coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single s] at h1
  · simp at h1; exact (mem_support_iff.1 hs) h1
  · intro s' _ hne
    split_ifs <;> simp [coeff_monomial, hne]
  · intro h; exact absurd hs h

theorem ntd_pow {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]

theorem isMH_of_pow (hB : 0 < B) (F0 : MvPolynomial (Fin B × Fin n) K) (κ : K) (m δ : ℕ)
    (hm : 1 ≤ m) (hκ : κ ≠ 0) (hF0 : F0 ≠ 0)
    (h : IsMultiHomogeneous (fun _ => δ) (C κ * F0 ^ m)) :
    ∃ d0, m * d0 = δ ∧ IsMultiHomogeneous (fun _ => d0) F0 := by
  classical
  have key : ∀ b : Fin B, ∃ k, m * k = δ ∧ ∀ s ∈ F0.support, bw b s = k := by
    intro b
    have h1 := psiB_eq_of_hom b δ _ (fun s hs => h s hs b)
    rw [map_mul, map_pow, show psiB b (C κ) = Polynomial.C (C κ) by
      simp [psiB, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply], map_mul] at h1
    have hCk : (Polynomial.C (C κ) : Polynomial (MvPolynomial (Fin B × Fin n) K)) ≠ 0 := by
      simp [hκ]
    have h2 : psiB b F0 ^ m = Polynomial.C (F0 ^ m) * Polynomial.X ^ δ := by
      apply mul_left_cancel₀ hCk
      rw [h1, map_pow]; ring
    obtain ⟨s0, hs0⟩ : F0.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 fun h0 => hF0 (support_eq_empty.1 h0)
    have hP : psiB b F0 ≠ 0 := fun h0 => coeff_psiB_ne_zero b F0 s0 hs0 (by rw [h0]; simp)
    have hFm : F0 ^ m ≠ 0 := pow_ne_zero _ hF0
    have hdeg := congrArg Polynomial.natDegree h2
    have htr := congrArg Polynomial.natTrailingDegree h2
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C_mul_X_pow _ _ hFm] at hdeg
    rw [ntd_pow _ hP, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hFm] at htr
    have heq : (psiB b F0).natDegree = (psiB b F0).natTrailingDegree :=
      Nat.eq_of_mul_eq_mul_left hm (hdeg.trans htr.symm)
    refine ⟨(psiB b F0).natDegree, hdeg, fun s hs => ?_⟩
    have hc := coeff_psiB_ne_zero b F0 s hs
    have h3 := Polynomial.le_natDegree_of_ne_zero hc
    have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
    omega
  obtain ⟨k0, hk0, -⟩ := key ⟨0, hB⟩
  refine ⟨k0, hk0, fun s hs b => ?_⟩
  obtain ⟨k, hk, hks⟩ := key b
  rw [show (∑ j, s (b, j)) = bw b s from rfl, hks s hs]
  exact Nat.eq_of_mul_eq_mul_left hm (hk.trans hk0.symm)

end ReciprocityTheory.ChartRestriction.G.T0.MHF
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem irreducible_factor_structure (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (κ : K)
      (a m deF : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ m * deF ≤ d.delc c ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d.delc c) ∧
      bilinearSubstitution (F c) = MvPolynomial.C κ * MvPolynomial.X (Sum.inr 0) ^ a * F1 ^ m ∧
      d.linearSubstitution c (bilinearSubstitution (F c)) = 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := by

  obtain ⟨F0, κ0, m0, hκ0, hm0, hirr0, hFeq, hker⟩ := d.fZ_eq_const_mul_irreducible_pow hd h c (F c) (hF c) hpos
  obtain ⟨F', hF', -, hmh', -⟩ := d.componentForm_properties hd h c
  have hFF : F c = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) ((hF c).trans hF'.symm)
  have hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := hFF ▸ hmh'
  have hmh1 : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (MvPolynomial.C κ0 * F0 ^ m0) := by
    rw [← hFeq]; exact hmh
  obtain ⟨d0, hd0, hmh0⟩ :=
    MHF.isMH_of_pow (Nat.succ_pos _) F0 κ0 m0 (d.delc c) hm0 hκ0 hirr0.ne_zero hmh1
  obtain ⟨a0, F1, deF, hG0, hirr1, hxh, hdeF, hU⟩ := d.substitution_split_irreducible hd c F0 hirr0 d0 hmh0 hker
  have hg : bilinearSubstitution (F c) = MvPolynomial.C κ0 * bilinearSubstitution F0 ^ m0 := by
    rw [hFeq]; simp only [bilinearSubstitution, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨F1, κ0, a0 * m0, m0, deF, hκ0, hm0, ?_, hirr1, hxh, ?_, ?_, ?_, hmh⟩
  · calc m0 * deF ≤ m0 * d0 := Nat.mul_le_mul_left _ hdeF
      _ = d.delc c := hd0
  · intro s hs
    refine (hU s hs).trans (Nat.mul_le_mul_left _ ?_)
    calc d0 ≤ m0 * d0 := Nat.le_mul_of_pos_left _ hm0
      _ = d.delc c := hd0
  · rw [hg, hG0, mul_pow, pow_mul]; ring
  · rw [hg, map_mul, map_pow, d.substitution_vanishes_of_relation hd c F0 ((hker F0).2 dvd_rfl), zero_pow (by omega), mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
