import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PFirstMinPos

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MeasureTheory Module

theorem pow_le_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : Fin m → V) (hb : LinearIndependent ℝ b) {lam : ℝ} (hlam : 0 ≤ lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    (lam / Real.sqrt m) ^ m ≤ Real.sqrt (Matrix.gram ℝ b).det := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set W := Submodule.span ℝ (Set.range b)
  let B : Basis (Fin m) ℝ W := Basis.span hb
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hBW : ∀ i, ((B i : W) : V) = b i := fun i => congrArg Subtype.val (Basis.span_apply hb i)
  have hfin : finrank ℝ W = m := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  let Λ : Submodule ℤ W := Submodule.span ℤ (Set.range B)
  have hcov : ZLattice.covolume Λ = Real.sqrt (Matrix.gram ℝ b).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ (B.restrictScalars ℤ)]
    congr 2
    ext i j
    simp only [Matrix.gram, Matrix.of_apply]
    rw [Basis.restrictScalars_apply, Basis.restrictScalars_apply]
    exact congrArg₂ (inner ℝ) (hBW i) (hBW j)
  have hF := ZSpan.isAddFundamentalDomain' B (volume : Measure W)
  have hFvol : volume (ZSpan.fundamentalDomain B) =
      ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det) := by
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
      (ZSpan.isAddFundamentalDomain B volume), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  let o : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hfin)
  set r := lam / Real.sqrt m with hr
  let f : W →ₗ[ℝ] (Fin m → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : ∀ x, f x = WithLp.ofLp (o.repr x) := fun x => rfl
  let s : Set W := f ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r
  have hs_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [map_neg, Pi.neg_apply, Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hs_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Ioo (-r) r).linear_preimage f
  have hs_vol : volume s = ENNReal.ofReal (2 * r) ^ m := by
    have h1 : s = o.repr ⁻¹' (WithLp.ofLp ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r) := rfl
    rw [h1, (o.measurePreserving_repr).measure_preimage
      (((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage
        (PiLp.volume_preserving_ofLp (Fin m)).measurable).nullMeasurableSet),
      (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hs_lat : ∀ x : W, x ∈ Λ → x ∈ s → x = 0 := by
    intro x hxΛ hxs
    by_contra hx0
    have hxV : (x : V) ∈ Submodule.span ℤ (Set.range b) := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxΛ
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
      rw [← hc, Submodule.coe_sum]
      simp [hBW]
    have hxV0 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hr0 : 0 < r := by
      have := hxs ⟨0, hm⟩ (Set.mem_univ _)
      exact neg_lt_self_iff.1 (this.1.trans this.2)
    have hnorm : ‖(x : V)‖ < lam := by
      have hxn : ‖(x : V)‖ = ‖o.repr x‖ := by
        rw [LinearIsometryEquiv.norm_map]
        rfl
      rw [hxn, EuclideanSpace.norm_eq]
      have hsum : ∑ i, ‖(o.repr x) i‖ ^ 2 < ∑ _i : Fin m, r ^ 2 := by
        have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
        have := hxs i (Set.mem_univ i)
        rw [hf] at this
        rw [Real.norm_eq_abs, sq_abs]
        exact sq_lt_sq' this.1 this.2
      have hlam_eq : lam = Real.sqrt (∑ _i : Fin m, r ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hr0.le, hr,
          mul_div_cancel₀ _ (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne']
      rw [hlam_eq]
      exact Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => by positivity) hsum
    exact absurd (hmin _ hxV hxV0) (not_le.2 hnorm)
  by_contra hlt
  push Not at hlt
  have hr_nonneg : 0 ≤ r := div_nonneg hlam (Real.sqrt_nonneg _)
  have hreal : Real.sqrt (Matrix.gram ℝ b).det * 2 ^ m < (2 * r) ^ m := by
    rw [mul_pow, mul_comm]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have h2 : (2 : ENNReal) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hbig : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ W < volume s := by
    rw [hFvol, hs_vol, hfin, h2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
  have : Countable (Submodule.span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range B)))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hs_symm hs_conv hbig
  exact hx0 (Subtype.ext (hs_lat _ x.2 hxs))

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem HermDatum.exists_emb_or_conj (A : HermDatum Em Ψ N j) (σ : Em →+* ℂ) :
    ∃ τ, A.emb τ = σ ∨ (starRingEnd ℂ).comp (A.emb τ) = σ := by
  by_cases h : ∃ τ, A.emb τ = σ
  · obtain ⟨τ, hτ⟩ := h
    exact ⟨τ, Or.inl hτ⟩
  · have h' : ∃ τ, A.emb τ = (starRingEnd ℂ).comp σ := by
      by_contra h''
      exact h ((A.cmType σ).2 h'')
    obtain ⟨τ, hτ⟩ := h'
    refine ⟨τ, Or.inr ?_⟩
    rw [hτ]
    ext x
    simp

theorem HermDatum.finrank_eq (A : HermDatum Em Ψ N j) : Module.finrank ℚ Em = 2 * Fintype.card Ψ := by
  classical
  let g : Ψ ⊕ Ψ → (Em →+* ℂ) := Sum.elim A.emb fun τ => (starRingEnd ℂ).comp (A.emb τ)
  have hconj : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ') := by
    intro τ τ' h
    have h1 := (A.cmType (A.emb τ')).1 ⟨τ', rfl⟩
    refine h1 ⟨τ, ?_⟩
    rw [h]
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (A.emb_inj h)
      · exact absurd h (hconj a b)
      · exact absurd h.symm (hconj b a)
      · refine congrArg Sum.inr (A.emb_inj (RingHom.ext fun x => ?_))
        have := congrArg (fun φ : Em →+* ℂ => starRingEnd ℂ (φ x)) h
        simpa [g] using this
    · intro σ
      obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
      exacts [⟨Sum.inl τ, h⟩, ⟨Sum.inr τ, h⟩]
  rw [← NumberField.Embeddings.card Em ℂ, ← Fintype.card_of_bijective hg, Fintype.card_sum]
  ring

theorem HermDatum.linearIndependent_real (A : HermDatum Em Ψ N j) {m : ℕ} {x : Fin m → Fin N → Em}
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℝ fun k (p : Ψ × Fin N) => A.emb p.1 (x k p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : ∀ τ a, ∑ k, (c k : ℂ) * A.emb τ (x k a) = 0 := by
    intro τ a
    have := congr_fun hc (τ, a)
    simpa [Finset.sum_apply, Complex.real_smul] using this
  have h2 : ∀ (σ : Em →+* ℂ) a, ∑ k, (c k : ℂ) * σ (x k a) = 0 := by
    intro σ a
    obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
    · rw [← h]
      exact h1 τ a
    · rw [← h]
      have := congrArg (starRingEnd ℂ) (h1 τ a)
      simpa [map_sum, Complex.conj_ofReal] using this
  set ω := NumberField.integralBasis Em
  have hxω : ∀ (σ : Em →+* ℂ) (y : Em), σ y = ∑ i, ((ω.repr y i : ℚ) : ℂ) * σ (ω i) := by
    intro σ y
    conv_lhs => rw [← ω.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  have h3 : ∀ a i, ∑ k, c k * (ω.repr (x k a) i : ℝ) = 0 := by
    intro a
    have key : ∀ (σ : Em →+* ℂ),
        ∑ i, ((∑ k, c k * (ω.repr (x k a) i : ℝ) : ℝ) : ℂ) * σ (ω i) = 0 := by
      intro σ
      rw [← h2 σ a]
      simp only [hxω σ (x _ a)]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    have hli := (NumberField.mixedEmbedding.latticeBasis Em).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    refine hli _ (Prod.ext (funext fun w => ?_) (funext fun w => ?_))
    · simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, Prod.fst_zero,
        Pi.zero_apply]
      apply Complex.ofReal_injective
      push_cast
      simp only [InfinitePlace.embedding_of_isReal_apply]
      have hk := key w.1.embedding
      push_cast at hk
      exact hk
    · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, Complex.real_smul,
        Prod.snd_zero, Pi.zero_apply]
      exact key _
  intro k
  rw [← Module.forall_dual_apply_eq_zero_iff ℚ (c k)]
  intro φ
  have h4 : ∑ k, φ (c k) • x k = 0 := by
    funext a
    apply ω.repr.injective
    ext i
    have := congrArg φ (h3 a i)
    rw [map_sum, map_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (c k), ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact Fintype.linearIndependent_iff.1 hx _ h4 k

theorem HermDatum.exists_isZBasis (A : HermDatum Em Ψ N j) {I : Submodule (𝓞 Em) (Fin N → Em)}
    (hI : I ≤ A.L) : ∃ m, ∃ b : Fin m → Fin N → Em, IsZBasis I b := by
  classical
  have hL : IsNoetherian ℤ (A.L.restrictScalars ℤ) := isNoetherian_of_fg_of_noetherian _ A.fg
  have hJ : IsNoetherian ℤ (I.restrictScalars ℤ) :=
    isNoetherian_of_le (s := I.restrictScalars ℤ) (t := A.L.restrictScalars ℤ) hI
  have hfin : Module.Finite ℤ (I.restrictScalars ℤ) := inferInstance
  have htf : Module.IsTorsionFree ℤ (I.restrictScalars ℤ) := inferInstance
  have hfree : Module.Free ℤ (I.restrictScalars ℤ) := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis ℤ (I.restrictScalars ℤ)
  have hspan : Submodule.span ℤ (Set.range fun k => (B k : Fin N → Em)) = I.restrictScalars ℤ := by
    have e : (Set.range fun k => (B k : Fin N → Em)) = (I.restrictScalars ℤ).subtype '' Set.range B :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, B.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℤ ((I.restrictScalars ℤ).subtype ∘ B) :=
    B.linearIndependent.map' (I.restrictScalars ℤ).subtype (Submodule.ker_subtype _)
  refine ⟨_, fun k => (B k : Fin N → Em), hli, fun v => ?_⟩
  rw [hspan]
  rfl

omit [IsCMField Em] in

theorem card_eq_of_isZBasis {I : Submodule (𝓞 Em) (Fin N → Em)} {ρ : ℕ} {v : Fin ρ → Fin N → Em}
    (hv : IsNzFamily I ρ v) {m : ℕ} {b : Fin m → Fin N → Em} (hb : IsZBasis I b) :
    m = Module.finrank ℚ Em * ρ := by
  classical
  set ω := NumberField.integralBasis Em
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hvE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).1 hv.2.2.1
  set w : _ × Fin ρ → Fin N → Em := fun p => ω p.1 • v p.2
  have hw : LinearIndependent ℚ w := linearIndependent_smul ω.linearIndependent hvE
  have hspan : Submodule.span ℚ (Set.range b) = Submodule.span ℚ (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hbk : b k ∈ I := (hb.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
      set T := Submodule.span (𝓞 Em) (Set.range v)
      have hmem : T.toAddSubgroup.relIndex I.toAddSubgroup • b k ∈ T.toAddSubgroup :=
        AddSubgroup.nsmul_relIndex_mem _ hbk
      have hT : ∀ t ∈ T, t ∈ Submodule.span ℚ (Set.range w) := by
        intro t ht
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 ht
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [← algebraMap_smul Em (a k) (v k), ← ω.sum_repr (algebraMap (𝓞 Em) Em (a k)),
          Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)
      have hn : (T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ) ≠ 0 := by exact_mod_cast hv.2.2.2
      have := Submodule.smul_mem _ ((T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ)⁻¹) (hT _ hmem)
      rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul] at this
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      have hpI : w p ∈ I := by
        show ω p.1 • v p.2 ∈ I
        rw [integralBasis_apply, algebraMap_smul]
        exact I.smul_mem _ (hv.2.1 p.2)
      exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hb.2 _).1 hpI)
  have h1 := finrank_span_eq_card hbQ
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2, Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_basis ω] at h1
  simpa using h1.symm

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def embHom : (Fin D.N → Em) →+ ((Ψ × Fin D.N) → ℂ) where
  toFun v p := D.herm.emb p.1 (v p.2)
  map_zero' := by
    funext p
    simp
  map_add' v w := by
    funext p
    simp

def hodgeFrame (z : (Σ k, ι k) → ℂ) : ((Ψ × Fin D.N) → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin D.N) where
  toFun y := WithLp.toLp 2 fun p =>
    (Real.sqrt (2 * ‖D.herm.emb p.1 D.herm.ξ‖) : ℂ) * ((D.per z p.1)⁻¹ *ᵥ fun a => y (p.1, a)) p.2
  map_add' y y' := by
    ext p
    simp only [PiLp.add_apply, Pi.add_apply]
    rw [show (fun a => y (p.1, a) + y' (p.1, a)) = (fun a => y (p.1, a)) + fun a => y' (p.1, a) from rfl,
      Matrix.mulVec_add, Pi.add_apply, mul_add]
  map_smul' r y := by
    ext p
    simp only [PiLp.smul_apply, Pi.smul_apply, RingHom.id_apply]
    rw [show (fun a => r • y (p.1, a)) = r • fun a => y (p.1, a) from rfl, Matrix.mulVec_smul,
      Pi.smul_apply, Complex.real_smul, Complex.real_smul]
    ring

theorem inner_hodgeFrame (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) :
    inner ℝ (D.hodgeFrame z (D.embHom v)) (D.hodgeFrame z (D.embHom w)) = D.hodgeInner z v w := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, hodgeInner]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hodgeFrame, embHom, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, WithLp.ofLp_toLp, Complex.inner, map_mul, Complex.conj_ofReal]
  have hs : Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) * Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) =
      2 * ‖D.herm.emb τ D.herm.ξ‖ := Real.mul_self_sqrt (by positivity)
  rw [show ∀ (s : ℝ) (u x : ℂ), (s * x * ((s : ℂ) * starRingEnd ℂ u)).re = (s * s) * (starRingEnd ℂ u * x).re by
    intro s u x
    rw [show (s : ℂ) * x * ((s : ℂ) * starRingEnd ℂ u) = ((s * s : ℝ) : ℂ) * (starRingEnd ℂ u * x) by
      push_cast
      ring, Complex.re_ofReal_mul], hs]

theorem hodgeFrame_injective {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) : Function.Injective (D.hodgeFrame z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  funext p
  obtain ⟨τ, a⟩ := p
  have hP : IsUnit (D.per z τ).det := FirstMinPos.isUnit_det_of_eq_signMat (D.per_witt z hz τ)
  have hs : (Real.sqrt (2 * ‖D.herm.emb τ D.herm.ξ‖) : ℂ) ≠ 0 := by
    have : D.herm.emb τ D.herm.ξ ≠ 0 := (map_ne_zero _).2 D.herm.ξ_ne
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : (D.per z τ)⁻¹ *ᵥ (fun b => y (τ, b)) = 0 := by
    funext b
    have := congrArg (fun x : EuclideanSpace ℂ (Ψ × Fin D.N) => x (τ, b)) hy
    simp only [hodgeFrame, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hs
  have h1 : (fun b => y (τ, b)) = 0 := by
    rw [← Matrix.one_mulVec (fun b => y (τ, b)), ← Matrix.mul_nonsing_inv _ hP, ← Matrix.mulVec_mulVec, h0,
      Matrix.mulVec_zero]
  exact congr_fun h1 a

end FullerData

theorem UnitaryMinkowskiBound.proof : UnitaryMinkowskiBound.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz I hI ρ v hv
  classical
  have hex := D.herm.exists_isZBasis hI
  have hcov : D.covolZ z I = Real.sqrt (Matrix.of fun k l =>
      D.hodgeInner z (hex.choose_spec.choose k) (hex.choose_spec.choose l)).det := by
    unfold FullerData.covolZ
    rw [dif_pos hex]
  have hb : IsZBasis I hex.choose_spec.choose := hex.choose_spec.choose_spec
  have hm : hex.choose = 2 * D.f * ρ := by
    rw [card_eq_of_isZBasis hv hb, D.herm.finrank_eq]
    rfl
  set b := hex.choose_spec.choose
  let u : Fin hex.choose → EuclideanSpace ℂ (Ψ × Fin D.N) := fun k => D.hodgeFrame z (D.embHom (b k))
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hu_li : LinearIndependent ℝ u :=
    (D.herm.linearIndependent_real hbQ).map' (D.hodgeFrame z)
      (LinearMap.ker_eq_bot.2 (D.hodgeFrame_injective hz))
  have hgram : Matrix.gram ℝ u = Matrix.of fun k l => D.hodgeInner z (b k) (b l) := by
    ext k l
    exact D.inner_hodgeFrame z _ _
  have hlam0 : 0 ≤ D.lam1 z :=
    Real.sInf_nonneg (by rintro x ⟨w, -, -, rfl⟩; exact Real.sqrt_nonneg _)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range u), x ≠ 0 → D.lam1 z ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : ∑ k, c k • u k = D.hodgeFrame z (D.embHom (∑ k, c k • b k)) := by
      simp only [u, map_sum, map_zsmul]
    have hwI : ∑ k, c k • b k ∈ I := (hb.2 _).2 ((Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩)
    have hw0 : ∑ k, c k • b k ≠ 0 := by
      intro h
      apply hx0
      rw [hw, h, map_zero, map_zero]
    rw [hw, norm_eq_sqrt_real_inner, D.inner_hodgeFrame, D.hodgeInner_self]
    exact D.firstMinimum_le_period_norm z (hI hwI) hw0
  have key := pow_le_sqrt_det_gram u hu_li hlam0 hmin
  rw [hgram, ← hcov, hm] at key
  push_cast at key
  exact key

end GroundTheory.Heights₂.Heights.NineStatements
end
end
