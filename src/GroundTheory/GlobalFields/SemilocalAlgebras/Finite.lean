import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter

noncomputable section

namespace SemiLocal

variable {L : Type*} [Field L] [NumberField L]

theorem exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩

theorem norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow,
    NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha

theorem toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num

theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji
      simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)

end SemiLocal

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZero

noncomputable section

namespace SemiLocal

section Integers

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem valued_algebraMap_int (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) = u.intValuation b := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]

theorem valued_algebraMap_int_le_one (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) ≤ 1 := by
  rw [valued_algebraMap_int]
  exact u.intValuation_le_one b

theorem valued_algebraMap_int_lt_one_iff (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) < 1 ↔ b ∈ u.asIdeal := by
  rw [valued_algebraMap_int]
  exact u.intValuation_lt_one_iff_mem b

theorem valued_algebraMap_field (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem exists_int_valued_sub_lt_one (d : u.adicCompletion F) (hd : Valued.v d ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r) < 1 := by
  obtain ⟨x, hx⟩ : ∃ x : F, Valued.v (d - algebraMap F (u.adicCompletion F) x) < 1 := by
    have ho : IsOpen {y : u.adicCompletion F | Valued.v (d - y) < 1} := by
      have : {y : u.adicCompletion F | Valued.v (d - y) < 1} = Metric.ball d 1 := by
        ext y
        rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_comm, dist_eq_norm,
          Valued.toNormedField.norm_lt_one_iff]
      rw [this]
      exact Metric.isOpen_ball
    exact (HeightOneSpectrum.denseRange_algebraMap F u).exists_mem_open ho ⟨d, by simp⟩
  have hx1 : u.valuation F x ≤ 1 := by
    rw [← valued_algebraMap_field]
    calc Valued.v (algebraMap F (u.adicCompletion F) x)
        = Valued.v (d - (d - algebraMap F (u.adicCompletion F) x)) := by rw [sub_sub_cancel]
      _ ≤ max (Valued.v d) (Valued.v (d - algebraMap F (u.adicCompletion F) x)) :=
          Valuation.map_sub _ _ _
      _ ≤ 1 := max_le hd hx.le
  obtain ⟨r, hr⟩ := u.exists_valuation_sub_lt_of_integer hx1 1
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) r -
      algebraMap F (u.adicCompletion F) x) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F), ← map_sub,
      valued_algebraMap_field]
    simpa using hr
  calc Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r)
      = Valued.v ((d - algebraMap F (u.adicCompletion F) x) -
          (algebraMap (𝓞 F) (u.adicCompletion F) r - algebraMap F (u.adicCompletion F) x)) := by
        congr 1; ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ < 1 := max_lt hx hr'

end Integers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem algebraMap_completion_algebraMap_int (r : 𝓞 K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap (𝓞 K) _ r) =
      algebraMap (𝓞 L) (w.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), algebraMap_completion_eq,
    completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
    IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, ← IsScalarTower.algebraMap_apply (𝓞 K) K L]

theorem valued_algebraMap_completion (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) :=
  valued_completionMap v w x

variable {ι : Type*} [Fintype ι]

theorem valued_sum_le (ω : ι → 𝓞 L) (c : ι → v.adicCompletion K) (M : ℤᵐ⁰)
    (hM : ∀ j, Valued.v (c j) ≤ M) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) ≤ M ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul, valued_algebraMap_completion]
  calc _ ≤ Valued.v (c j) ^ w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
        mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
    _ ≤ _ := by rw [mul_one]; exact pow_le_pow_left' (hM j) _

theorem valued_sum_eq_one (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (d : ι → v.adicCompletion K) (hd : ∀ j, Valued.v (d j) ≤ 1) (j0 : ι)
    (hj0 : Valued.v (d j0) = 1) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) = 1 := by
  refine le_antisymm (by simpa using valued_sum_le v w ω d 1 hd) ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  choose r hr using fun j ↦ exists_int_valued_sub_lt_one v (d j) (hd j)
  have h1 : Valued.v (algebraMap (𝓞 L) (w.adicCompletion L)
      (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j)) < 1 := by
    have heq : algebraMap (𝓞 L) (w.adicCompletion L) (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j) =
        (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) -
        ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L)
          (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_sub, algebraMap_completion_algebraMap_int]
      ring
    rw [heq]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hlt ?_)
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, valued_algebraMap_completion]
    calc _ ≤ Valued.v (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) ^
          w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
          mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
      _ < 1 := by rw [mul_one]; exact pow_lt_one' (hr j) he0
  rw [valued_algebraMap_int_lt_one_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sum] at h1
  have hsum : ∑ j, Ideal.Quotient.mk v.asIdeal (r j) • Ideal.Quotient.mk w.asIdeal (ω j) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, map_mul, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hr0 := Fintype.linearIndependent_iff.1 hω _ hsum j0
  rw [Ideal.Quotient.eq_zero_iff_mem, ← valued_algebraMap_int_lt_one_iff v] at hr0
  have : Valued.v (d j0) < 1 := by
    calc Valued.v (d j0) = Valued.v ((d j0 - algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) +
          algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt (hr j0) hr0
  exact absurd hj0 this.ne

omit [Fintype ι] in
theorem valued_sum_eq [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (c : ι → v.adicCompletion K) (j0 : ι) (hj0 : ∀ j, Valued.v (c j) ≤ Valued.v (c j0)) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) =
      Valued.v (c j0) ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  by_cases h0 : c j0 = 0
  · have hc : ∀ j, c j = 0 := fun j ↦ by
      have := hj0 j
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
    simp [hc, zero_pow he0]
  · have hv0 : Valued.v (c j0) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    set d : ι → v.adicCompletion K := fun j ↦ c j * (c j0)⁻¹ with hd_def
    have hcd : ∀ j, c j = c j0 * d j := fun j ↦ by
      simp only [hd_def]
      rw [mul_comm (c j), ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    have hd : ∀ j, Valued.v (d j) ≤ 1 := fun j ↦ by
      simp only [hd_def, map_mul, map_inv₀]
      rw [← mul_inv_cancel₀ hv0]
      exact mul_le_mul_left (hj0 j) _
    have hdj0 : Valued.v (d j0) = 1 := by simp [hd_def, mul_inv_cancel₀ h0]
    have : ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
        algebraMap (𝓞 L) (w.adicCompletion L) (ω j) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j0) *
          ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
            algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcd j, map_mul, mul_assoc]
    rw [this, map_mul, valued_algebraMap_completion, valued_sum_eq_one v w ω hω d hd j0 hdj0,
      mul_one]

theorem eq_of_exp_mul_pow_eq {e i i' : ℕ} (hi : i < e) (hi' : i' < e) {a b : ℤᵐ⁰} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : exp (-(i : ℤ)) * a ^ e = exp (-(i' : ℤ)) * b ^ e) : i = i' := by
  rw [← exp_log ha, ← exp_log hb, ← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_add, exp_inj] at h
  simp only [nsmul_eq_mul] at h
  have hdvd : (e : ℤ) ∣ (i : ℤ) - i' := ⟨log a - log b, by rw [mul_sub]; linarith⟩
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
  omega

omit [Fintype ι] in

theorem linearIndependent_uniformizer_pow_mul [Finite ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (π : L) (hπ : w.valuation L π = exp (-1 : ℤ)) :
    LinearIndependent (v.adicCompletion K)
      (fun p : Fin (w.asIdeal.ramificationIdx (𝓞 K)) × ι ↦
        algebraMap L (w.adicCompletion L) π ^ (p.1 : ℕ) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω p.2)) := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact linearIndependent_empty_type
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  set P := algebraMap L (w.adicCompletion L) π with hP
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set s : Fin e → w.adicCompletion L := fun i ↦
    ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (g (i, j)) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j) with hs_def
  have hsum : ∑ i : Fin e, P ^ (i : ℕ) * s i = 0 := by
    rw [← hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hs_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def]
    ring
  have hvP : ∀ n : ℕ, Valued.v (P ^ n) = exp (-(n : ℤ)) := by
    intro n
    rw [map_pow, hP, valued_algebraMap_field, hπ, ← exp_nsmul]
    simp
  choose J hJ using fun i : Fin e ↦ Finite.exists_max (fun j ↦ Valued.v (g (i, j)))
  set M : Fin e → ℤᵐ⁰ := fun i ↦ Valued.v (g (i, J i)) with hM_def
  have hterm : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) = exp (-((i : ℕ) : ℤ)) * M i ^ e := by
    intro i
    rw [map_mul, hvP, hs_def, valued_sum_eq v w ω hω _ (J i) (hJ i)]
  have hM : ∀ i, M i = 0 := by
    by_contra hne
    obtain ⟨i1, hi1⟩ := not_forall.1 hne
    have : Nonempty (Fin e) := ⟨i1⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i : Fin e ↦ Valued.v (P ^ (i : ℕ) * s i))
    have hnz : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) ≠ 0 → M i ≠ 0 := by
      intro i hi hMi
      rw [hterm, hMi, zero_pow he0, mul_zero] at hi
      exact hi rfl
    have htop : Valued.v (P ^ (i0 : ℕ) * s i0) ≠ 0 := by
      intro h
      have := hi0 i1
      rw [h, hterm] at this
      have h' : exp (-((i1 : ℕ) : ℤ)) * M i1 ^ e = 0 := le_antisymm this zero_le
      rw [mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact exp_ne_zero h'
      · exact hi1 (pow_eq_zero_iff he0 |>.1 h')
    have hlt : ∀ i ∈ Finset.univ \ {i0},
        Valued.v (P ^ (i : ℕ) * s i) < Valued.v (P ^ (i0 : ℕ) * s i0) := by
      intro i hi
      have hne : i ≠ i0 := by simpa using hi
      refine lt_of_le_of_ne (hi0 i) fun heq ↦ hne (Fin.ext ?_)
      have hi_nz : Valued.v (P ^ (i : ℕ) * s i) ≠ 0 := heq ▸ htop
      rw [hterm, hterm] at heq
      exact eq_of_exp_mul_pow_eq i.2 i0.2 (hnz i hi_nz) (hnz i0 htop) heq
    have := Valuation.map_sum_eq_of_lt _ (Finset.mem_univ i0) hlt
    rw [hsum, map_zero] at this
    exact htop this.symm
  rintro ⟨i, j⟩
  have := hJ i j
  rw [show Valued.v (g (i, J i)) = M i from rfl, hM i] at this
  exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)

theorem ramificationIdx_mul_inertiaDeg_le_finrank :
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := v.isMaximal
  have := w.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  let b := Module.finBasis (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)
  choose ω hω using fun j ↦ Ideal.Quotient.mk_surjective (b j)
  have hli : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)) := by
    convert b.linearIndependent with j
    exact hω j
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have := (linearIndependent_uniformizer_pow_mul v w ω hli π hπ).fintype_card_le_finrank
  simpa using this

end SemiLocal

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

abbrev CompletionsOver : Type _ := (w : PlacesOver L v) → w.1.adicCompletion L

def tensorMap : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap_tmul (a : v.adicCompletion K) (x : L) :
    tensorMap L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x := by
  simp [tensorMap]

theorem denseRange_algebraMap_completionsOver :
    DenseRange (algebraMap L (CompletionsOver L v)) :=
  denseRange_algebraMap_pi (fun w : PlacesOver L v ↦ w.1) Subtype.val_injective

open scoped Valued in
theorem tensorMap_surjective : Function.Surjective (tensorMap L v) := by
  have hclosed : IsClosed (LinearMap.range (tensorMap L v).toLinearMap :
      Set (CompletionsOver L v)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (Set.range (tensorMap L v)) := by
    refine (denseRange_algebraMap_completionsOver L v).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩
  rw [LinearMap.coe_range] at hclosed
  have h2 : closure (Set.range (tensorMap L v)) = Set.range (tensorMap L v) := hclosed.closure_eq
  rw [← Set.range_eq_univ, ← h2, hdense.closure_eq]

theorem sum_finrank_le :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ finrank K L := by
  rw [← Module.finrank_pi_fintype]
  calc _ ≤ finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
        LinearMap.finrank_le_finrank_of_surjective (f := (tensorMap L v).toLinearMap)
          (tensorMap_surjective L v)
    _ = finrank K L := Module.finrank_baseChange

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) =
      finrank K L := by
  have := v.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ (fun _ ↦ rfl)

theorem sum_finrank_eq :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = finrank K L := by
  refine le_antisymm (sum_finrank_le L v) ?_
  rw [← sum_ramificationIdx_mul_inertiaDeg L v]
  exact Finset.sum_le_sum fun w _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1

theorem finrank_eq_ramificationIdx_mul_inertiaDeg (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (w : PlacesOver L v) _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1)).1
    (by rw [sum_ramificationIdx_mul_inertiaDeg, sum_finrank_eq])
  exact (h ⟨w, inferInstance⟩ (Finset.mem_univ _)).symm

theorem tensorMap_injective : Function.Injective (tensorMap L v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorMap L v).toLinearMap)
    (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_finrank_eq])).2
    (tensorMap_surjective L v)

def tensorEquiv : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap L v) ⟨tensorMap_injective L v, tensorMap_surjective L v⟩

@[simp] theorem tensorEquiv_tmul (a : v.adicCompletion K) (x : L) :
    tensorEquiv L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x :=
  tensorMap_tmul L v a x

@[simp] theorem tensorEquiv_one_tmul (x : L) :
    tensorEquiv L v (1 ⊗ₜ x) = algebraMap L (CompletionsOver L v) x := by
  simp

def tensorMap' : L ⊗[K] v.adicCompletion K →ₐ[L] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (IsScalarTower.toAlgHom K (v.adicCompletion K) _) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap'_tmul (x : L) (a : v.adicCompletion K) :
    tensorMap' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a := by
  simp [tensorMap']

theorem tensorMap'_eq_comp :
    ⇑(tensorMap' L v) = tensorEquiv L v ∘ Algebra.TensorProduct.comm K L (v.adicCompletion K) := by
  have : (tensorMap' L v).restrictScalars K =
      ((tensorEquiv L v).toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toAlgHom :=
    Algebra.TensorProduct.ext' fun x a ↦ by simp [mul_comm]
  exact congrArg DFunLike.coe this

def tensorEquiv' : L ⊗[K] v.adicCompletion K ≃ₐ[L] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap' L v) (by
    rw [tensorMap'_eq_comp]
    exact (tensorEquiv L v).bijective.comp (AlgEquiv.bijective _))

@[simp] theorem tensorEquiv'_tmul (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a :=
  tensorMap'_tmul L v x a

theorem tensorEquiv'_tmul_mul (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by
  rw [map_mul, tensorEquiv'_tmul, map_one, one_mul]

open scoped Valued in

instance isModuleTopology_completionsOver :
    IsModuleTopology (v.adicCompletion K) (CompletionsOver L v) :=
  isModuleTopologyOfFiniteDimensional

def tensorHomeomorph [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)] :
    v.adicCompletion K ⊗[K] L ≃ₜ CompletionsOver L v where
  toEquiv := (tensorEquiv L v).toEquiv
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).toLinearEquiv.toLinearMap
  continuous_invFun := by
    have := IsModuleTopology.toContinuousAdd (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
    exact IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).symm.toLinearEquiv.toLinearMap

@[simp] theorem tensorHomeomorph_apply [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]
    (y : v.adicCompletion K ⊗[K] L) : tensorHomeomorph L v y = tensorEquiv L v y := rfl

end SemiLocal

end

end GroundTheory.Global
end
