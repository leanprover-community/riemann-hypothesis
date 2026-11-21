import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

section
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S)

theorem linv_mono {E E' : Subgroup Λ} (h : E ≤ E') {u : S → ℝ} (hu : LInv j E' u) : LInv j E u :=
  fun γ hγ x => hu γ (h hγ) x

theorem linv_sub {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x - v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_mul {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x * v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_sq {E : Subgroup Λ} {u : S → ℝ} (hu : LInv j E u) : LInv j E (fun x => u x ^ 2) := by
  intro γ hγ x
  simp only [hu γ hγ x]

variable {B K : Subgroup Λ}

theorem card_cosets :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem finite_cosets (h : (B.subgroupOf K).index ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
  Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)

theorem avg_sub (h : (B.subgroupOf K).index ≠ 0) (u v : S → ℝ) (x : S) :
    avg j B K (fun y => u y - v y) x = avg j B K u x - avg j B K v x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

theorem avg_mul_left {a : S → ℝ} (ha : LInv j K a) (b : S → ℝ) (x : S) :
    avg j B K (fun y => a y * b y) x = a x * avg j B K b x := by
  by_cases h : (B.subgroupOf K).index = 0
  · simp [avg, h]
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype]
  have hc : ∀ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)),
      a (j (c.out : Λ) * x) * b (j (c.out : Λ) * x) = a x * b (j (c.out : Λ) * x) := by
    intro c
    rw [ha _ c.out.2 x]
  simp only [hc, ← Finset.mul_sum]
  ring

theorem avg_nonneg {u : S → ℝ} (hu : ∀ y, 0 ≤ u y) (x : S) : 0 ≤ avg j B K u x := by
  unfold avg
  apply mul_nonneg
  · positivity
  · exact finsum_nonneg fun c => hu _

theorem avg_sq_le (h : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (x : S) :
    avg j B K u x ^ 2 ≤ avg j B K (fun y => u y ^ 2) x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hc : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_cosets]
  have hn : (0 : ℝ) < (B.subgroupOf K).index := by exact_mod_cast Nat.pos_of_ne_zero h
  simp only [avg, finsum_eq_sum_of_fintype]
  have key := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) => u (j (c.out : Λ) * x))
  rw [hc] at key
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn_def
  set s := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x)
  set t := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x) ^ 2
  calc (n⁻¹ * s) ^ 2 = n⁻¹ ^ 2 * s ^ 2 := by ring
    _ ≤ n⁻¹ ^ 2 * (n * t) := by gcongr
    _ = n⁻¹ * t := by
      field_simp

end PositivityTheory.KB.SpectralGap.PGap

end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace Pointwise

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] [MeasurableSpace S] (j : Λ →* S) (B : Subgroup Λ)
  (μ : Measure S) (DB : Set S)

abbrev Qt := Quotient (MulAction.orbitRel (B.map j) S)

def pr : S → Qt j B := Quotient.mk _

def nu : Measure (Qt j B) := (μ.restrict DB).map (pr j B)

abbrev HL := Lp ℝ 2 (nu j B μ DB)

def lift (u : S → ℝ) : Qt j B → ℝ := fun q => u q.out

def Good (u : S → ℝ) : Prop := Measurable u ∧ LInv j B u ∧ MemLp u 2 (μ.restrict DB)

variable {j B μ DB}

theorem linv_rel {u : S → ℝ} (hu : LInv j B u) {x y : S} (h : MulAction.orbitRel (B.map j) S x y) :
    u x = u y := by
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨⟨g, hg⟩, rfl⟩ := h
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  exact hu γ hγ y

theorem measurable_pr : Measurable (pr j B) := by
  exact measurable_quotient_mk''

theorem pr_mul {γ : Λ} (hγ : γ ∈ B) (x : S) : pr j B (j γ * x) = pr j B x := by
  unfold pr
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨⟨j γ, Subgroup.mem_map_of_mem j hγ⟩, rfl⟩

theorem lift_pr {u : S → ℝ} (hu : LInv j B u) (x : S) : lift j B u (pr j B x) = u x := by
  exact linv_rel hu (Quotient.mk_out' x)

theorem measurable_lift {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) : Measurable (lift j B u) := by
  refine measurable_from_quotient.mpr ?_
  have : (lift j B u ∘ Quotient.mk'') = u := funext fun x => lift_pr hu x
  rw [this]; exact hm

theorem memLp_lift {u : S → ℝ} (h : Good j B μ DB u) : MemLp (lift j B u) 2 (nu j B μ DB) := by
  obtain ⟨hm, hi, hmem⟩ := h
  unfold nu
  rw [memLp_map_measure_iff (measurable_lift hm hi).aestronglyMeasurable measurable_pr.aemeasurable]
  have : (lift j B u ∘ pr j B) = u := funext fun x => lift_pr hi x
  rw [this]; exact hmem

variable (j B μ DB) in

def cls (u : S → ℝ) : HL j B μ DB := by
  classical exact if h : Good j B μ DB u then (memLp_lift h).toLp (lift j B u) else 0

theorem good_iff {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) :
    Good j B μ DB u ↔ IntegrableOn (fun x => u x ^ 2) DB μ := by
  unfold Good
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨fun h => h.2.2, fun h => ⟨hm, hu, h⟩⟩

theorem good_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    Good j B μ DB (fun x => u x - v x) := by
  refine ⟨hu.1.sub hv.1, fun γ hγ x => ?_, hu.2.2.sub hv.2.2⟩
  show u (j γ * x) - v (j γ * x) = u x - v x
  rw [hu.2.1 γ hγ x, hv.2.1 γ hγ x]

theorem cls_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB (fun x => u x - v x) = cls j B μ DB u - cls j B μ DB v := by
  unfold cls
  rw [dif_pos (good_sub hu hv), dif_pos hu, dif_pos hv]
  exact MemLp.toLp_sub (memLp_lift hu) (memLp_lift hv)

theorem cls_inner {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    ⟪cls j B μ DB u, cls j B μ DB v⟫_ℝ = ∫ x in DB, u x * v x ∂μ := by
  unfold cls
  rw [dif_pos hu, dif_pos hv, L2.inner_def]
  have h1 := (memLp_lift hu).coeFn_toLp
  have h2 := (memLp_lift hv).coeFn_toLp
  have hcongr : (fun q => ⟪((memLp_lift hu).toLp (lift j B u) : Qt j B → ℝ) q,
      ((memLp_lift hv).toLp (lift j B v) : Qt j B → ℝ) q⟫_ℝ) =ᵐ[nu j B μ DB]
      fun q => lift j B u q * lift j B v q := by
    filter_upwards [h1, h2] with q hq1 hq2
    rw [hq1, hq2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae hcongr]
  have hm : Measurable (fun q => lift j B u q * lift j B v q) :=
    (measurable_lift hu.1 hu.2.1).mul (measurable_lift hv.1 hv.2.1)
  unfold nu
  rw [integral_map measurable_pr.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem cls_norm_sq {u : S → ℝ} (hu : Good j B μ DB u) :
    ‖cls j B μ DB u‖ ^ 2 = ∫ x in DB, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, cls_inner hu hu]
  simp only [sq]

theorem cls_surj (f : HL j B μ DB) : ∃ u, Good j B μ DB u ∧ cls j B μ DB u = f := by
  have hf := (Lp.aestronglyMeasurable f).aemeasurable
  set g := hf.mk f with hgdef
  have hg : Measurable g := hf.measurable_mk
  have hfg : (f : Qt j B → ℝ) =ᵐ[nu j B μ DB] g := hf.ae_eq_mk
  have hinv : LInv j B (g ∘ pr j B) := fun γ hγ x => by
    show g (pr j B (j γ * x)) = g (pr j B x)
    rw [pr_mul hγ x]
  have hLg : MemLp g 2 (nu j B μ DB) := (Lp.memLp f).ae_eq hfg
  have hgood : Good j B μ DB (g ∘ pr j B) := by
    refine ⟨hg.comp measurable_pr, hinv, ?_⟩
    unfold nu at hLg
    exact (memLp_map_measure_iff hg.aestronglyMeasurable measurable_pr.aemeasurable).1 hLg
  refine ⟨g ∘ pr j B, hgood, ?_⟩
  have hl : lift j B (g ∘ pr j B) = g := funext fun q => by
    show g (Quotient.mk _ q.out) = g q
    rw [Quotient.out_eq]
  unfold cls
  rw [dif_pos hgood]
  apply Lp.ext
  filter_upwards [(memLp_lift hgood).coeFn_toLp, hfg] with q h1 h2
  rw [h1, hl, h2]

theorem cls_eq_iff {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB u = cls j B μ DB v ↔ u =ᵐ[μ.restrict DB] v := by
  unfold cls; rw [dif_pos hu, dif_pos hv, MemLp.toLp_eq_toLp_iff]
  unfold nu Filter.EventuallyEq
  rw [ae_map_iff measurable_pr.aemeasurable
    (measurableSet_eq_fun (measurable_lift hu.1 hu.2.1) (measurable_lift hv.1 hv.2.1))]
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem countable_map [Countable Λ] : Countable (B.map j) := by
  have hc : ((B.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact hc.to_subtype

theorem ae_spread [Countable Λ] [MeasurableMul S] [μ.IsMulLeftInvariant]
    (hD : IsFundamentalDomain (B.map j) DB μ) {u v : S → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hiu : LInv j B u) (hiv : LInv j B v) (h : u =ᵐ[μ.restrict DB] v) : u =ᵐ[μ] v := by
  haveI := countable_map (j := j) (B := B)
  have inv : ∀ w : S → ℝ, LInv j B w → ∀ (g : B.map j) (x : S), w (g • x) = w x :=
    fun w hw g x => linv_rel hw (by rw [MulAction.orbitRel_apply]; exact MulAction.mem_orbit x g)
  have htm : MeasurableSet {x | u x ≠ v x} := (measurableSet_eq_fun hu hv).compl
  have ht : ∀ g : B.map j, g • {x | u x ≠ v x} = {x | u x ≠ v x} := by
    intro g
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq]
    rw [inv u hiu g⁻¹ x, inv v hiv g⁻¹ x]
  have hts : μ ({x | u x ≠ v x} ∩ DB) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h
  exact ae_iff.2 (hD.measure_zero_of_invariant _ ht hts)

theorem ae_translate [MeasurableMul S] [μ.IsMulLeftInvariant] {u v : S → ℝ} (g : S)
    (h : u =ᵐ[μ] v) : (fun x => u (g * x)) =ᵐ[μ] fun x => v (g * x) := by
  exact (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq h

end PositivityTheory.KB.SpectralGap.PGap

end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem idx_ne {Λ : Type} [Group Λ] {B E K : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K)
    (h : (B.subgroupOf K).index ≠ 0) : (B.subgroupOf E).index ≠ 0 ∧ (E.subgroupOf K).index ≠ 0 := by
  have h' : (B.subgroupOf E).index * (E.subgroupOf K).index = (B.subgroupOf K).index :=
    Subgroup.relIndex_mul_relIndex B E K hBE hEK
  rw [← h'] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem exists_not_mem {Λ : Type} [Group Λ] {B E : Subgroup Λ} (h : 25 ≤ (B.subgroupOf E).index) :
    ∃ g ∈ E, g ∉ B := by
  by_contra hc
  push_neg at hc
  have htop : B.subgroupOf E = ⊤ := Subgroup.subgroupOf_eq_top.mpr (fun g hg => hc g hg)
  rw [htop, Subgroup.index_top] at h
  omega

theorem twoTr_le {Λ : Type} [Group Λ] {E K G : Subgroup Λ} (htwo : TwoTr E K) (hEG : E ≤ G)
    {g : Λ} (hgK : g ∈ K) (hgE : g ∉ E) (hgG : g ∈ G) : K ≤ G := by
  intro g' hg'
  by_cases h : g' ∈ E
  · exact hEG h
  · obtain ⟨e, he, e', he', rfl⟩ := htwo g hgK hgE g' hg' h
    exact G.mul_mem (G.mul_mem (hEG he) hgG) (hEG he')

theorem t_trick {I X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10) :
    |I| ≤ 1 / 5 * (Real.sqrt X * Real.sqrt Y) := by
  set s := Real.sqrt X with hs_def
  set r := Real.sqrt Y with hr_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hXs : X = s ^ 2 := (Real.sq_sqrt hX).symm
  have hYr : Y = r ^ 2 := (Real.sq_sqrt hY).symm
  have key : ∀ δ : ℝ, 0 < δ → 10 * |I| ≤ 2 * (s * r) + δ * (r + s) := by
    intro δ hδ
    have ha : 0 < r + δ := by linarith
    have hb : 0 < s + δ := by linarith
    have ht : 0 < (r + δ) / (s + δ) := div_pos ha hb
    have h1 := h _ ht
    have e1 : (r + δ) / (s + δ) * X ≤ (r + δ) * s := by
      rw [hXs, div_mul_eq_mul_div, div_le_iff₀ hb]
      nlinarith [mul_nonneg ha.le hs, mul_nonneg (mul_nonneg ha.le hs) hδ.le]
    have e2 : Y / ((r + δ) / (s + δ)) ≤ r * (s + δ) := by
      rw [hYr, div_div_eq_mul_div, div_le_iff₀ ha]
      nlinarith [mul_nonneg hb.le hr, mul_nonneg (mul_nonneg hb.le hr) hδ.le]
    nlinarith
  by_contra hc
  push_neg at hc
  set δ := (|I| - 1 / 5 * (s * r)) * 10 / (r + s + 1) with hδ_def
  have hpos : 0 < r + s + 1 := by linarith
  have hδ : 0 < δ := by
    apply div_pos _ hpos
    linarith
  have hδ' : δ * (r + s + 1) = (|I| - 1 / 5 * (s * r)) * 10 := by
    rw [hδ_def]
    field_simp
  nlinarith [key δ hδ]

section Unf

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  (μ : Measure S) [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B K : Subgroup Λ} (hBK : B ≤ K)
  (hi : (B.subgroupOf K).index ≠ 0)

include μ hU hj hBK hi

theorem u_inv {u : S → ℝ} (hu : LInv j B u) : LInv j K (avg j B K u) :=
  (hU Λ S μ j hj B K hBK hi).1 u hu

theorem u_id {u : S → ℝ} (hu : LInv j K u) : avg j B K u = u :=
  (hU Λ S μ j hj B K hBK hi).2.1 u hu

theorem u_meas {u : S → ℝ} (hu : Measurable u) : Measurable (avg j B K u) :=
  (hU Λ S μ j hj B K hBK hi).2.2.1 u hu

theorem u_trans {E : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K) {u : S → ℝ} (hu : LInv j B u) :
    avg j E K (avg j B E u) = avg j B K u :=
  (hU Λ S μ j hj B K hBK hi).2.2.2.1 E hBE hEK u hu

theorem u_dom {D : Set S} (hD : IsFundamentalDomain (K.map j) D μ) :
    ∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ :=
  ((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).1

theorem u_measure {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) : μ D' = (B.subgroupOf K).index * μ D :=
  (((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').1

theorem u_int_iff {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) :
    IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ :=
  ((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).1

theorem u_int_eq {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u)
    (hint : IntegrableOn u D' μ) :
    ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ :=
  (((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).2 hint).2

theorem u_int_avg {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u)
    (hint : IntegrableOn u D' μ) : IntegrableOn (avg j B K u) D μ :=
  (((((hU Λ S μ j hj B K hBK hi).2.2.2.2 D hD).2 D' hD').2 u hm hu).2 hint).1

theorem int_iff_inv {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j K u) :
    IntegrableOn u D' μ ↔ IntegrableOn u D μ := by
  have hB : LInv j B u := fun γ hγ x => hu γ (hBK hγ) x
  have habs : LInv j K (fun y => |u y|) := by
    intro γ hγ x
    simp only [hu γ hγ x]
  rw [u_int_iff μ hU hj hBK hi hD hD' hm hB, u_id μ hU hj hBK hi habs]
  unfold IntegrableOn
  simp_rw [← Real.norm_eq_abs]
  exact integrable_norm_iff hm.aestronglyMeasurable

theorem int_eq_inv {D D' : Set S} (hD : IsFundamentalDomain (K.map j) D μ)
    (hD' : IsFundamentalDomain (B.map j) D' μ) {u : S → ℝ} (hm : Measurable u) (hu : LInv j K u)
    (hint : IntegrableOn u D' μ) :
    ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, u x ∂μ := by
  have hB : LInv j B u := fun γ hγ x => hu γ (hBK hγ) x
  rw [u_int_eq μ hU hj hBK hi hD hD' hm hB hint, u_id μ hU hj hBK hi hu]

end Unf

section Sub

variable {Λ S : Type} [Group Λ] [Group S] [MeasurableSpace S] (j : Λ →* S) (B : Subgroup Λ)
  (μ : Measure S) (DB : Set S)

def R (E : Subgroup Λ) : Set (HL j B μ DB) :=
  {f | ∃ u, Good j B μ DB u ∧ Good j B μ DB (avg j B E u) ∧
    f = cls j B μ DB (fun x => u x - avg j B E u x)}

def W (E : Subgroup Λ) : Submodule ℝ (HL j B μ DB) := (Submodule.span ℝ (R j B μ DB E))ᗮ

theorem W_closed (E : Subgroup Λ) : IsClosed (W j B μ DB E : Set (HL j B μ DB)) :=
  Submodule.isClosed_orthogonal _

end Sub

theorem integrableOn_mul {S : Type} [MeasurableSpace S] {μ : Measure S} {D : Set S} {u v : S → ℝ}
    (hu : MemLp u 2 (μ.restrict D)) (hv : MemLp v 2 (μ.restrict D)) :
    IntegrableOn (fun x => u x * v x) D μ :=
  MemLp.integrable_mul (p := 2) (q := 2) hu hv

section W

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem good_avg {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u) :
    Good j B μ DB (avg j B E u) := by
  obtain ⟨hm, hinv, hL⟩ := hu
  have hmA : Measurable (avg j B E u) := u_meas μ hU hj hBE hi hm
  have hEinv : LInv j E (avg j B E u) := u_inv μ hU hj hBE hi hinv
  have hBinv : LInv j B (avg j B E u) := fun γ hγ x => hEinv γ (hBE hγ) x
  refine ⟨hmA, hBinv, ?_⟩
  have hsq : IntegrableOn (fun y => u y ^ 2) DB μ := hL.integrable_sq
  have hsqinv : LInv j B (fun y => u y ^ 2) := by
    intro γ hγ x
    simp only [hinv γ hγ x]
  have hsqm : Measurable (fun y => u y ^ 2) := hm.pow_const 2
  have h1 : IntegrableOn (avg j B E fun y => |u y ^ 2|) DE μ :=
    (u_int_iff μ hU hj hBE hi hDE hDB hsqm hsqinv).1 hsq
  have habs : (fun y => |u y ^ 2|) = fun y => u y ^ 2 := funext fun y => abs_of_nonneg (sq_nonneg _)
  rw [habs] at h1
  have h2 : IntegrableOn (fun x => avg j B E u x ^ 2) DE μ := by
    refine Integrable.mono' h1 (hmA.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact avg_sq_le j hi u x
  have hsqE : LInv j E (fun x => avg j B E u x ^ 2) := by
    intro γ hγ x
    simp only [hEinv γ hγ x]
  have h3 : IntegrableOn (fun x => avg j B E u x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBE hi hDE hDB (hmA.pow_const 2) hsqE).2 h2
  exact (memLp_two_iff_integrable_sq hmA.aestronglyMeasurable).2 h3

theorem ip_zero {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {a r : S → ℝ} (ha : Good j B μ DB a) (haE : LInv j E a)
    (hr : Good j B μ DB r) (hr' : Good j B μ DB (avg j B E r)) :
    ∫ x in DB, a x * (r x - avg j B E r x) ∂μ = 0 := by
  obtain ⟨ham, hainv, haL⟩ := ha
  obtain ⟨hrm, hrinv, hrL⟩ := hr
  obtain ⟨hsm, hsinv, hsL⟩ := hr'
  have haB : LInv j B a := fun γ hγ x => haE γ (hBE hγ) x
  have hint1 : IntegrableOn (fun x => a x * r x) DB μ := integrableOn_mul haL hrL
  have hint2 : IntegrableOn (fun x => a x * avg j B E r x) DB μ := integrableOn_mul haL hsL
  have hsE : LInv j E (avg j B E r) := u_inv μ hU hj hBE hi hrinv
  have harB : LInv j B (fun x => a x * r x) := by
    intro γ hγ x
    simp only [haB γ hγ x, hrinv γ hγ x]
  have haE2 : LInv j E (fun x => a x * avg j B E r x) := by
    intro γ hγ x
    simp only [haE γ hγ x, hsE γ hγ x]
  have e1 : ∫ x in DB, a x * r x ∂μ =
      (B.subgroupOf E).index * ∫ x in DE, avg j B E (fun y => a y * r y) x ∂μ :=
    u_int_eq μ hU hj hBE hi hDE hDB (ham.mul hrm) harB hint1
  have e2 : ∫ x in DB, a x * avg j B E r x ∂μ =
      (B.subgroupOf E).index * ∫ x in DE, a x * avg j B E r x ∂μ :=
    int_eq_inv μ hU hj hBE hi hDE hDB (ham.mul hsm) haE2 hint2
  simp only [avg_mul_left j haE r] at e1
  simp_rw [mul_sub]
  rw [integral_sub hint1 hint2, e1, e2, sub_self]

theorem mem_W_of_inv {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u) (huE : LInv j E u) :
    cls j B μ DB u ∈ W j B μ DB E := by
  unfold W
  rw [Submodule.mem_orthogonal]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, hr', rfl⟩ := hx
    have hd : Good j B μ DB (fun x => r x - avg j B E r x) :=
      ⟨hr.1.sub hr'.1, fun γ hγ x => by simp only [hr.2.1 γ hγ x, hr'.2.1 γ hγ x], hr.2.2.sub hr'.2.2⟩
    rw [cls_inner hd hu]
    calc ∫ x in DB, (r x - avg j B E r x) * u x ∂μ = ∫ x in DB, u x * (r x - avg j B E r x) ∂μ := by
          congr 1
          funext x
          ring
      _ = 0 := ip_zero hU hj hDB hBE hi hDE hu huE hr hr'
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem ae_eq_cosetAvg_of_mem_invariantSubspace {E : Subgroup Λ} (hBE : B ≤ E) (hi : (B.subgroupOf E).index ≠ 0) {DE : Set S}
    (hDE : IsFundamentalDomain (E.map j) DE μ) {u : S → ℝ} (hu : Good j B μ DB u)
    (hW : cls j B μ DB u ∈ W j B μ DB E) : u =ᵐ[μ.restrict DB] avg j B E u := by
  have hA : Good j B μ DB (avg j B E u) := good_avg hU hj hDB hBE hi hDE hu
  have hAE : LInv j E (avg j B E u) := u_inv μ hU hj hBE hi hu.2.1
  have hd : Good j B μ DB (fun x => u x - avg j B E u x) :=
    ⟨hu.1.sub hA.1, fun γ hγ x => by simp only [hu.2.1 γ hγ x, hA.2.1 γ hγ x], hu.2.2.sub hA.2.2⟩
  have hR : cls j B μ DB (fun x => u x - avg j B E u x) ∈ R j B μ DB E := ⟨u, hu, hA, rfl⟩
  have h1 : ⟪cls j B μ DB (fun x => u x - avg j B E u x), cls j B μ DB u⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 hW _ (Submodule.subset_span hR)
  have h2 : ⟪cls j B μ DB (fun x => u x - avg j B E u x), cls j B μ DB (avg j B E u)⟫_ℝ = 0 := by
    rw [cls_inner hd hA]
    calc ∫ x in DB, (u x - avg j B E u x) * avg j B E u x ∂μ =
          ∫ x in DB, avg j B E u x * (u x - avg j B E u x) ∂μ := by
          congr 1
          funext x
          ring
      _ = 0 := ip_zero hU hj hDB hBE hi hDE hA hAE hu hA
  have hdd : cls j B μ DB (fun x => u x - avg j B E u x) =
      cls j B μ DB u - cls j B μ DB (avg j B E u) := cls_sub hu hA
  have h3 : ⟪cls j B μ DB (fun x => u x - avg j B E u x),
      cls j B μ DB (fun x => u x - avg j B E u x)⟫_ℝ = 0 := by
    nth_rewrite 2 [hdd]
    rw [inner_sub_right, h1, h2, sub_self]
  rw [inner_self_eq_zero, hdd, sub_eq_zero] at h3
  exact (cls_eq_iff hu hA).1 h3

theorem W_anti {E K : Subgroup Λ} (hBE : B ≤ E) (hEK : E ≤ K) (hiK : (B.subgroupOf K).index ≠ 0)
    {DE DK : Set S} (hDE : IsFundamentalDomain (E.map j) DE μ)
    (hDK : IsFundamentalDomain (K.map j) DK μ) : W j B μ DB K ≤ W j B μ DB E := by
  have hiE : (B.subgroupOf E).index ≠ 0 := (idx_ne hBE hEK hiK).1
  have hBK : B ≤ K := hBE.trans hEK
  unfold W
  apply Submodule.orthogonal_le
  rw [Submodule.span_le]
  rintro f ⟨r, hr, hr', rfl⟩
  have hK1 : Good j B μ DB (avg j B K r) := good_avg hU hj hDB hBK hiK hDK hr
  have hK2 : Good j B μ DB (avg j B K (avg j B E r)) := good_avg hU hj hDB hBK hiK hDK hr'
  have htow : avg j B K (avg j B E r) = avg j B K r := by
    rw [← u_trans μ hU hj hBK hiK hBE hEK hr'.2.1,
      u_id μ hU hj hBE hiE (u_inv μ hU hj hBE hiE hr.2.1),
      u_trans μ hU hj hBK hiK hBE hEK hr.2.1]
  have hd1 : Good j B μ DB (fun x => r x - avg j B K r x) :=
    ⟨hr.1.sub hK1.1, fun γ hγ x => by simp only [hr.2.1 γ hγ x, hK1.2.1 γ hγ x], hr.2.2.sub hK1.2.2⟩
  have hd2 : Good j B μ DB (fun x => avg j B E r x - avg j B K (avg j B E r) x) :=
    ⟨hr'.1.sub hK2.1, fun γ hγ x => by simp only [hr'.2.1 γ hγ x, hK2.2.1 γ hγ x], hr'.2.2.sub hK2.2.2⟩
  have heq : cls j B μ DB (fun x => r x - avg j B E r x) =
      cls j B μ DB (fun x => r x - avg j B K r x) -
        cls j B μ DB (fun x => avg j B E r x - avg j B K (avg j B E r) x) := by
    rw [← cls_sub hd1 hd2]
    congr 1
    funext x
    rw [htow]
    ring
  show _ ∈ Submodule.span ℝ (R j B μ DB K)
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨r, hr, hK1, rfl⟩)
    (Submodule.subset_span ⟨avg j B E r, hr', hK2, rfl⟩)

end W

end PositivityTheory.KB.SpectralGap.PGap

end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem pt_bound {z p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) (h : z ^ 2 ≤ 1 / 25 * (p * q)) :
    |z| ≤ (t * p + q / t) / 10 := by
  have hts : t * (q / t) = q := by field_simp
  have hw : 0 ≤ (t * p + q / t) / 10 := by positivity
  have h4 : z ^ 2 ≤ ((t * p + q / t) / 10) ^ 2 := by
    nlinarith [sq_nonneg (t * p - q / t)]
  exact abs_le_of_sq_le_sq' h4 hw |> fun h => abs_le.mpr h

section Ang

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem perp_avg {K : Subgroup Λ} (hBK : B ≤ K) (hiK : (B.subgroupOf K).index ≠ 0) {DK : Set S}
    (hDK : IsFundamentalDomain (K.map j) DK μ) {a : S → ℝ} (ha : Good j B μ DB a)
    (hperp : cls j B μ DB a ∈ (W j B μ DB K)ᗮ) : cls j B μ DB (avg j B K a) = 0 := by
  have hm := good_avg hU hj hDB hBK hiK hDK ha
  have hmK : LInv j K (avg j B K a) := u_inv μ hU hj hBK hiK ha.2.1
  have hmW := mem_W_of_inv hU hj hDB hBK hiK hDK hm hmK
  have h0 := Submodule.inner_right_of_mem_orthogonal hmW hperp
  rw [cls_inner hm ha] at h0
  have key : ∫ x in DB, avg j B K a x ^ 2 ∂μ = ∫ x in DB, avg j B K a x * a x ∂μ := by
    have e : (fun x => avg j B K a x ^ 2) = fun x => avg j B K a x * avg j B K a x := by
      funext x; ring
    rw [e, u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * avg j B K a x) (hm.1.mul hm.1) (linv_mul j hm.2.1 hm.2.1)
        (integrableOn_mul hm.2.2 hm.2.2),
      u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * a x) (hm.1.mul ha.1) (linv_mul j hm.2.1 ha.2.1)
        (integrableOn_mul hm.2.2 ha.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hmK, avg_mul_left j hmK, u_id μ hU hj hBK hiK hmK]
  have hn : ‖cls j B μ DB (avg j B K a)‖ ^ 2 = 0 := by rw [cls_norm_sq hm, key, h0]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hn)

theorem core (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ) {a b : S → ℝ} (ha : Good j B μ DB a)
    (haE : LInv j E a) (hz : ∀ x, avg j B K a x = 0) (hb : Good j B μ DB b) (hbE : LInv j E' b) :
    |∫ x in DB, a x * b x ∂μ| ≤
      1 / 5 * (Real.sqrt (∫ x in DB, a x ^ 2 ∂μ) * Real.sqrt (∫ x in DB, b x ^ 2 ∂μ)) := by
  have hBK : B ≤ K := hB ▸ inf_le_left.trans hEK
  have hab := integrableOn_mul ha.2.2 hb.2.2
  have haa := integrableOn_mul ha.2.2 ha.2.2
  have hbb := integrableOn_mul hb.2.2 hb.2.2
  have sa : (fun x => a x ^ 2) = fun x => a x * a x := by funext x; ring
  have sb : (fun x => b x ^ 2) = fun x => b x * b x := by funext x; ring
  rw [sa, sb]
  rw [u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb]
  have iab := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab
  have iaa := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa
  have ibb := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hiK
  set I := ∫ x in DK, avg j B K (fun y => a y * b y) x ∂μ
  set X := ∫ x in DK, avg j B K (fun y => a y * a y) x ∂μ
  set Y := ∫ x in DK, avg j B K (fun y => b y * b y) x ∂μ
  have pa : ∀ x, 0 ≤ avg j B K (fun y => a y * a y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have pb : ∀ x, 0 ≤ avg j B K (fun y => b y * b y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have hX : 0 ≤ X := integral_nonneg pa
  have hY : 0 ≤ Y := integral_nonneg pb
  have hpt : ∀ x, avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y * a y) x * avg j B K (fun y => b y * b y) x) := by
    intro x
    have := hD Λ S j B E E' K hB hEK hE'K hiK htwo hbig a b haE hbE x (hz x)
    simpa only [sq] using this
  have ht : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10 := by
    intro t ht
    calc |I| ≤ ∫ x in DK, |avg j B K (fun y => a y * b y) x| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.restrict DK)
            (fun x => avg j B K (fun y => a y * b y) x)
      _ ≤ ∫ x in DK, (t * avg j B K (fun y => a y * a y) x + avg j B K (fun y => b y * b y) x / t) / 10 ∂μ :=
          integral_mono iab.abs (((iaa.const_mul t).add (ibb.div_const t)).div_const 10)
            fun x => pt_bound (pa x) (pb x) ht (hpt x)
      _ = (t * X + Y / t) / 10 := by
          rw [integral_div, integral_add (iaa.const_mul t) (ibb.div_const t), integral_const_mul,
            integral_div]
  have h1 := t_trick hX hY ht
  rw [abs_mul, abs_of_pos hn0, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le]
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  calc n * |I| ≤ n * (1 / 5 * (Real.sqrt X * Real.sqrt Y)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = 1 / 5 * (Real.sqrt n * Real.sqrt X * (Real.sqrt n * Real.sqrt Y)) := by
      linear_combination (-(1 / 5 * (Real.sqrt X * Real.sqrt Y))) * hs

theorem angle (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK DE DE' : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ)
    (hDE : IsFundamentalDomain (E.map j) DE μ) (hDE' : IsFundamentalDomain (E'.map j) DE' μ) :
    ∀ u ∈ W j B μ DB E, u ∈ (W j B μ DB K)ᗮ → ∀ u' ∈ W j B μ DB E',
      |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖) := by
  intro u hu hperp u' hu'
  have hBE : B ≤ E := hB ▸ inf_le_left
  have hBE' : B ≤ E' := hB ▸ inf_le_right
  have hBK : B ≤ K := hBE.trans hEK
  have hiE := (idx_ne hBE hEK hiK).1
  have hiE' := (idx_ne hBE' hE'K hiK).1
  obtain ⟨a, ha, rfl⟩ := cls_surj u
  obtain ⟨b, hb, rfl⟩ := cls_surj u'
  have ha1 := good_avg hU hj hDB hBE hiE hDE ha
  have ha1E : LInv j E (avg j B E a) := u_inv μ hU hj hBE hiE ha.2.1
  have e1 : cls j B μ DB a = cls j B μ DB (avg j B E a) :=
    (cls_eq_iff ha ha1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE ha hu)
  have hb1 := good_avg hU hj hDB hBE' hiE' hDE' hb
  have hb1E : LInv j E' (avg j B E' b) := u_inv μ hU hj hBE' hiE' hb.2.1
  have e2 : cls j B μ DB b = cls j B μ DB (avg j B E' b) :=
    (cls_eq_iff hb hb1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE' hiE' hDE' hb hu')
  rw [e1] at hperp ⊢
  rw [e2]
  have hm := good_avg hU hj hDB hBK hiK hDK ha1
  have hmK : LInv j K (avg j B K (avg j B E a)) := u_inv μ hU hj hBK hiK ha1.2.1
  have h0 := perp_avg hU hj hDB hBK hiK hDK ha1 hperp
  have ha2 := good_sub ha1 hm
  have e3 : cls j B μ DB (avg j B E a) =
      cls j B μ DB (fun x => avg j B E a x - avg j B K (avg j B E a) x) := by
    rw [cls_sub ha1 hm, h0, sub_zero]
  rw [e3]
  have ha2E : LInv j E (fun x => avg j B E a x - avg j B K (avg j B E a) x) :=
    linv_sub j ha1E (linv_mono j hEK hmK)
  have hz : ∀ x, avg j B K (fun x => avg j B E a x - avg j B K (avg j B E a) x) x = 0 := by
    intro x
    rw [avg_sub j hiK, u_id μ hU hj hBK hiK hmK, sub_self]
  rw [cls_inner ha2 hb1, ← Real.sqrt_sq (norm_nonneg (cls j B μ DB _)),
    ← Real.sqrt_sq (norm_nonneg (cls j B μ DB (avg j B E' b))), cls_norm_sq ha2, cls_norm_sq hb1]
  exact core hU hj hDB hD hB hEK hE'K hiK htwo hbig hDK ha2 ha2E hz hb1 hb1E

end Ang

end PositivityTheory.KB.SpectralGap.PGap

end
end

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap

open PGap

theorem gapAbs_of : Hilb → Design → Unfold → AEConst → GapAbs := by
  intro hH hD hU hA Λ S _ _ _ _ _ _ _ _ _ _ μ _ j hj K₀ K₁ K₂ hT hdense D₀ D₁ D₂ hD₀ hD₁ hD₂ hfin h01
    w hwm hwi hw2 hw0
  set B := K₀ ⊓ K₁ ⊓ K₂ with hBdef
  have hBE1 : B ≤ K₀ ⊓ K₁ := inf_le_left
  have hBE2 : B ≤ K₀ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hBE3 : B ≤ K₁ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hE1K0 : K₀ ⊓ K₁ ≤ K₀ := inf_le_left
  have hE1K1 : K₀ ⊓ K₁ ≤ K₁ := inf_le_right
  have hE2K0 : K₀ ⊓ K₂ ≤ K₀ := inf_le_left
  have hE2K2 : K₀ ⊓ K₂ ≤ K₂ := inf_le_right
  have hE3K1 : K₁ ⊓ K₂ ≤ K₁ := inf_le_left
  have hE3K2 : K₁ ⊓ K₂ ≤ K₂ := inf_le_right
  have hBK0 : B ≤ K₀ := hBE1.trans hE1K0
  have hBK1 : B ≤ K₁ := hBE1.trans hE1K1
  have i0 : (B.subgroupOf K₀).index ≠ 0 := hT.fin₀
  have i1 : (B.subgroupOf K₁).index ≠ 0 := hT.fin₁
  have i2 : (B.subgroupOf K₂).index ≠ 0 := hT.fin₂
  have iBE1 := (idx_ne hBE1 hE1K0 i0).1
  have iE1K0 := (idx_ne hBE1 hE1K0 i0).2
  have iE1K1 := (idx_ne hBE1 hE1K1 i1).2
  have iBE2 := (idx_ne hBE2 hE2K0 i0).1
  have iE2K0 := (idx_ne hBE2 hE2K0 i0).2
  have iBE3 := (idx_ne hBE3 hE3K1 i1).1
  have iE3K1 := (idx_ne hBE3 hE3K1 i1).2
  obtain ⟨DB, hDB⟩ := u_dom μ hU hj hBK0 i0 hD₀
  obtain ⟨DE1, hDE1⟩ := u_dom μ hU hj hE1K0 iE1K0 hD₀
  obtain ⟨DE2, hDE2⟩ := u_dom μ hU hj hE2K0 iE2K0 hD₀
  obtain ⟨DE3, hDE3⟩ := u_dom μ hU hj hE3K1 iE3K1 hD₁

  have hm0 := u_measure μ hU hj hBK0 i0 hD₀ hDB
  have hm1 := u_measure μ hU hj hBK1 i1 hD₁ hDB
  have : Countable (K₀.map j) := countable_map
  have hD0ne : μ D₀ ≠ 0 := hD₀.measure_ne_zero (NeZero.ne μ)
  have hidx : (B.subgroupOf K₀).index = (B.subgroupOf K₁).index := by
    have h : ((B.subgroupOf K₀).index : ENNReal) * μ D₀ = (B.subgroupOf K₁).index * μ D₀ := by
      rw [← hm0, hm1, h01]
    exact_mod_cast (ENNReal.mul_left_inj hD0ne hfin.ne).1 h
  have hDBfin : μ DB < ⊤ := by
    rw [hm0]; exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin
  have : IsFiniteMeasure (μ.restrict DB) := isFiniteMeasure_restrict.2 hDBfin.ne
  have : IsFiniteMeasure (μ.restrict D₁) := isFiniteMeasure_restrict.2 (h01 ▸ hfin).ne

  have hwB : LInv j B w := linv_mono j hBK1 hwi
  have hw2B : IntegrableOn (fun x => w x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK1 i1 hD₁ hDB (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
  have hwG : Good j B μ DB w := (good_iff hwm hwB).2 hw2B

  set v := avg j (K₀ ⊓ K₁) K₀ w with hv
  have hvm : Measurable v := u_meas μ hU hj hE1K0 iE1K0 hwm
  have hvK : LInv j K₀ v := u_inv μ hU hj hE1K0 iE1K0 (linv_mono j hE1K1 hwi)
  have hv2 : IntegrableOn (fun x => v x ^ 2) D₀ μ := by
    have h1 : IntegrableOn (fun x => w x ^ 2) DE1 μ :=
      (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
    rw [u_int_iff μ hU hj hE1K0 iE1K0 hD₀ hDE1 (hwm.pow_const 2)
      (linv_sq j (linv_mono j hE1K1 hwi))] at h1
    have e : (avg j (K₀ ⊓ K₁) K₀ fun y => |w y ^ 2|) = avg j (K₀ ⊓ K₁) K₀ fun y => w y ^ 2 := by
      congr 1; funext y; exact abs_of_nonneg (sq_nonneg _)
    rw [e] at h1
    refine h1.mono' (hvm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact avg_sq_le j iE1K0 w x
  have hv2B : IntegrableOn (fun x => v x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK0 i0 hD₀ hDB (hvm.pow_const 2) (linv_sq j hvK)).2 hv2
  have hvG : Good j B μ DB v := (good_iff hvm (linv_mono j hBK0 hvK)).2 hv2B

  have hwint1 : IntegrableOn w D₁ μ :=
    ((memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2 hw2).integrable (by norm_num)
  have hwE1 : IntegrableOn w DE1 μ := (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi).2 hwint1
  have hv0 : ∫ x in D₀, v x ∂μ = 0 := by
    have e1 := int_eq_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi hwE1
    have e2 := u_int_eq μ hU hj hE1K0 iE1K0 hD₀ hDE1 hwm (linv_mono j hE1K1 hwi) hwE1
    rw [hw0, mul_zero] at e1
    rw [e1] at e2
    have hne : (((K₀ ⊓ K₁).subgroupOf K₀).index : ℝ) ≠ 0 := by exact_mod_cast iE1K0
    exact (mul_eq_zero.1 e2.symm).resolve_left hne

  have hker : cls j B μ DB v ∈
      (W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) ⊓ W j B μ DB (K₁ ⊓ K₂))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro f hf
    obtain ⟨F, hF, rfl⟩ := cls_surj f
    rw [Submodule.mem_inf, Submodule.mem_inf] at hf
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf
    have inv : ∀ {E : Subgroup Λ}, B ≤ E → (B.subgroupOf E).index ≠ 0 → ∀ {DE : Set S},
        IsFundamentalDomain (E.map j) DE μ → cls j B μ DB F ∈ W j B μ DB E →
        ∀ γ ∈ E, (fun x => F (j γ * x)) =ᵐ[μ] F := by
      intro E hBE hiE DE hDE hW γ hγ
      have hae := ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE hF hW
      have hG := good_avg hU hj hDB hBE hiE hDE hF
      have hsp := ae_spread hDB hF.1 hG.1 hF.2.1 hG.2.1 hae
      have hinv := u_inv μ hU hj hBE hiE hF.2.1
      have e : (fun x => avg j B E F (j γ * x)) = avg j B E F := funext fun x => hinv γ hγ x
      exact ((ae_translate (j γ) hsp).trans (Filter.EventuallyEq.of_eq e)).trans hsp.symm
    let G : Subgroup Λ :=
      { carrier := {γ | (fun x => F (j γ * x)) =ᵐ[μ] F}
        one_mem' := by
          simp only [Set.mem_ofPred_eq, map_one, one_mul]; exact Filter.EventuallyEq.rfl
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, map_mul, mul_assoc] at ha hb ⊢
          exact (ae_translate (j b) ha).trans hb
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
          have := ae_translate (j a)⁻¹ ha
          simp only [mul_inv_cancel_left] at this
          exact this.symm }
    have hE1G : K₀ ⊓ K₁ ≤ G := fun γ hγ => inv hBE1 iBE1 hDE1 h1 γ hγ
    have hE2G : K₀ ⊓ K₂ ≤ G := fun γ hγ => inv hBE2 iBE2 hDE2 h2 γ hγ
    have hE3G : K₁ ⊓ K₂ ≤ G := fun γ hγ => inv hBE3 iBE3 hDE3 h3 γ hγ
    obtain ⟨g, hg, hgB⟩ := exists_not_mem hT.big₀₂
    have hgE1 : g ∉ K₀ ⊓ K₁ := fun h => hgB (Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hg).2⟩)
    have hK0 : K₀ ≤ G := twoTr_le hT.two₀ hE1G (Subgroup.mem_inf.1 hg).1 hgE1 (hE2G hg)
    obtain ⟨g', hg', hg'B⟩ := exists_not_mem hT.big₀₁
    have hg'E3 : g' ∉ K₁ ⊓ K₂ := fun h =>
      hg'B (Subgroup.mem_inf.2 ⟨hg', (Subgroup.mem_inf.1 h).2⟩)
    have hK1 : K₁ ≤ G := twoTr_le hT.two₁ hE3G (Subgroup.mem_inf.1 hg').2 hg'E3 (hE1G hg')
    have hsup : K₀ ⊔ K₁ ≤ G := sup_le hK0 hK1
    obtain ⟨c, hc⟩ := hA S μ ((K₀ ⊔ K₁).map j) hdense F hF.1 (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact hsup hγ)
    rw [cls_inner hF hvG]
    have hFc : (fun x => F x * v x) =ᵐ[μ.restrict DB] fun x => c * v x :=
      (ae_restrict_of_ae hc).mono fun x hx => by dsimp only; rw [hx]
    have hvint : IntegrableOn v DB μ := hvG.2.2.integrable (by norm_num)
    rw [integral_congr_ae hFc, integral_const_mul,
      int_eq_inv μ hU hj hBK0 i0 hD₀ hDB hvm hvK hvint, hv0, mul_zero, mul_zero]

  have hB1 : B = (K₀ ⊓ K₁) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB2 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₁) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB3 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have a1 := angle hU hj hDB hD hB1 hE1K0 hE2K0 i0 hT.two₀ hT.big₀₂ hD₀ hDE1 hDE2
  have a2 := angle hU hj hDB hD hB2 hE3K1 hE1K1 i1 hT.two₁ hT.big₀₁ hD₁ hDE3 hDE1
  have a3 := angle hU hj hDB hD hB3 hE3K2 hE2K2 i2 hT.two₂ hT.big₀₂ hD₂ hDE3 hDE2
  have le12 := le_inf (W_anti hU hj hDB hBE1 hE1K0 i0 hDE1 hD₀) (W_anti hU hj hDB hBE2 hE2K0 i0 hDE2 hD₀)
  have le13 := le_inf (W_anti hU hj hDB hBE1 hE1K1 i1 hDE1 hD₁) (W_anti hU hj hDB hBE3 hE3K1 i1 hDE3 hD₁)
  have le23 := le_inf (W_anti hU hj hDB hBE2 hE2K2 i2 hDE2 hD₂) (W_anti hU hj hDB hBE3 hE3K2 i2 hDE3 hD₂)
  have hvmem : cls j B μ DB v ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hvG (linv_mono j hE1K0 hvK),
      mem_W_of_inv hU hj hDB hBE2 iBE2 hDE2 hvG (linv_mono j hE2K0 hvK)⟩
  have hwmem : cls j B μ DB w ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₁ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hwG (linv_mono j hE1K1 hwi),
      mem_W_of_inv hU hj hDB hBE3 iBE3 hDE3 hwG (linv_mono j hE3K1 hwi)⟩
  have hmain := hH (HL j B μ DB) (W j B μ DB (K₀ ⊓ K₁)) (W j B μ DB (K₀ ⊓ K₂))
    (W j B μ DB (K₁ ⊓ K₂)) (W j B μ DB K₀) (W j B μ DB K₁) (W j B μ DB K₂)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) le12 le13 le23 a1 a2 a3 _ hvmem hker _ hwmem

  have hBw : avg j B K₀ w = v := by
    rw [← u_trans μ hU hj hBK0 i0 hBE1 hE1K0 hwB,
      u_id μ hU hj hBE1 iBE1 (linv_mono j hE1K1 hwi)]
  have hin : ⟪cls j B μ DB v, cls j B μ DB w⟫_ℝ =
      (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_inner hvG hwG, u_int_eq μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x * w x) (hvm.mul hwm)
      (linv_mul j (linv_mono j hBK0 hvK) hwB) (integrableOn_mul hvG.2.2 hwG.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hvK, hBw, sq]
  have hnv : ‖cls j B μ DB v‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_norm_sq hvG, int_eq_inv μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x ^ 2) (hvm.pow_const 2)
      (linv_sq j hvK) hv2B]
  have hnw : ‖cls j B μ DB w‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₁, w x ^ 2 ∂μ := by
    rw [cls_norm_sq hwG, int_eq_inv μ hU hj hBK1 i1 hD₁ hDB (u := fun x => w x ^ 2) (hwm.pow_const 2)
      (linv_sq j hwi) hw2B, hidx]
  refine ⟨hv2, hv0, ?_⟩
  set n : ℝ := ((B.subgroupOf K₀).index : ℝ)
  have hn0 : 0 < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero i0)
  set P := ∫ x in D₀, v x ^ 2 ∂μ
  set Q := ∫ x in D₁, w x ^ 2 ∂μ
  set a := ‖cls j B μ DB v‖
  set b := ‖cls j B μ DB w‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rw [hin] at hmain
  have h1 : a ^ 2 ≤ 2 / 5 * (a * b) := by rw [hnv]; exact (le_abs_self _).trans hmain
  have h2 : a ^ 2 ≤ (2 / 5) ^ 2 * b ^ 2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · have : a ≤ 2 / 5 * b := by nlinarith
      nlinarith
    · rw [← ha']; nlinarith [sq_nonneg b]
  rw [hnv, hnw] at h2
  have : n * P ≤ n * ((2 / 5) ^ 2 * Q) := by linarith
  exact le_of_mul_le_mul_left this hn0

end PositivityTheory.KB.SpectralGap

end
end
