import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutPieces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeCriterion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepHilb
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlockAdjoinPrime
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAssoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialPieceRank
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericPieceRank
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealSurj
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section MixedDiffLinearProof

variable {K : Type*}

theorem diffStep_add' (b : K → ℤ) (f g : (K → ℤ) → ℤ) :
    diffStep b (f + g) = diffStep b f + diffStep b g := by
  funext m; simp only [diffStep, Pi.add_apply]; ring

theorem diffStep_smul' (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by
  funext m; simp only [diffStep, Pi.smul_apply, smul_eq_mul]; ring

theorem diffStep_shiftFn' (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by
  funext m; simp only [diffStep, shiftFn, sub_right_comm]

theorem diffStep_comm' (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by
  funext m; simp only [diffStep, sub_right_comm m b b']; ring

theorem foldr_diffStep_props (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, diffStep_add']
    · rw [h2, diffStep_smul']
    · rw [h3, diffStep_shiftFn']
    · rw [h4, diffStep_comm']

theorem MixedDiffLinear.proof : MixedDiffLinear.Statement := by
  intro K n bs f g c s b
  obtain ⟨h1, h2, h3, h4⟩ := foldr_diffStep_props (List.ofFn bs) f g c s b
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]

end MixedDiffLinearProof

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type}

theorem tendsto_sub_const_atTop (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id

theorem diffStep_eventuallyEq (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']

theorem foldr_diffStep_eventuallyEq (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih

theorem DegLTClosure.proof (h1 : MixedDiffLinear.Statement) : DegLTClosure.Statement := by
  intro K n f g c s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf hg bs
    filter_upwards [hf bs, hg bs] with m hm hm'
    rw [(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]
  · intro hf bs
    filter_upwards [hf bs] with m hm
    rw [(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]
  · intro hf bs
    have h' := (tendsto_sub_const_atTop s).eventually (hf bs)
    filter_upwards [h'] with m hm
    rw [(h1 K n bs f g c s 0).2.2.1]
    exact hm
  · intro hf bs
    have hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0 :=
      hf (fun i => bs i.succ)
    have hz' := (tendsto_sub_const_atTop (bs 0)).eventually hz
    filter_upwards [hz, hz'] with m hm hm'
    have e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f) := by
      unfold mixedDiff
      rw [List.ofFn_succ, List.foldr_cons]
    rw [e]
    simp only [diffStep, hm, hm', sub_zero]
  · intro hfg hf bs
    have e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g :=
      foldr_diffStep_eventuallyEq (List.ofFn bs) hfg
    filter_upwards [e, hf bs] with m hm hm'
    rw [← hm, hm']

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DiffStepExpansion

variable {K : Type}

lemma listSum_apply {α : Type} (l : List α) (F : α → (K → ℤ) → ℤ) (m : K → ℤ) :
    (l.map F).sum m = (l.map fun t => F t m).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

def expand [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum

lemma expand_apply [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ)
    (m : K → ℤ) :
    expand l f m = (l.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)).sum := by
  unfold expand
  rw [listSum_apply]
  rfl

def expandable (K : Type) [DecidableEq K] : AddSubgroup (K → ℤ) where
  carrier := {b | ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f, diffStep b f = expand l f}
  zero_mem' := ⟨[], fun f => by funext m; simp [diffStep, expand]⟩
  add_mem' := by
    rintro a c ⟨la, ha⟩ ⟨lc, hc⟩
    refine ⟨la ++ lc.map (fun t => ((t.1.1, t.1.2 + a), t.2)), fun f => ?_⟩
    funext m
    have h1 := congrFun (ha f) m
    have h2 := congrFun (hc f) (m - a)
    simp only [diffStep] at h1 h2 ⊢
    rw [expand_apply] at h1 h2
    rw [expand_apply, List.map_append, List.sum_append, List.map_map, ← h1]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 + a), t.2))).sum =
        (lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - a - t.1.2)).sum := by
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      congr 2
      abel
    rw [h3, ← h2]
    have : m - (a + c) = m - a - c := by abel
    rw [this]
    ring
  neg_mem' := by
    rintro c ⟨lc, hc⟩
    refine ⟨lc.map (fun t => ((t.1.1, t.1.2 - c), -t.2)), fun f => ?_⟩
    funext m
    have h2 := congrFun (hc f) (m + c)
    simp only [diffStep] at h2 ⊢
    rw [expand_apply] at h2
    rw [expand_apply, List.map_map]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 - c), -t.2))).sum =
        -(lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m + c - t.1.2)).sum := by
      clear hc h2
      induction lc with
      | nil => simp
      | cons t l ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
        have e : m - (t.1.2 - c) = m + c - t.1.2 := by abel
        rw [ih, e]
        ring
    rw [h3, ← h2]
    have e1 : m + c - c = m := by abel
    have e2 : m - -c = m + c := by abel
    rw [e1, e2]
    ring

lemma single_mem [DecidableEq K] (k : K) : (Pi.single k 1 : K → ℤ) ∈ expandable K :=
  ⟨[((k, 0), 1)], fun f => by funext m; simp [expand, shiftFn]⟩

theorem proof : DiffStepExpansion.Statement := by
  intro K _ _ b
  have hb : b ∈ expandable K := by
    rw [← Finset.univ_sum_single b]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have : (Pi.single k (b k) : K → ℤ) = b k • (Pi.single k 1 : K → ℤ) := by
      ext j
      by_cases h : j = k <;> simp [h]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (single_mem k) _
  obtain ⟨l, hl⟩ := hb
  exact ⟨l, fun f => hl f⟩

end DiffStepExpansion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem DegLTOfUnitSteps.degLT_diffStep (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement)
    (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ)
    (hf : ∀ k, DegLT (diffStep (Pi.single k 1) f) n) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  obtain ⟨l, hl⟩ := h1 K b
  rw [hl f]
  clear hl
  induction l with
  | nil =>
    intro cs
    refine Filter.Eventually.of_forall fun m => ?_
    have h0 := (h2 K n cs f f 0 0 0).2.1
    rw [zero_smul, zero_smul] at h0
    simp only [List.map_nil, List.sum_nil]
    rw [h0]
    rfl
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs : DegLT (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (diffStep (Pi.single t.1.1 1) f) f 0 t.1.2).2.2.1 (hf t.1.1)
    have hc : DegLT (t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) f t.2 0).2.1 hs
    exact (h3 K n _ (List.map (fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) l).sum
      0 0).1 hc ih

theorem DegLTOfUnitSteps.proof (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement) :
    DegLTOfUnitSteps.Statement := by
  intro K _ _ n f hf bs
  have key : mixedDiff bs f = mixedDiff (Fin.tail bs) (diffStep (bs 0) f) := by
    rw [(h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.1,
      ← (h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.2]
    congr 1
    exact (Fin.cons_self_tail bs).symm
  rw [key]
  exact DegLTOfUnitSteps.degLT_diffStep h1 h2 h3 K n f hf (bs 0) _

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace DegLTEventuallyConst

theorem eq_of_unitSteps_eq_zero {K : Type} [Fintype K] [DecidableEq K] (g : (K → ℤ) → ℤ)
    (N : K → ℤ) (h : ∀ m, N ≤ m → ∀ k, g m - g (m - Pi.single k 1) = 0) :
    ∀ d : ℕ, ∀ m, N ≤ m → ∑ k, (m k - N k).toNat = d → g m = g N := by
  intro d
  induction d with
  | zero =>
    intro m hm hs
    have hmN : m = N := by
      funext k
      have hk : (m k - N k).toNat = 0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have hle : N k ≤ m k := hm k
      omega
    rw [hmN]
  | succ d ih =>
    intro m hm hs
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (m k - N k).toNat ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at hs
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : K → ℤ, m' = m - Pi.single k (1 : ℤ) := ⟨_, rfl⟩
    have hm'k : m' k = m k - 1 := by simp [hm']
    have hm'j : ∀ j, j ≠ k → m' j = m j := by
      intro j hj
      simp [hm', hj]
    have hkk : N k + 1 ≤ m k := by omega
    have hNm' : N ≤ m' := by
      intro j
      show N j ≤ m' j
      by_cases hj : j = k
      · rw [hj, hm'k]
        omega
      · rw [hm'j j hj]
        exact hm j
    have hs' : ∑ j, (m' j - N j).toNat = d := by
      have e1 := Finset.add_sum_erase Finset.univ (fun j => (m j - N j).toNat) (Finset.mem_univ k)
      have e2 := Finset.add_sum_erase Finset.univ
        (fun j => (m' j - N j).toNat) (Finset.mem_univ k)
      have e3 : ∑ j ∈ Finset.univ.erase k, (m' j - N j).toNat =
          ∑ j ∈ Finset.univ.erase k, (m j - N j).toNat :=
        Finset.sum_congr rfl fun j hj => by rw [hm'j j (Finset.ne_of_mem_erase hj)]
      simp only [hm'k] at e2
      omega
    have step : g m - g m' = 0 := by rw [hm']; exact h m hm k
    rw [← ih _ hNm' hs']
    omega

theorem proof (h1 : MixedDiffLinear.Statement) : DegLTEventuallyConst.Statement := by
  intro K _ _ n f hf bs
  have hev : ∀ k : K, ∀ᶠ m in Filter.atTop,
      mixedDiff bs f m - mixedDiff bs f (m - Pi.single k 1) = 0 := by
    intro k
    have hk := hf (Matrix.vecCons (Pi.single k 1) bs)
    rw [(h1 K n bs f 0 0 0 (Pi.single k 1)).2.2.2.2] at hk
    exact hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨mixedDiff bs f N, Filter.eventually_atTop.mpr ⟨N, fun m hm =>
    eq_of_unitSteps_eq_zero (mixedDiff bs f) N (fun m hm => hN m hm) _ m hm rfl⟩⟩

end DegLTEventuallyConst

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem AssociatedMultiHomogPrime.proof (h1 : MultiHomogPrimeCriterion.Statement.{u})
    (h2 : ColonMultiHomog.Statement.{u}) : AssociatedMultiHomogPrime.Statement.{u} := by
  intro F _ K _ _ ι _ J hJ hJtop
  classical

  let A : Set (Ideal (MRing ι F)) :=
    {Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}
  have hne : A.Nonempty := by
    refine ⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩
    · exact isWeightedHomogeneous_one F (blockWeight ι)
    · intro h
      exact hJtop ((Ideal.eq_top_iff_one J).2 h)
  have hnoeth : IsNoetherianRing (MRing ι F) := inferInstance
  obtain ⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne
  refine ⟨f, s, hf, hfJ, ?_⟩
  apply h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)
  · intro htop
    apply hfJ
    have h1mem : (1 : MRing ι F) ∈ J.colon {f} := by rw [htop]; exact Submodule.mem_top
    simpa using (Submodule.mem_colon_singleton.1 h1mem)
  · intro a b sa sb _ hb hab
    by_cases hbQ : b ∈ J.colon {f}
    · exact Or.inr hbQ
    left
    have hbf : b * f ∉ J := by
      intro h
      apply hbQ
      exact Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)
    have hform : IsMultiHomog (b * f) (sb + s) := hb.mul hf
    have hle : J.colon {f} ≤ J.colon {b * f} := by
      intro x hx
      have hx' : x * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx
      refine Submodule.mem_colon_singleton.2 ?_
      have : b * (x * f) ∈ J := J.mul_mem_left b hx'
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have heq : J.colon {f} = J.colon {b * f} := by
      by_contra hne'
      exact hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')
    rw [heq]
    refine Submodule.mem_colon_singleton.2 ?_
    have hab' : a * b * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab
    simpa [smul_eq_mul, mul_assoc] using hab'

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem FiltrationStepLength.proof : FiltrationStepLength.Statement := by
  intro R _ K ι L W _ f
  let g₁ : (MRing ι R ⧸ L.colon {f}) →ₗ[MRing ι R] MRing ι R ⧸ L :=
    Submodule.mapQ _ _ (LinearMap.mulRight (MRing ι R) f) (fun x hx => by
      have := Submodule.mem_colon_singleton.mp hx
      simpa [smul_eq_mul] using this)
  let g₂ : (MRing ι R ⧸ L) →ₗ[MRing ι R] MRing ι R ⧸ (L ⊔ Ideal.span {f}) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => Submodule.mem_sup_left hx)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | _ c => ?_
    rw [LinearMap.mem_ker] at hy
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hy)
  have hsurj : Function.Surjective g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply]
      rw [Submodule.Quotient.eq]
      have e : c * f - (l + c * f) = -l := by ring
      rw [e]
      exact L.neg_mem hl
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply] at hx
      rw [Submodule.Quotient.eq] at hx
      have e : a = -(c * f - a) + c * f := by ring
      rw [e]
      exact Submodule.add_mem_sup (L.neg_mem hx) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have key := Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)
  unfold multAt
  rw [add_comm]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem decompose_blockWeight {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (r : MRing ι R) (b : K → ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) r b : MRing ι R) =
      weightedHomogeneousComponent (blockWeight ι) b r :=
  weightedDecomposition.decompose'_apply R (blockWeight ι) r b

theorem isMultiHomogIdeal_iff_isHomogeneous {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
  constructor
  · intro h b r hr
    rw [decompose_blockWeight]
    exact h r hr b
  · intro h r hr b
    rw [← decompose_blockWeight]
    exact h b hr

theorem isMultiHomogIdeal_sup_span {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} {J : Ideal (MRing ι R)} {f : MRing ι R} {s : K → ℕ}
    (hJ : IsMultiHomogIdeal J) (hf : IsMultiHomog f s) :
    IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ ?_)
  rintro x rfl
  exact ⟨s, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩

theorem multAt_top {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (W : Ideal (MRing ι R)) [W.IsPrime] : multAt (⊤ : Ideal (MRing ι R)) W = 0 := by
  unfold multAt
  have : Subsingleton (MRing ι R ⧸ (⊤ : Ideal (MRing ι R))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

theorem PrimeFiltration.proof (h1 : AssociatedMultiHomogPrime.Statement.{u})
    (h2 : FiltrationStepHilb.Statement.{u}) (h3 : FiltrationStepLength.Statement.{u})
    (h4 : ColonMultiHomog.Statement.{u}) : PrimeFiltration.Statement.{u} := by
  intro F _ K _ _ ι _ J
  have : WellFoundedGT (Ideal (MRing ι F)) := inferInstance
  induction J using WellFoundedGT.induction
  rename_i J ih
  intro hJ
  by_cases hT : J = ⊤
  · subst hT
    refine ⟨[], by simp, fun m => by simp [hilbFn_top], fun W _ => by simp [multAt_top]⟩
  obtain ⟨f, s, hf, hfJ, hQ⟩ := h1 F K ι J hJ hT
  have hQh : IsMultiHomogIdeal (J.colon {f}) := h4 F K ι J f s hJ hf
  have hJQ : J ≤ J.colon {f} := fun x hx =>
    Submodule.mem_colon_singleton.mpr (J.mul_mem_right f hx)
  have hlt : J < J ⊔ Ideal.span {f} :=
    SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, f, Ideal.mem_sup_right (Ideal.mem_span_singleton_self f), hfJ⟩
  obtain ⟨l', hl'1, hl'2, hl'3⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨(J.colon {f}, s) :: l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hQ, hQh, hJQ⟩
    · obtain ⟨a, b, c⟩ := hl'1 p hp
      exact ⟨a, b, le_sup_left.trans c⟩
  · intro m
    rw [h2 F K ι J f s hJ hf m, hl'2 m, List.map_cons, List.sum_cons, add_comm]
  · intro W _
    rw [h3 F K ι J W f, hl'3 W, List.map_cons, List.sum_cons, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace IntNumOfFiltration

theorem eventually_mixedDiff_sum (h1 : MixedDiffLinear.Statement)
    (h3 : EventualValueFacts.Statement) {K : Type} {n : ℕ} (bs : Fin n → K → ℤ)
    {α : Type*} (h : α → (K → ℤ) → ℤ) (s : α → K → ℤ) :
    ∀ l : List α, (∀ p ∈ l, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (h p) m = c) →
      ∀ᶠ m in Filter.atTop,
        mixedDiff bs (fun m => (l.map fun p => h p (m - s p)).sum) m =
          (l.map fun p => eventualValue (mixedDiff bs (h p))).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    have h0 : (fun m : K → ℤ => (([] : List α).map fun p => h p (m - s p)).sum) = 0 := by
      funext m
      simp
    have hz : mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
      have := (h1 K n bs 0 0 0 0 0).2.1
      simpa using this
    refine Filter.Eventually.of_forall fun m => ?_
    rw [h0, hz]
    simp
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc⟩ := hl p List.mem_cons_self
    have hsplit : (fun m : K → ℤ => ((p :: l).map fun q => h q (m - s q)).sum) =
        shiftFn (s p) (h p) + fun m => (l.map fun q => h q (m - s q)).sum := by
      funext m
      simp [shiftFn]
    have hev := (h3 K _ c (s p)).1 hc
    have hsh := (h3 K _ c (s p)).2 hc
    filter_upwards [ih fun q hq => hl q (List.mem_cons_of_mem p hq), hsh] with m hm hm'
    rw [hsplit, (h1 K n bs (shiftFn (s p) (h p)) (fun m => (l.map fun q => h q (m - s q)).sum)
      0 (s p) 0).1, (h1 K n bs (h p) 0 0 (s p) 0).2.2.1]
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    rw [hm', hm, hev]

theorem proof (h1 : MixedDiffLinear.Statement) (h2 : DegLTEventuallyConst.Statement)
    (h3 : EventualValueFacts.Statement) : IntNumOfFiltration.Statement := by
  intro F _ K _ _ ι _ n J l hdeg hJ bs
  have hfun : hilbFn J = fun m => (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum :=
    funext hJ
  have hev := eventually_mixedDiff_sum h1 h3 bs
    (fun p : Ideal (MRing ι F) × (K → ℕ) => hilbFn p.1) (fun p k => (p.2 k : ℤ)) l
    (fun p hp => h2 K n (hilbFn p.1) (hdeg p hp) bs)
  unfold intNum
  rw [hfun]
  exact (h3 K _ _ 0).1 hev

end IntNumOfFiltration

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finite_setOf_weight_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  refine ((Set.Finite.pi' fun v : (Σ k, ι k) => Set.finite_le_nat (m v.1)).preimage
    DFunLike.coe_injective.injOn).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro v
  rw [← hd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun u => (d u • blockWeight ι u) v.1) (fun _ _ => Nat.zero_le _) hv)
    simp [blockWeight]
  · simp [Finsupp.notMem_support_iff.mp hv]

theorem mem_of_C_pow_mul_mem {O : Type u} [CommRing O] {K : Type} {ι : K → Type}
    {P : Ideal (MRing ι O)} {ϖ : O} (hP : ∀ x, C ϖ * x ∈ P → x ∈ P) :
    ∀ (n : ℕ) (y : MRing ι O), C (ϖ ^ n) * y ∈ P → y ∈ P := by
  intro n
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    apply hP
    apply ih
    rwa [pow_succ, map_mul, mul_assoc] at hy

theorem GradedPieceFree.proof : GradedPieceFree.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP m
  have hfg : (weightedHomogeneousSubmodule O (blockWeight ι) m).FG := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
    have := (finite_setOf_weight_blockWeight_eq ι m).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport O _)
  have hfin : Module.Finite O (gradedPieceR P m) := Module.Finite.iff_fg.mpr (hfg.map _)
  have htf : Module.IsTorsionFree O (gradedPieceR P m) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x hcx => ?_
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x : MRing ι O ⧸ P)
    have h1 : ((↑w * ϖ ^ n) • (x : MRing ι O ⧸ P)) = 0 := congrArg Subtype.val hcx
    rw [← hy, ← Ideal.Quotient.mkₐ_eq_mk O, ← map_smul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul] at h1
    have h2 : C (ϖ ^ n) * y ∈ P := by
      have := P.mul_mem_left (C (↑w⁻¹ : O)) h1
      rwa [← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul] at this
    apply Subtype.ext
    rw [← hy, Submodule.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_C_pow_mul_mem hP n y h2
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ConservationOfNumber.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u})
    (h6 : SpecialDimBound.Statement.{u}) : ConservationOfNumber.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a

  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiProj.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom)
    (h6 O ϖ hϖ K ι P d hP) a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IntNumVanish.proof (h1 : HilbDegBound.Statement.{u})
    (h2 : HilbFnVanishBlock.Statement.{u}) (h3 : DegLTClosure.Statement)
    (h4 : EventualValueFacts.Statement) : IntNumVanish.Statement.{u} := by
  intro F _ K _ _ ι _ n Q hQ hQh hcase bs

  suffices hdeg : DegLT (hilbFn Q) n by
    exact (h4 K (mixedDiff bs (hilbFn Q)) 0 0).1 (hdeg bs)
  rcases hcase with hirr | hdim
  ·
    have hblock : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ Q := by
      by_contra hne
      exact hirr fun k => by_contra fun h => hne ⟨k, fun i => by_contra fun hi => h ⟨i, hi⟩⟩
    obtain ⟨k, hk⟩ := hblock
    have hzero : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
      exact (h2 F K ι Q k hk m (hm k)).symm
    exact (h3 K n 0 (hilbFn Q) 0 0).2.2.2.2 hzero (degLT_zero n)
  · exact h1 F K ι n Q hQ hQh hdim

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MixedDiffLinear.full : MixedDiffLinear.Statement := MixedDiffLinear.proof

theorem DegLTClosure.full : DegLTClosure.Statement := DegLTClosure.proof MixedDiffLinear.full

theorem DiffStepExpansion.full : DiffStepExpansion.Statement := DiffStepExpansion.proof

theorem DegLTOfUnitSteps.full : DegLTOfUnitSteps.Statement :=
  DegLTOfUnitSteps.proof DiffStepExpansion.full MixedDiffLinear.full DegLTClosure.full

theorem DegLTEventuallyConst.full : DegLTEventuallyConst.Statement :=
  DegLTEventuallyConst.proof MixedDiffLinear.full

theorem EventualValueFacts.full : EventualValueFacts.Statement := EventualValueFacts.proof

theorem HilbFnVanishBlock.full : HilbFnVanishBlock.Statement.{u} := HilbFnVanishBlock.proof

theorem GradedPieceQuot.full : GradedPieceQuot.Statement.{u} := GradedPieceQuot.proof

theorem CutPieces.full : CutPieces.Statement.{u} := CutPieces.proof

theorem HilbFnCut.full : HilbFnCut.Statement.{u} := HilbFnCut.proof GradedPieceQuot.full CutPieces.full

theorem MultiHomogPrimeCriterion.full : MultiHomogPrimeCriterion.Statement.{u} :=
  MultiHomogPrimeCriterion.proof

theorem ColonMultiHomog.full : ColonMultiHomog.Statement.{u} := ColonMultiHomog.proof

theorem AssociatedMultiHomogPrime.full : AssociatedMultiHomogPrime.Statement.{u} :=
  AssociatedMultiHomogPrime.proof MultiHomogPrimeCriterion.full ColonMultiHomog.full

theorem FiltrationStepHilb.full : FiltrationStepHilb.Statement.{u} := FiltrationStepHilb.proof

theorem FiltrationStepLength.full : FiltrationStepLength.Statement.{u} := FiltrationStepLength.proof

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof AssociatedMultiHomogPrime.full FiltrationStepHilb.full
    FiltrationStepLength.full ColonMultiHomog.full

theorem MultAtPrimeAtMinimal.full : MultAtPrimeAtMinimal.Statement.{u} := MultAtPrimeAtMinimal.proof

theorem DimStrictDrop.full : DimStrictDrop.Statement.{u} := DimStrictDrop.proof

theorem BlockAdjoinPrime.full : BlockAdjoinPrime.Statement.{u} := BlockAdjoinPrime.proof

theorem RelevantDimGe.full : RelevantDimGe.Statement.{u} := RelevantDimGe.proof BlockAdjoinPrime.full

theorem HilbDegBound.full : HilbDegBound.Statement.{u} :=
  HilbDegBound.proof HilbFnVanishBlock.full HilbFnCut.full PrimeFiltration.full DimStrictDrop.full
    RelevantDimGe.full DegLTClosure.full DegLTOfUnitSteps.full

theorem TopDimMinimal.full : TopDimMinimal.Statement.{u} := TopDimMinimal.proof DimStrictDrop.full

theorem IntNumOfFiltration.full : IntNumOfFiltration.Statement.{u} :=
  IntNumOfFiltration.proof MixedDiffLinear.full DegLTEventuallyConst.full EventualValueFacts.full

theorem GradedPieceFree.full : GradedPieceFree.Statement.{u} := GradedPieceFree.proof

theorem SpecialPieceRank.full : SpecialPieceRank.Statement.{u} :=
  SpecialPieceRank.proof GradedPieceFree.full

theorem GenericPieceRank.full : GenericPieceRank.Statement.{u} := GenericPieceRank.proof

theorem SpecialIdealMultiHomog.full : SpecialIdealMultiHomog.Statement.{u} :=
  SpecialIdealMultiHomog.proof

theorem SpecialIdealCorresp.full : SpecialIdealCorresp.Statement.{u} := SpecialIdealCorresp.proof

theorem SpecialIdealSurj.full : SpecialIdealSurj.Statement.{u} := SpecialIdealSurj.proof

theorem SpecialMultAt.full : SpecialMultAt.Statement.{u} := SpecialMultAt.proof

theorem SpecialCycleEval.full : SpecialCycleEval.Statement.{u} :=
  SpecialCycleEval.proof SpecialIdealCorresp.full SpecialIdealSurj.full SpecialMultAt.full

theorem SpecialDimBound.full : SpecialDimBound.Statement.{u} := SpecialDimBound.proof

theorem IntNumVanish.full : IntNumVanish.Statement.{u} :=
  IntNumVanish.proof HilbDegBound.full HilbFnVanishBlock.full DegLTClosure.full EventualValueFacts.full

theorem IntNumAssoc.full : IntNumAssoc.Statement.{u} :=
  IntNumAssoc.proof PrimeFiltration.full IntNumOfFiltration.full MultAtPrimeAtMinimal.full
    IntNumVanish.full TopDimMinimal.full HilbDegBound.full

theorem CutByForm.full : CutByForm.Statement.{u} :=
  CutByForm.proof IntNumAssoc.full HilbFnCut.full MixedDiffLinear.full

theorem ConservationOfNumber.full : ConservationOfNumber.Statement.{u} :=
  ConservationOfNumber.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full SpecialDimBound.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end
