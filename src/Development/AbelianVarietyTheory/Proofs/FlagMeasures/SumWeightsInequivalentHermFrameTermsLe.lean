import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormExistsConjNearReference
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos

section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_star_stable_ideal_absorbing_minors : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔠 : Ideal (𝓞 K), (Ideal.absNorm 𝔠 : ℝ) ≤ (N.Db * N.NT) ^ 2 ∧ 1 ≤ N.Db ∧ 1 ≤ N.Del ∧ ∀ Q : Prop, (𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → Q) → Q := by
  first | exact @GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | exact GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal | (intros; apply GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal <;> assumption)
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.NearCount

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩
    simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)

theorem smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)

theorem exists_gens [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)

end GlobalTheory.DegCnt.NearCount

theorem GlobalTheory.DegCnt.NearCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N m hm
  have hn : m * m ≠ ⊥ := mul_ne_zero hm hm
  obtain ⟨v, hv, hP⟩ := GlobalTheory.DegCnt.NearCount.exists_gens N (m * m) hn
  have h1 := GlobalTheory.DegCnt.NearCount.count_between N.P0 (m * m) hn _ v hv hP
  have h2 : ({P : Submodule (𝓞 K) V | m • N.P0 ≤ P ∧ m • P ≤ N.P0}).encard ≤
      {L : Submodule (𝓞 K) V | (m * m) • N.P0 ≤ L ∧ L ≤ N.P0}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun P => m • P) ?_
      (GlobalTheory.DegCnt.NearCount.smul_injective m hm).injOn
    rintro P ⟨h, h'⟩
    exact ⟨by rw [Submodule.mul_smul]; exact Submodule.smul_mono le_rfl h, h'⟩
  refine (ENat.toENNReal_le.2 (h2.trans h1)).trans (le_of_eq ?_)
  rw [map_mul, ← sq, ← pow_mul, ← sq]
  simp
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_lattices_near_reference_lattice_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  atlas_forward_decl GlobalTheory.DegCnt.NearCount.main
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem count_index_fg {K Q : Type} [Field K] [NumberField K] [AddCommGroup Q] [Module K Q]
    [Module (𝓞 K) Q] [IsScalarTower (𝓞 K) K Q] [FiniteDimensional K Q] (M : Submodule (𝓞 K) Q) (hM : M.FG)
    (S : Submodule K Q) (hS : M ≤ S.restrictScalars (𝓞 K)) (k : ℕ) (hk : Module.finrank K S ≤ k)
    (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) Q := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K Q
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K M x hx
  refine ⟨h1, ?_⟩
  have hr : Module.finrank (𝓞 K) M ≤ k := by
    refine le_trans ?_ hk
    apply Module.finrank_le_of_rank_le
    have h3 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) S := Submodule.rank_mono hS
    have h5 : Module.rank K S = Module.rank (𝓞 K) S := IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl
    rw [Module.finrank_eq_rank, h5]
    exact h3
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x hn hx
  have h3 : (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (𝓞 K) M := by exact_mod_cast h2
  have hr' : (Module.finrank (𝓞 K) M : ℝ) ≤ k := by exact_mod_cast hr
  calc _ ≤ _ := h3
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) M :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ ((Module.finrank (𝓞 K) M : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem count_index_latMod {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (W I : Submodule K V)
    (La : Submodule (𝓞 K) V) (h : IsLatMod La (W ⊔ I) I) (x : ℕ) (hx : 1 ≤ x) :
    ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ ((Module.finrank K W : ℝ) + cf K)) := by
  obtain ⟨⟨N, hN, hLa⟩, hsp⟩ := h
  let q : V →ₗ[𝓞 K] (V ⧸ I) := I.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker q = rs (𝓞 K) I := by
    ext v; simp [q]
  have hM : (La.map q).FG := by
    have : (rs (𝓞 K) I).map q = ⊥ := by
      rw [← hker]; exact LinearMap.le_ker_iff_map.1 le_rfl
    rw [hLa, Submodule.map_sup, this, sup_bot_eq]
    exact hN.map q
  have hS : La.map q ≤ (W.map I.mkQ).restrictScalars (𝓞 K) := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ W ⊔ I := hsp ▸ Submodule.subset_span hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨w, hw, ?_⟩
    have : I.mkQ u = 0 := by simpa using hu
    change I.mkQ w = I.mkQ (w + u)
    rw [map_add, this, add_zero]
  obtain ⟨h1, h2⟩ := count_index_fg (La.map q) hM (W.map I.mkQ) hS _ (Submodule.finrank_map_le _ _) x hx
  have hle : {Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}.encard ≤
      {N : Submodule (𝓞 K) (La.map q) | N.toAddSubgroup.index = x}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun Th => (Th.map q).comap (La.map q).subtype) ?_ ?_
    · rintro Th ⟨hI, hL, hi⟩
      have e : (Th.map q).comap q = Th := Submodule.comap_map_eq_self (hker ▸ hI)
      have e2 : idx La ((Th.map q).comap q) = idx (La.map q) (Th.map q) :=
        AddSubgroup.relIndex_comap (Th.map q).toAddSubgroup q.toAddMonoidHom La.toAddSubgroup
      rw [e, hi] at e2
      exact e2.symm
    · rintro Th ⟨hI, hL, -⟩ Th' ⟨hI', hL', -⟩ he
      have he2 : Th.map q = Th'.map q := by
        have := congrArg (Submodule.map (La.map q).subtype) he
        simp only [Submodule.map_comap_subtype] at this
        rwa [inf_eq_right.2 (Submodule.map_mono hL), inf_eq_right.2 (Submodule.map_mono hL')] at this
      rw [← Submodule.comap_map_eq_self (f := q) (p := Th) (hker ▸ hI), he2,
        Submodule.comap_map_eq_self (hker ▸ hI')]
  refine le_trans (ENat.toENNReal_le.2 hle) ?_
  rw [← h1.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h2

theorem count_sublattices_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N La i hi h
  have hw := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).2.2.2.2.2.2.1
  rw [hw] at h
  exact count_index_latMod N.Wt _ La h i hi

end GlobalTheory.DegCnt
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_sublattices_definiteQuotient_normalForm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  atlas_forward_decl GlobalTheory.DegCnt.count_sublattices_definite
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Glue

open TensorProduct

theorem finrank_baseChange_field (R M F : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] [Field F] [Algebra R F] :
    Module.finrank F (F ⊗[R] M) = Module.finrank R M := by
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := F) ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

theorem exists_gens (R M : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ t : Fin (Module.finrank R M) → M, ∀ N : Submodule R M, (∀ i, t i ∈ N) → I • (⊤ : Submodule R M) ≤ N →
      N = ⊤ := by
  have : Finite (MaximalSpectrum (R ⧸ I)) := inferInstance
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] M) (Module.finrank R M) (by
    intro P
    have := P.isMaximal
    let _ := Ideal.Quotient.field P.asIdeal
    rw [(AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) M).finrank_eq]
    exact finrank_baseChange_field R M _)
  have hs : Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) :=
    TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective
  choose t ht using fun i => hs (b i)
  refine ⟨t, fun N hN hI => eq_top_iff.2 fun m _ => ?_⟩
  choose a ha using fun i => Ideal.Quotient.mk_surjective (b.repr (TensorProduct.mk R (R ⧸ I) M 1 m) i)
  have h0 : TensorProduct.mk R (R ⧸ I) M 1 (m - ∑ i, a i • t i) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (TensorProduct.mk R (R ⧸ I) M 1 m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ht, ← ha, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have h1 : m - ∑ i, a i • t i ∈ I • (⊤ : Submodule R M) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← this]
    simp
  have h2 := N.add_mem (hI h1) (N.sum_mem (t := Finset.univ) fun i _ => N.smul_mem (a i) (hN i))
  simpa using h2

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem finrank_le {D : Submodule (𝓞 K) V} {W : Submodule K V} (h : D ≤ rs (𝓞 K) W) :
    Module.finrank (𝓞 K) D ≤ Module.finrank K W := by
  let f : D →ₗ[𝓞 K] W := { toFun := fun d => ⟨d, h d.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b e => Subtype.ext (congrArg (fun z : W => (z : V)) e)
  have h1 := LinearMap.rank_le_of_injective f hf
  rw [← IsLocalization.rank_eq (N := W) K (nonZeroDivisors (𝓞 K)) le_rfl] at h1
  exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K W)

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (S : Submodule K V) :
    Submodule.span K ((L ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun x hx => hx.2
  · intro v hv
    obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hL v
    have hc := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) s.2
    rw [← Submodule.smul_mem_iff _ hc]
    refine Submodule.subset_span ⟨?_, S.smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs

omit [StarRing K] [FiniteDimensional K V] in
theorem flat_of_submodule (D : Submodule (𝓞 K) V) : Module.Flat (𝓞 K) D := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro q ⟨a, ha⟩
  have h1 : (algebraMap (𝓞 K) K a) • (q : V) = 0 := by
    rw [algebraMap_smul]; exact congrArg Subtype.val ha
  have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
  rw [Submodule.mem_bot]
  exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h3)

section Proj

variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)

omit [NumberField K] [FiniteDimensional K V] in
include hU in
theorem integral {y x : V} (hy : y ∈ L) (hx : x ∈ L) : H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← hU.2, mem_dual_iff] at hy
  exact hy.2 x hx

omit [FiniteDimensional K V] in
include hU hp hq in

theorem proj_mem_dual {v : V} (hv : v ∈ L) : p v ∈ dual H (L ⊓ rs (𝓞 K) U) := by
  rw [mem_dual_iff, span_inf ((isLatMod_top_bot_iff L).1 hU.1)]
  refine ⟨hp v, fun a ha => ?_⟩
  have h0 := (mem_perp_iff H U _).1 (hq v) a ha.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
  rw [← h0]
  exact integral H hU hv ha.1

include hc hU hp hq in

theorem mem_dual_iff_proj (d : V) : d ∈ dual H (L ⊓ rs (𝓞 K) (perp H U)) ↔ ∃ v ∈ L, v - p v = d := by
  have hsp := span_inf ((isLatMod_top_bot_iff L).1 hU.1) (perp H U)
  have h0 : ∀ v, ∀ b ∈ perp H U, H.B b (p v) = 0 := fun v b hb => (mem_perp_iff H U _).1 hb _ (hp v)
  rw [mem_dual_iff, hsp]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H U)), IsIntegral ℤ (H.B x d) := by
      intro x
      rw [← GlobalTheory.UnimodQuot.mem_one_iff, ← H.herm]
      exact GlobalTheory.UnimodQuot.star_mem_one (hyM x x.2)
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H U)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x d, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) d = H.B a d + H.B b d
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) d = algebraMap (𝓞 K) K a * H.B b d
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨v, hv, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU (perp H U) φ
    refine ⟨v, hv, sub_eq_zero.1 ?_⟩
    have h1 : v - p v - d ∈ U := by
      apply GlobalTheory.UnimodQuot.mem_of_perp_perp H U
      intro x hx
      rw [← hsp] at hx
      have : Submodule.span K ((L ⊓ rs (𝓞 K) (perp H U) : Submodule (𝓞 K) V) : Set V) ≤
          LinearMap.ker (H.B.flip (v - p v - d)) := by
        rw [Submodule.span_le]
        intro b hb
        have h2 : H.B b v = H.B b d := h' ⟨b, hb⟩
        show H.B b (v - p v - d) = 0
        rw [map_sub, map_sub, h0 v b hb.2, h2, sub_zero, sub_self]
      exact this hx
    exact (Submodule.disjoint_def.1 hc.disjoint) _ h1 ((perp H U).sub_mem (hq v) hy)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨hq v, fun b hb => ?_⟩
    have : H.B (p v) b = 0 := by rw [← H.herm, h0 v b hb.2, star_zero]
    rw [map_sub, LinearMap.sub_apply, this, sub_zero]
    exact integral H hU hv hb.1

include hc hU in

theorem idx_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    idx (dual H (L ⊓ rs (𝓞 K) U)) (L ⊓ rs (𝓞 K) U) ≠ 0 := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  have hM : IsLatMod (L ⊓ rs (𝓞 K) U) U ⊥ := by
    refine ⟨⟨L ⊓ rs (𝓞 K) U, ?_, by simp⟩, span_inf hL U⟩
    have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) U) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  obtain ⟨h1, h2⟩ := (GlobalTheory.DegCnt.DelScale.main K V H hK _ _ U ⊥ bot_le (fun x hx =>
    ⟨fun h => (Submodule.disjoint_def.1 hc.disjoint) x hx ((mem_perp_iff H U x).2 h), by
      rintro rfl y _
      simp⟩) hM hM).2.2.2 ((isIntegralLat_iff H _).2 fun x hx y hy => integral H hU hx.1 hy.1)
  intro h
  rw [h] at h2
  have : (0 : ℝ) < del H (L ⊓ rs (𝓞 K) U) ^ 2 := by positivity
  rw [h2] at this
  simp at this

end Proj

theorem encard_gluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  intro K V _ _ _ _ _ _ _ _ H hK U A B x hc hx
  set S := {Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B} with hS
  rcases S.eq_empty_or_nonempty with h | ⟨L₀, hL₀, hA₀, hB₀⟩
  · rw [h]; simp
  obtain ⟨p, hp, hq⟩ : ∃ p : V →ₗ[K] V, (∀ v, p v ∈ U) ∧ ∀ v, v - p v ∈ perp H U :=
    ⟨U.projection _ hc, fun v => Submodule.projection_apply_mem hc v, fun v => Submodule.sub_projection_mem hc v⟩
  have hx0 : x ≠ 0 := by rw [← hx, ← hA₀]; exact idx_ne_zero H hc hL₀ hK
  have hpA : ∀ L ∈ S, ∀ v ∈ L, p v ∈ dual H A := fun L hL v hv => hL.2.1 ▸ proj_mem_dual H hL.1 hp hq hv
  have hD : ∀ L ∈ S, ∀ d, d ∈ dual H B ↔ ∃ v ∈ L, v - p v = d := fun L hL d =>
    hL.2.2 ▸ mem_dual_iff_proj H hc hL.1 hp hq d
  have hS₀ : L₀ ∈ S := ⟨hL₀, hA₀, hB₀⟩
  let q : V →ₗ[𝓞 K] V := (LinearMap.id - p).restrictScalars (𝓞 K)
  have hqv : ∀ v, q v = v - p v := fun _ => rfl
  have hfin : Module.Finite (𝓞 K) (dual H B) := by
    have e : dual H B = L₀.map q := by
      ext d; rw [hD L₀ hS₀]; rfl
    rw [e, Module.Finite.iff_fg]
    exact ((isLatMod_top_bot_iff L₀).1 hL₀.1).fg.map _
  have hflat := flat_of_submodule (dual H B)
  have hI : Ideal.span {(x : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hx0
  have := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨t, ht⟩ := exists_gens (𝓞 K) (dual H B) (Ideal.span {(x : 𝓞 K)})
  have hrk : Module.finrank (𝓞 K) (dual H B) ≤ Module.finrank K (perp H U) := by
    refine finrank_le fun d hd => ?_
    obtain ⟨v, -, rfl⟩ := (hD L₀ hS₀ d).1 hd
    exact hq v
  have hAL : ∀ L ∈ S, A ≤ L := fun L hL => hL.2.1 ▸ inf_le_left
  have hBL : ∀ L ∈ S, B ≤ L := fun L hL => hL.2.2 ▸ inf_le_left
  have hxB : ∀ d ∈ dual H B, (x : 𝓞 K) • d ∈ B := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (hD L₀ hS₀ d).1 hd
    have h1 : x • p v ∈ A := by
      have := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := (dual H A).toAddSubgroup) (hpA L₀ hS₀ v hv)
      rwa [show A.toAddSubgroup.relIndex (dual H A).toAddSubgroup = x from hx] at this
    rw [← hB₀]
    refine ⟨?_, (rs (𝓞 K) (perp H U)).smul_mem _ (hq v)⟩
    rw [Nat.cast_smul_eq_nsmul, smul_sub]
    exact L₀.sub_mem (nsmul_mem hv x) (hAL L₀ hS₀ h1)
  have hpB : ∀ b ∈ B, p b = 0 := by
    intro b hb
    rw [← hB₀] at hb
    refine (Submodule.disjoint_def.1 hc.disjoint) _ (hp b) ?_
    simpa using (perp H U).sub_mem hb.2 (hq b)
  choose w hw hw' using fun (L : S) i => (hD L L.2 (t i)).1 (t i).2
  let Q := (dual H A).toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf (dual H A).toAddSubgroup
  have hQ : Nat.card Q = x := hx
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hx0)
  let f : S → Fin (Module.finrank (𝓞 K) (dual H B)) → Q := fun L i =>
    QuotientAddGroup.mk ⟨p (w L i), hpA L L.2 _ (hw L i)⟩
  have key : ∀ L L' : S, f L = f L' → L.1 ≤ L'.1 := by
    intro L L' e v hv
    have h1 : ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype = ⊤ := by
      refine ht _ (fun i => ⟨w L i, ⟨hw L i, ?_⟩, hw' L i⟩) ?_
      · have h2 : -p (w L i) + p (w L' i) ∈ A := QuotientAddGroup.eq.1 (congrFun e i)
        have h3 : w L i = w L' i - (-p (w L i) + p (w L' i)) := by
          have := (hw' L i).trans (hw' L' i).symm
          linear_combination (norm := module) this
        rw [h3]
        exact L'.1.sub_mem (hw L' i) (hAL L' L'.2 h2)
      · refine Submodule.smul_le.2 fun r hr d _ => ?_
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h2 : (c * x) • (d : V) ∈ B := by rw [mul_smul]; exact B.smul_mem _ (hxB d d.2)
        refine ⟨(c * x) • (d : V), ⟨hBL L L.2 h2, hBL L' L'.2 h2⟩, ?_⟩
        rw [hqv, hpB _ h2, sub_zero]; rfl
    have h2 : (⟨v - p v, (hD L L.2 _).2 ⟨v, hv, rfl⟩⟩ : dual H B) ∈
        ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype := h1 ▸ Submodule.mem_top
    obtain ⟨u, ⟨hu, hu'⟩, e'⟩ := h2
    have e'' : u - p u = v - p v := e'
    have h3 : v - u ∈ A := by
      rw [← L.2.2.1]
      refine ⟨L.1.sub_mem hv hu, ?_⟩
      have : v - u = p v - p u := by linear_combination (norm := module) -e''
      rw [this]
      exact U.sub_mem (hp v) (hp u)
    simpa using L'.1.add_mem (hAL L' L'.2 h3) hu'
  have hf : Function.Injective f := fun L L' e => Subtype.ext (le_antisymm (key L L' e) (key L' L e.symm))
  have : Finite S := Finite.of_injective f hf
  have h1 : Nat.card S ≤ x ^ Module.finrank K (perp H U) := by
    refine (Nat.card_le_card_of_injective f hf).trans ?_
    rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx0) hrk
  rw [← (Set.toFinite S).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h1

end GlobalTheory.DegCnt.Glue
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_unimodular_hermGluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  atlas_forward_decl GlobalTheory.DegCnt.Glue.encard_gluings_le
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  haveI : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  haveI : Module.Finite R (LinearMap.range π) := inferInstance
  haveI : Module.Flat R (LinearMap.range π) := inferInstance
  haveI : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.fg hL.span_eq_top (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_exists_unipotent_split_lattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  atlas_forward_decl GlobalTheory.DegCnt.SplitLift.main
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.OmCount

theorem encard_le_of_fibres {α β : Type*} (S : Set α) (A : Set β) (f : α → β) (c : ℝ≥0∞)
    (hA : ∀ x ∈ S, f x ∈ A)
    (hc : ∀ x ∈ S, ((({y | y ∈ S ∧ f y = f x} : Set α).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((A.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun x : S => (⟨f x, hA x x.2⟩ : A))]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [ENNReal.tsum_set_one]
  rcases Set.eq_empty_or_nonempty ((fun x : S => (⟨f x, hA x x.2⟩ : A)) ⁻¹' {a}) with h | ⟨x, hx⟩
  · rw [h]; simp
  · refine le_trans (ENat.toENNReal_le.2 ?_) (hc x x.2)
    refine Set.encard_le_encard_of_injOn (f := Subtype.val) ?_ Subtype.val_injective.injOn
    intro y hy
    refine ⟨y.2, ?_⟩
    have h1 : (⟨f y, hA y y.2⟩ : A) = a := hy
    have h2 : (⟨f x, hA x x.2⟩ : A) = a := hx
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem tsum_orbits_le {G α : Type*} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞) (S : Set α)
    (B : ℝ≥0∞) (h : ∀ x, Q x → w x ≤ B ∧ ∃ s : G, s • x ∈ S) :
    (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * B := by
  set T : Set (MulAction.orbitRel.Quotient G α) := {o | Q o.out} with hT
  have h1 : (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤ ∑' _ : T, B := by
    rw [tsum_subtype T (fun _ => B)]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases ho : Q o.out
    · rw [if_pos ho, Set.indicator_of_mem (show o ∈ T from ho)]
      exact (h _ ho).1
    · rw [if_neg ho]; exact zero_le
  refine h1.trans ?_
  rw [ENNReal.tsum_set_const]
  gcongr
  have h2 : T ⊆ (fun x : α => (Quotient.mk (MulAction.orbitRel G α) x)) '' S := by
    intro o ho
    obtain ⟨s, hs⟩ := (h _ ho).2
    refine ⟨_, hs, ?_⟩
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound ⟨s, rfl⟩
  exact (Set.encard_le_encard h2).trans (Set.encard_image_le _ _)

section

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

theorem idx_dual_sup (H : HermSpace K V) (W I : Submodule K V) (A : Submodule R V) (hA : A ≤ rs R W)
    (hWI : W ⊓ I = ⊥) (h1 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B x y = 0) (h2 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B y x = 0)
    (hint : IsIntegralLat H A) :
    idx (dual H (A ⊔ rs R I)) (A ⊔ rs R I) = idx (dual H A) A := by
  have hsp : Submodule.span K (A : Set V) ≤ W := Submodule.span_le.2 hA
  have hdW : dual H A ≤ rs R W := fun y hy => hsp ((mem_dual_iff H A y).1 hy).1
  have hAd : A ≤ dual H A := fun y hy => (mem_dual_iff H A y).2
    ⟨Submodule.subset_span hy, fun x hx => (isIntegralLat_iff H A).1 hint y hy x hx⟩
  have hspan : Submodule.span K ((A ⊔ rs R I : Submodule R V) : Set V) = Submodule.span K (A : Set V) ⊔ I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : A ⊔ rs R I ≤ rs R (Submodule.span K (A : Set V) ⊔ I) :=
        sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span hx))
          (fun x hx => Submodule.mem_sup_right hx)
      exact this
    · exact sup_le (Submodule.span_mono fun x hx => Submodule.mem_sup_left hx)
        (fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx))
  have hd : dual H (A ⊔ rs R I) = dual H A ⊔ (A ⊔ rs R I) := by
    rw [← sup_assoc, sup_eq_left.2 hAd]
    apply le_antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := (mem_dual_iff H _ y).1 hy
      rw [hspan] at hy1
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy1
      refine Submodule.add_mem_sup ((mem_dual_iff H A a).2 ⟨ha, fun x hx => ?_⟩) hi
      have := hy2 x (Submodule.mem_sup_left hx)
      rwa [map_add, LinearMap.add_apply, h2 x (Submodule.mem_sup_left (hA hx)) i hi, add_zero] at this
    · intro y hy
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨ha1, ha2⟩ := (mem_dual_iff H A a).1 ha
      refine (mem_dual_iff H _ _).2 ⟨?_, fun x hx => ?_⟩
      · rw [hspan]; exact Submodule.add_mem_sup ha1 hi
      · obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add, h1 (a + i) (Submodule.add_mem_sup (hsp ha1) hi) i' hi', add_zero, map_add,
          LinearMap.add_apply, h2 a' (Submodule.mem_sup_left (hA ha')) i hi, add_zero]
        exact ha2 a' ha'
  have hinf : (A ⊔ rs R I) ⊓ dual H A = A := by
    rw [sup_inf_assoc_of_le _ hAd, sup_eq_left]
    intro x hx
    have : x ∈ W ⊓ I := ⟨hdW hx.2, hx.1⟩
    rw [hWI, Submodule.mem_bot] at this
    rw [this]; exact A.zero_mem
  unfold idx
  rw [hd, Submodule.sup_toAddSubgroup (dual H A), AddSubgroup.relIndex_sup_right,
    ← AddSubgroup.inf_relIndex_right]
  congr 1
  exact congrArg Submodule.toAddSubgroup hinf

end

theorem numeric (r k : ℕ) (i b c n Db Del NT x : ℝ) (hi : 0 < i) (hb : 0 ≤ b) (hn0 : 0 ≤ n) (hx0 : 0 ≤ x)
    (hDb : 1 ≤ Db) (hDel : 1 ≤ Del) (hNT : 1 ≤ NT) (hn : n ≤ (Db * NT) ^ 2) (hx : x ≤ (Del * NT) ^ 2) :
    i ^ ((k : ℝ) + c) * (n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      (b ^ k * Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) ≤
    (i * b) ^ k * i ^ c * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3) := by
  set M := Db * Del * NT with hM
  have hM1 : Db * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDel) (mul_nonneg (zero_le_one.trans hDb) (zero_le_one.trans hNT))]
  have hM2 : Del * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDb) (mul_nonneg (zero_le_one.trans hDel) (zero_le_one.trans hNT))]
  have hM3 : Del ≤ M := le_trans (le_mul_of_one_le_right (by linarith) hNT) hM2
  have hM4 : 1 ≤ M := hDel.trans hM3
  have hn' : n ≤ M ^ 2 := hn.trans (by gcongr)
  have hx' : x ≤ M ^ 2 := hx.trans (by gcongr)
  have hic : 0 ≤ i ^ c := by positivity
  calc _ = (i * b) ^ k * i ^ c * ((n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        rw [Real.rpow_add hi, Real.rpow_natCast, mul_pow]; ring
    _ ≤ (i * b) ^ k * i ^ c * (((M ^ 2) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * (M ^ 2) ^ (2 * r + 1) *
      M ^ r * (M ^ 2) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        have : 0 ≤ Del := by linarith
        gcongr
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [← pow_mul, ← pow_add]
        refine pow_le_pow_right₀ hM4 ?_
        ring_nf
        nlinarith [Nat.zero_le r, Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3)]

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem om_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) {s : V ≃ₗ[K] V} (hs : s ∈ N.R) : N.om (s • Λ) = N.om Λ := by
  obtain ⟨-, hS, -, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s hs
  obtain ⟨-, -, -, -, hRef, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨-, -, -, -, hnil⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  have hL : Submodule.IsLattice K Λ := ((isUnimod_iff H Λ).1 hΛ.1.1).1
  unfold NF.om NF.Gam
  rw [hS.1]
  exact (Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hL hRef).2 s hs

theorem isLatMod_latLa (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) :
    IsLatMod (latLa N.F N.F' Λ (g : 𝓞 K)) (wSp N.F N.F') (II N.F N.F') := by
  obtain ⟨hTh, -, -, -, -, -, -, ⟨M, -, hM⟩, hsp⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  obtain ⟨⟨⟨⟨M', hM', hL⟩, -⟩, -⟩, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  have h0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hI : rs (𝓞 K) (II N.F N.F') ≤ latLa N.F N.F' Λ (g : 𝓞 K) := le_trans (by rw [hM]; exact le_sup_right) hTh
  refine ⟨⟨latLa N.F N.F' Λ (g : 𝓞 K) ⊓ M', ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M' := isNoetherian_of_fg_of_noetherian _ hM'
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 (h0.trans inf_le_left)).symm
  · exact Submodule.span_le.2 fun x hx => (h0 hx).2
  · rw [← hsp]; exact Submodule.span_mono hTh

theorem inf_Wt_of_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {Λ : Submodule (𝓞 K) V} (h : N.Split Λ) :
    Λ ⊓ rs (𝓞 K) N.Wt = latTh N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt := by
  obtain ⟨-, hlift, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  rw [h, sup_inf_assoc_of_le _ inf_le_right, eq_comm, sup_eq_left]
  intro x hx
  have : x ∈ N.Wt ⊓ II N.F N.F' := ⟨hx.2, hx.1⟩
  rw [hlift.2.1, Submodule.mem_bot] at this
  rw [this]; exact Submodule.zero_mem _

theorem idx_dual_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) (h : N.Split Λ) :
    (idx (dual H (Λ ⊓ rs (𝓞 K) N.Wt)) (Λ ⊓ rs (𝓞 K) N.Wt) : ℝ) ≤ (N.Del * N.NT) ^ 2 := by
  obtain ⟨-, hlift, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hgi, -, hdel, hlat⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have h1 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B x y = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    exact (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1))
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← H.herm, h1 x hx y hy, star_zero]
  have hintΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hu : dual H Λ = Λ := hΛ.1.1.2
    rw [← hu] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2 y hy
  have hintA : IsIntegralLat H (Λ ⊓ rs (𝓞 K) N.Wt) :=
    (isIntegralLat_iff H _).2 fun x hx y hy => hintΛ x hx.1 y hy.1
  have hintT : IsIntegralLat H (latTh N.F N.F' Λ) := by
    rw [h]
    refine (isIntegralLat_iff H _).2 fun x hx y hy => ?_
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, h1 (a + i) (Submodule.add_mem_sup ha.2 hi) i' hi', add_zero, map_add,
      LinearMap.add_apply, h2 a' (Submodule.mem_sup_left ha'.2) i hi, add_zero]
    exact hintΛ a ha.1 a' ha'.1
  have hrad : ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    rw [hw]
    intro x hx
    refine ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    have haa := hx0 a (Submodule.mem_sup_left ha)
    rw [map_add, LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have ha0 : a = 0 := by
      by_contra hne
      have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
      have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
      rw [e, haa] at this
      simp at this
    rw [ha0, zero_add]; exact hi
  have hd := (DelScale.main K V H hK _ _ _ _ (by rw [hw]; exact le_sup_right) hrad hlat hlat).2.2.2 hintT
  rw [← idx_dual_sup H N.Wt (II N.F N.F') _ inf_le_right hlift.2.1 h1 h2 hintA, ← h, ← hd.2, hdel]
  have : 0 ≤ N.NT := by unfold NF.NT; positivity
  gcongr

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ i b
  obtain ⟨𝔠, hcn, hDb, hDel, hQ⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors K V H hK r N g Λ hg hΛ
  refine hQ _ fun c0 c1 c2 c3 => ?_
  obtain ⟨-, -, hcompl, hrk, -, -, -, -, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hrkPi : Module.finrank K (perp H N.Wt) = 2 * r + 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    unfold NF.Pi at this
    omega
  have hNT : 1 ≤ N.NT := one_le_pow₀ (by exact_mod_cast hT)
  set S : Set (Submodule (𝓞 K) V) := {Λ' | (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ∧
    N.Split Λ' ∧ N.Near (𝔠 ^ (12 * r + 50)) Λ'} with hS
  set B : ℝ := (b : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r *
    (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2) with hB
  have hQs : ∀ Λ', (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) → ∀ s ∈ N.R,
      (N.IsTerm g (s • Λ') ∧ N.SameDat g Λ (s • Λ') ∧ N.iI g (s • Λ') = i ∧ N.bI (s • Λ') = b) := by
    rintro Λ' ⟨h1, h2, h3, h4⟩ s hs
    obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ' hg h1 s hs
    refine ⟨k1, ⟨k2.1.trans h2.1, k2.2.1.trans h2.2.1, k2.2.2.trans h2.2.2⟩, ?_, k4.trans h4⟩
    rw [← h3]
    unfold NF.iI latLa
    rw [k3, k2.2.2]
  have step1 : N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal B := by
    refine tsum_orbits_le (G := N.R)
      (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) (fun Λ' => ENNReal.ofReal (N.om Λ')) S _ ?_
    intro Λ' h
    obtain ⟨s, hs, hsp⟩ := GlobalTheory.T.hermFramePair_exists_unipotent_split_lattice K V H hK r N g Λ' hg h.1
    have h' := hQs Λ' h s hs
    obtain ⟨t, ht, hsp', hnear⟩ := GlobalTheory.T.hermFramePairNormalForm_exists_conj_near_reference K V H hK r N g _ hg h'.1 𝔠 c0 c1 c2 c3 hsp
    have h'' := hQs _ h' t ht.1
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ⟨t, ht.1⟩ * ⟨s, hs⟩, ?_⟩
    · rw [← om_smul hK N hg h.1 hs, ← om_smul hK N hg h'.1 ht.1, hB, ← h''.2.2.2]
      exact GlobalTheory.T.splitTermWeight_le_near_referenceLattice K V H hK r N g _ hg h''.1 𝔠 c0 c1 c2 c3 _ hsp' hnear
    · rw [mul_smul]
      exact ⟨h'', hsp', hnear⟩
  refine step1.trans ?_
  rcases Set.eq_empty_or_nonempty S with hE | ⟨Λ₀, hΛ₀⟩
  · rw [hE]; simp
  have hi : 1 ≤ i := by
    rw [← hΛ₀.1.2.2.1]
    exact (GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ₀ hg hΛ₀.1.1).2.2.1
  have hTh := GlobalTheory.T.card_sublattices_definiteQuotient_normalForm_le K V H hK r N _ i hi (isLatMod_latLa hK N hg hΛ)
  have hP := GlobalTheory.T.encard_lattices_near_reference_lattice_le K V H hK r N (𝔠 ^ (12 * r + 50)) (pow_ne_zero _ c0)
  have step2 := encard_le_of_fibres S
    ({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧
        idx (latLa N.F N.F' Λ (g : 𝓞 K)) Th = i} ×ˢ
      {P : Submodule (𝓞 K) V | 𝔠 ^ (12 * r + 50) • N.P0 ≤ P ∧ 𝔠 ^ (12 * r + 50) • P ≤ N.P0})
    (fun Λ' => (latTh N.F N.F' Λ', Λ' ⊓ rs (𝓞 K) N.Pi))
    (ENNReal.ofReal (((N.Del * N.NT) ^ 2) ^ (2 * r + 1))) ?_ ?_
  rotate_left
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have e : latLa N.F N.F' Λ' (g : 𝓞 K) = latLa N.F N.F' Λ (g : 𝓞 K) := by
      unfold latLa; rw [h2.2.2]
    refine ⟨⟨?_, ?_, ?_⟩, h6⟩
    · show _ ≤ latTh N.F N.F' Λ'
      rw [h5]; exact le_sup_right
    · rw [← e]; exact (GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1).1
    · rw [← e]; exact h3
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have hgl := GlobalTheory.T.encard_unimodular_hermGluings_le K V H hK N.Wt (Λ' ⊓ rs (𝓞 K) N.Wt) (Λ' ⊓ rs (𝓞 K) N.Pi) _ hcompl rfl
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) (hgl.trans ?_)
    · rintro Λ'' ⟨⟨⟨k1, -⟩, k5, -⟩, k⟩
      refine ⟨k1.1.1, ?_, (Prod.ext_iff.1 k).2⟩
      rw [inf_Wt_of_split hK N k5, inf_Wt_of_split hK N h5]
      exact congrArg (· ⊓ rs (𝓞 K) N.Wt) (Prod.ext_iff.1 k).1
    · rw [hrkPi, ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast]
      gcongr
      exact idx_dual_le hK N hg h1 h5
  rw [Set.encard_prod, ENat.toENNReal_mul] at step2
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hDel0 : 0 ≤ N.Del := by linarith
  have hP' : (Ideal.absNorm (𝔠 ^ (12 * r + 50)) : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) =
      ENNReal.ofReal (((Ideal.absNorm 𝔠 : ℝ) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2)) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, map_pow,
      Nat.cast_pow]
  rw [hP'] at hP
  refine le_trans (mul_le_mul_left (step2.trans (mul_le_mul_left (mul_le_mul' hTh hP) _)) _) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (numeric r _ i b (cf K) _ N.Db N.Del N.NT _ hipos (by positivity) (by positivity)
    (by positivity) hDb hDel hNT hcn le_rfl)

end GlobalTheory.DegCnt.OmCount
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_omSum_same_datum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  atlas_forward_decl GlobalTheory.DegCnt.OmCount.main
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem tsum_ite_le_sum_fibres {α β : Type*} (Q : α → Prop) (R : β → α → Prop) (f : α → ℝ≥0∞) (S : Finset β)
    [∀ a, Decidable (Q a)] [∀ p a, Decidable (R p a)]
    (h : ∀ a, Q a → ∃ p ∈ S, R p a) :
    (∑' a, if Q a then f a else 0) ≤ ∑ p ∈ S, ∑' a, if R p a then f a else 0 := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hq
  · obtain ⟨p, hp, hr⟩ := h a hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0)
      (fun _ _ => zero_le) hp)
    simp [hr]
  · exact zero_le

theorem cf_nonneg_of_numberField (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have := Real.logb_nonneg (b := 2) (by norm_num) h
  unfold cf
  linarith

theorem index_pair_bound {G D c X : ℝ} (k i b : ℕ) (hG : 0 < G) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (h : G * (i : ℝ) ^ 2 * (b : ℝ) ^ 2 ≤ D) (hi : (i : ℝ) ≤ D) :
    ((i : ℝ) * b) ^ k * (i : ℝ) ^ c * X ≤ (D / G) ^ ((k : ℝ) / 2) * D ^ c * X := by
  have h0 : (0 : ℝ) ≤ (i : ℝ) * b := by positivity
  have h1 : ((i : ℝ) * b) ^ 2 ≤ D / G := by
    rw [le_div_iff₀ hG]; nlinarith
  have h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2) := by
    calc ((i : ℝ) * b) ^ k = (((i : ℝ) * b) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (i : ℝ) ^ c ≤ D ^ c := Real.rpow_le_rpow (by positivity) hi hc
  have h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2) := le_trans (by positivity) h2
  gcongr

theorem omSum_sameDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, hG, hI, -, hGI, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have hG1 : (1 : ℝ) ≤ N.gI g Λ := by exact_mod_cast hG
  have hI1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hI
  have hD : 1 ≤ N.Del := le_trans (by nlinarith) hGI
  have hnD : ∀ l, 0 ≤ N.nD l := fun l => by
    unfold NF.nD
    split_ifs
    · positivity
    · exact le_rfl
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => hnD l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) := by positivity
  set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter
    (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS
  have hcard : (S.card : ℝ) ≤ N.Del ^ 2 := by
    have h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊ := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del := Nat.floor_le (by linarith)
    calc (S.card : ℝ) ≤ (⌊N.Del⌋₊ : ℝ) * ⌊N.Del⌋₊ := by exact_mod_cast h1
      _ ≤ N.Del * N.Del := by gcongr
      _ = _ := by ring
  have hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' →
      ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2 := by
    rintro Λ' ⟨h1, h2⟩
    refine ⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩
    obtain ⟨-, -, hI', hb, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1
    have hb0 := (GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ' hg h1).1
    have hgg : N.gI g Λ' = N.gI g Λ := by
      unfold NF.gI flagPairDefinitePartLattice latLa
      rw [h2.1, h2.2.2]
    rw [hgg] at hb
    have hi1 : (1 : ℝ) ≤ N.iI g Λ' := by exact_mod_cast hI'
    have hb1 : (1 : ℝ) ≤ N.bI Λ' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    have hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2 := by nlinarith
    have hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2 := by nlinarith
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩
    · refine le_trans ?_ hb
      calc (N.iI g Λ' : ℝ) = 1 * (N.iI g Λ' : ℝ) * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · refine le_trans ?_ hb
      calc (N.bI Λ' : ℝ) = 1 * 1 * (N.bI Λ' : ℝ) := by ring
        _ ≤ _ := by gcongr; linarith
  have hc := cf_nonneg_of_numberField K
  have hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X := by
    have : 0 ≤ N.Del := by linarith
    positivity
  calc N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ')
      ≤ ∑ p ∈ S, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2) := by
        unfold NF.omSum
        exact @tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _)
          (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine (GlobalTheory.T.hermFramePair_omSum_same_datum_le K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        refine index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_
        exact le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))
    _ = ENNReal.ofReal (S.card *
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))
        rw [Real.rpow_add (by linarith), Real.rpow_two]
        ring

end GlobalTheory.DegCnt
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFrame_weightSum_sameDatum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  atlas_forward_decl GlobalTheory.DegCnt.omSum_sameDat_le
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.GlueZ

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_mem {t : K} (h : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 h
  have h1 : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    map_isIntegral_int (starRingEnd K) a.isIntegral_coe
  exact Submodule.mem_one.2 ⟨⟨_, h1⟩, rfl⟩

def Good (H : HermSpace K V) (S : Submodule K V) (z : V) (M : Submodule (𝓞 K) V) : Prop :=
  dual H M = M ∧ Submodule.span K (M : Set V) = S ∧ ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K)

variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem Good.z_mem (h : Good H S z M) : z ∈ M := by
  simpa using (h.2.2 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)

theorem Good.int (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy

theorem Good.mem_S (h : Good H S z M) {x : V} (hx : x ∈ M) : x ∈ S :=
  h.2.1 ▸ Submodule.subset_span hx

theorem Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩

theorem Good.exists_one (h : Good H S z M) (hz : H.B z z ≠ 0) : ∃ y ∈ M, H.B y z = 1 := by
  let J : Ideal (𝓞 K) :=
    (M.map ((H.B.flip z).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ a : 𝓞 K, a ∈ J ↔ ∃ y ∈ M, H.B y z = algebraMap (𝓞 K) K a := fun a => by
    simp [J]
  have hne : J ≠ ⊥ := by
    intro h0
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int h.z_mem h.z_mem)
    have : a ∈ J := (hJ a).2 ⟨z, h.z_mem, ha.symm⟩
    rw [h0, Ideal.mem_bot] at this
    exact hz (by rw [← ha, this, map_zero])
  have htop : J = ⊤ := by
    by_contra hJ1
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hne hJ1
    apply hx1
    rw [FractionalIdeal.mem_inv_iff (by simpa using hne)] at hx
    have h2 : star x • z ∈ M := by
      refine h.mem_of (S.smul_mem _ (h.mem_S h.z_mem)) fun y hy => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hy h.z_mem)
      have h3 := hx (algebraMap (𝓞 K) K a)
        (FractionalIdeal.mem_coeIdeal_of_mem _ ((hJ a).2 ⟨y, hy, ha.symm⟩))
      have h4 : x * algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K) := by
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h3
        exact Submodule.mem_one.2 ⟨b, hb⟩
      have h5 := star_mem h4
      rw [ha, star_mul', H.herm] at h5
      simpa using h5
    have h6 := star_mem ((h.2.2 _).1 h2)
    rw [star_star] at h6
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h6
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨y, hy, e⟩ := (hJ 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨y, hy, by rw [e, map_one]⟩

theorem Good.proj (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp

theorem count (T : ℕ) (hT : T ≠ 0) (hz : H.B z z = -(T : K)) (M₁ : Submodule (𝓞 K) V) (h₁ : Good H S z M₁) :
    {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)}.encard ≤
      (T ^ Module.finrank ℚ K : ℕ) := by
  have hz0 : H.B z z ≠ 0 := by rw [hz]; simpa using hT
  obtain ⟨y₁, hy₁, e₁⟩ := h₁.exists_one hz0
  have e₁' : H.B z y₁ = 1 := by rw [← H.herm, e₁, star_one]
  set 𝓢 := {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)} with h𝓢
  have key : ∀ M : Submodule (𝓞 K) V, ∃ (y : V) (u : K) (a : 𝓞 K), M ∈ 𝓢 →
      y ∈ M ∧ H.B y z = 1 ∧ y + u • z ∈ M₁ ∧ algebraMap (𝓞 K) K a = 1 - u * T := by
    intro M
    by_cases hM : M ∈ 𝓢
    swap
    · exact ⟨0, 0, 0, fun h => absurd h hM⟩
    obtain ⟨y, hy, e⟩ := hM.1.exists_one hz0
    have hm : y + (-H.B y y₁) • z ∈ M₁ := by
      refine h₁.mem_of (S.add_mem (hM.1.mem_S hy) (S.smul_mem _ (h₁.mem_S h₁.z_mem))) fun m hm => ?_
      obtain ⟨a, ha, ha0⟩ := h₁.proj hy₁ e₁ hm
      have h2 := hM.1.int hy ((hM.2 _ ha0).2 ha)
      have h3 : H.B z (m - a • y₁) = 0 := by rw [← H.herm, ha0, star_zero]
      have h4 : m = (m - a • y₁) + (algebraMap (𝓞 K) K a) • y₁ := by rw [algebraMap_smul]; abel
      generalize m - a • y₁ = m₀ at h2 h3 h4
      rw [h4]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3, e₁',
        smul_eq_mul]
      convert h2 using 1
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h₁.int hm h₁.z_mem)
    refine ⟨y, -H.B y y₁, a, fun _ => ⟨hy, e, hm, ?_⟩⟩
    rw [ha, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, e, hz, smul_eq_mul]
    ring
  choose y u a hyu using key
  let I : Ideal (𝓞 K) := Ideal.span {(T : 𝓞 K)}
  have hle : ∀ M ∈ 𝓢, ∀ M' ∈ 𝓢, Ideal.Quotient.mk I (a M) = Ideal.Quotient.mk I (a M') → M ≤ M' := by
    intro M hM M' hM' e
    obtain ⟨p1, p2, p3, p4⟩ := hyu M hM
    obtain ⟨q1, q2, q3, q4⟩ := hyu M' hM'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
    have hb' : algebraMap (𝓞 K) K b = u M' - u M := by
      have := congrArg (algebraMap (𝓞 K) K) hb
      rw [map_sub, map_mul, map_natCast, p4, q4] at this
      have hT' : (T : K) ≠ 0 := by exact_mod_cast hT
      apply mul_right_cancel₀ hT'
      rw [this]; ring
    have h5 : y M - y M' ∈ M₁ := by
      have := M₁.add_mem (M₁.sub_mem p3 q3) (M₁.smul_mem b h₁.z_mem)
      rw [← algebraMap_smul K b z, hb', sub_smul] at this
      convert this using 1
      abel
    have h6 : H.B (y M - y M') z = 0 := by rw [map_sub, LinearMap.sub_apply, p2, q2, sub_self]
    have h7 : y M ∈ M' := by simpa using M'.add_mem ((hM'.2 _ h6).2 h5) q1
    intro m hm
    obtain ⟨c, hc, hc0⟩ := hM.1.proj p1 p2 hm
    simpa using M'.add_mem ((hM'.2 _ hc0).2 ((hM.2 _ hc0).1 hc)) (M'.smul_mem c h7)
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h8 : 𝓢.encard ≤ (Set.univ : Set (𝓞 K ⧸ I)).encard :=
    Set.encard_le_encard_of_injOn (f := fun M => Ideal.Quotient.mk I (a M)) (fun _ _ => Set.mem_univ _)
      fun M hM M' hM' e => le_antisymm (hle M hM M' hM' e) (hle M' hM' M hM e.symm)
  refine h8.trans (le_of_eq ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem mem_lattice_zeroTorus {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]

end GlobalTheory.DegCnt.GlueZ

theorem GlobalTheory.DegCnt.GlueZ.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  have good : ∀ Λ', N.IsTerm g Λ' → GlueZ.Good H (uPerp N.F N.F') N.F'.z (latL N.F' N.F Λ') := fun Λ' h => by
    obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ' hg h
    exact ⟨h2.2, h2.1.2, h4⟩
  have hT : N.T ≠ 0 := by
    intro h0
    apply N.F'.hT
    rw [N.hT', h0, Nat.cast_zero]
  have hz : H.B N.F'.z N.F'.z = -(N.T : K) := N.hT' ▸ N.F'.zz
  have h1 := GlueZ.count N.T hT hz _ (good Λ hΛ)
  have h2 : {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧
      flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}.encard ≤ (N.T ^ Module.finrank ℚ K : ℕ) := by
    refine (Set.encard_le_encard ?_).trans h1
    rintro _ ⟨Λ', h, rfl, e⟩
    exact ⟨good Λ' h, fun y hy => by rw [GlueZ.mem_lattice_zeroTorus N Λ' y hy, GlueZ.mem_lattice_zeroTorus N Λ y hy, e]⟩
  haveI := hK.1
  have h3 : Module.finrank ℚ K = Formalism.HermitianLatticesTheory.fDeg K * 2 := by
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  refine (ENat.toENNReal_le.2 h2).trans (le_of_eq ?_)
  rw [NF.NT, ← pow_mul, ← h3, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rfl
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  atlas_forward_decl GlobalTheory.DegCnt.GlueZ.main
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.FixedForm

theorem sum_le_orbit {G α ι : Type} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞)
    (t : Finset ι) (x : ι → α) (hQ : ∀ i ∈ t, ∀ ρ : G, Q (ρ • x i) ∧ w (ρ • x i) = w (x i))
    (hd : ∀ i ∈ t, ∀ i' ∈ t, (∃ ρ : G, ρ • x i = x i') → i = i') :
    ∑ i ∈ t, w (x i) ≤ ∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0 := by
  let q : ι → MulAction.orbitRel.Quotient G α := fun i => Quotient.mk _ (x i)
  have hinj : ∀ i ∈ t, ∀ i' ∈ t, q i = q i' → i = i' := by
    intro i hi i' hi' h
    have h1 : (MulAction.orbitRel G α) (x i') (x i) := Quotient.exact h.symm
    rw [MulAction.orbitRel_apply] at h1
    exact hd i hi i' hi' h1
  have h1 : ∑ i ∈ t, w (x i) = ∑ o ∈ t.image q, if Q o.out then w o.out else 0 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 : (MulAction.orbitRel G α) (q i).out (x i) := Quotient.exact (Quotient.out_eq (q i))
    rw [MulAction.orbitRel_apply] at h2
    obtain ⟨ρ, hρ⟩ := h2
    have hρ' : ρ • x i = (q i).out := hρ
    rw [← hρ', if_pos (hQ i hi ρ).1, (hQ i hi ρ).2]
  rw [h1]
  exact ENNReal.sum_le_tsum _

theorem nD_nonneg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (l : ℕ) :
    0 ≤ N.nD l := by
  unfold NF.nD
  split_ifs
  · positivity
  · exact le_rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ₀ ι s Λ hg h0 hs hd
  set B : ℝ := (N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hB
  have hDel : 0 ≤ N.Del := nD_nonneg N _
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => nD_nonneg N l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hom := (GlobalTheory.DegAsm.WeightInf.main K V H hK r).1 N g
  let f : ι → Submodule (𝓞 K) V := fun i => latL N.F' N.F (Λ i)
  have hcard : ((s.image f).card : ℝ) ≤ N.NT ^ 2 := by
    have h1 := GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm K V H hK r N g Λ₀ hg h0
    have h2 : ((s.image f : Finset _) : Set (Submodule (𝓞 K) V)) ⊆ {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ₀} := by
      intro L hL
      rw [Finset.mem_coe, Finset.mem_image] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact ⟨Λ i, (hs i hi).1, rfl, (hs i hi).2.2.1⟩
    have h3 := (ENat.toENNReal_le.2 (Set.encard_le_encard h2)).trans h1
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hfib : ∀ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) ≤ B := by
    intro L hL
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hL
    have h1 := GlobalTheory.T.hermFrame_weightSum_sameDatum_le K V H hK r N g (Λ i₀) hg (hs i₀ hi₀).1
    have hgI : N.gI g (Λ i₀) = N.gI g Λ₀ := by
      unfold NF.gI latLa flagPairDefinitePartLattice
      rw [(hs i₀ hi₀).2.1, (hs i₀ hi₀).2.2.2]
    rw [hgI, ← hB] at h1
    have h2 := sum_le_orbit (G := N.R) (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g (Λ i₀) Λ')
      (fun Λ' => ENNReal.ofReal (N.om Λ')) (s.filter fun i => f i = f i₀) Λ
      (by
        intro i hi ρ
        obtain ⟨hi, hfi⟩ := Finset.mem_filter.1 hi
        obtain ⟨a1, ⟨a2, a3, a4⟩, -⟩ := GlobalTheory.DegCnt.StabInv.main K V H hK r N g (Λ i) hg (hs i hi).1 ρ.1 ρ.2
        refine ⟨⟨a1, a2.trans ((hs i hi).2.1.trans (hs i₀ hi₀).2.1.symm), a3.trans hfi,
          a4.trans ((hs i hi).2.2.2.trans (hs i₀ hi₀).2.2.2.symm)⟩, ?_⟩
        exact congrArg ENNReal.ofReal ((hom (Λ i) hg (hs i hi).1).2 ρ.1 ρ.2))
      (by
        rintro i hi i' hi' ⟨ρ, hρ⟩
        exact hd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 ⟨ρ.1, ρ.2, hρ⟩)
    have h3 : ∑ i ∈ s with f i = f i₀, ENNReal.ofReal (N.om (Λ i)) ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h1
      unfold NF.omSum
      convert h2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      (hom (Λ i) hg (hs i (Finset.mem_filter.1 hi).1).1).1.le), ENNReal.ofReal_le_ofReal_iff hB0] at h3
    exact h3
  calc ∑ i ∈ s, N.om (Λ i) = ∑ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ ≤ (s.image f).card • B := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = ((s.image f).card : ℝ) * B := nsmul_eq_mul _ _
    _ ≤ N.NT ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0

end GlobalTheory.DegAsm.FixedForm
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  atlas_forward_decl GlobalTheory.DegAsm.FixedForm.main
end
