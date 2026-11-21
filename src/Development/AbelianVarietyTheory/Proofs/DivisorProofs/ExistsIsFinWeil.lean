import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction

section
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private theorem sum_over_quotient_fixed_of_fixed {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (S : AddSubgroup X)
    [Fintype (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)]
    (hSA : ∀ s ∈ S, s ∈ A) (y : M) (hy : ∀ s ∈ S, W s y = y) :
    ∀ b ∈ A, W b (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      W ((Quotient.out q : ↥A.toAddSubgroup) : X) y) =
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        W ((Quotient.out q : ↥A.toAddSubgroup) : X) y := by
  intro b hb
  have hstep : ∀ x s : X, x ∈ A → s ∈ S → W (x + s) y = W x y := fun x s hx hs => by
    rw [← hW.comp_of_mem hA hx (hSA s hs), hy s hs]
  rw [map_sum]
  let b' : ↥A.toAddSubgroup := ⟨b, hb⟩
  refine Fintype.sum_equiv
    (Equiv.addLeft (QuotientAddGroup.mk b' : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup))
    _ _ (fun q => ?_)
  rw [hW.comp_of_mem hA hb (Quotient.out q).2 y]
  have hmem : -(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) ∈ S.addSubgroupOf A.toAddSubgroup := by
    rw [← QuotientAddGroup.eq]
    simp [QuotientAddGroup.out_eq']
  simp only [Equiv.coe_addLeft]
  have hdec : ((Quotient.out ((QuotientAddGroup.mk b' :
      ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) =
      (b + ((Quotient.out q : ↥A.toAddSubgroup) : X)) +
        ((-(b' + Quotient.out q) + Quotient.out ((QuotientAddGroup.mk b' :
          ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) + q) : ↥A.toAddSubgroup) : X) := by
    push_cast
    abel
  rw [hdec, hstep _ _ (A.add_mem hb (Quotient.out q).2) (AddSubgroup.mem_addSubgroupOf.mp hmem)]

open Classical in
open scoped BigOperators in

theorem _root_.GlobalTheory.FinWeil.span_translates_vacua : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, _root_.GlobalTheory.FinWeil.idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W hW A hA hloc
  rw [eq_top_iff]
  rintro v -
  obtain ⟨T, hT, hfix⟩ := hloc v
  have hAdual : ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1 := by
    unfold _root_.GlobalTheory.FinWeil.SelfDual at hA
    exact hA
  unfold _root_.GlobalTheory.FinWeil.idx at hT
  let S : AddSubgroup X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [hW.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => hW.zero_left t⟩
      neg_mem' := fun {a} ha => ⟨A.neg_mem ha.1, fun t ht => by
        rw [hW.neg_left, ha.2 t ht, inv_one]⟩ }
  have hSmem : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  let T₀ : AddSubgroup X := A.toAddSubgroup ⊓ T.toAddSubgroup
  have hS : ∀ a ∈ A.toAddSubgroup, a ∈ S ↔ ∀ t ∈ T.toAddSubgroup, γ a t = 1 :=
    fun a ha => ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hT₀ : ∀ t ∈ T.toAddSubgroup, t ∈ T₀ ↔ ∀ a ∈ A.toAddSubgroup, γ a t = 1 := by
    intro t ht
    constructor
    · rintro ⟨htA, -⟩ a ha
      exact hW.iso hA ha htA
    · intro h
      exact ⟨(hAdual t).2 fun a ha => hW.swap_eq_one (h a ha), ht⟩
  have hidx : T₀.relIndex T.toAddSubgroup ≠ 0 := by
    rwa [AddSubgroup.inf_relIndex_right]
  obtain ⟨hKN, -, -⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW S A.toAddSubgroup T₀ T.toAddSubgroup hS hT₀ hidx
  have hK : S.relIndex A.toAddSubgroup ≠ 0 := hKN ▸ hidx
  obtain ⟨-, -, horth⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T₀ T.toAddSubgroup S A.toAddSubgroup
    (fun t ht => by
      rw [hT₀ t ht]
      exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
        fun h a ha => hW.swap_eq_one (h a ha)⟩)
    (fun a ha => by
      rw [hS a ha]
      exact ⟨fun h t ht => hW.swap_eq_one (h t ht),
        fun h t ht => hW.swap_eq_one (h t ht)⟩) hK
  haveI : (S.addSubgroupOf A.toAddSubgroup).FiniteIndex := ⟨hK⟩
  haveI : (T₀.addSubgroupOf T.toAddSubgroup).FiniteIndex := ⟨hidx⟩
  letI := Fintype.ofFinite (↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup)
  letI := Fintype.ofFinite (↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup)
  have hz : ∀ t ∈ T, (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t • W ((Quotient.out q : ↥A.toAddSubgroup) : X) v)
      ∈ Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} := by
    intro t ht
    have hy : ∀ s ∈ S, W s (W t v) = W t v := by
      intro s hs
      rw [hW.comm, hs.2 t ht, one_smul, hfix s hs.1 hs.2]
    have hu := sum_over_quotient_fixed_of_fixed hW hA S (fun s hs => hs.1) (W t v) hy
    set c := γ (w • -t) t with hc_def
    have hc : c ≠ 0 := hW.ne_zero _ _
    have key : (∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) t •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
        W (-t) (c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v)) := by
      symm
      rw [map_smul, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hW.comm _ t v, map_smul, hW.neg_comp,
        ← hc_def, smul_smul, smul_smul, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [key]
    refine Submodule.subset_span ⟨-t, c⁻¹ • ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) (W t v), ?_, rfl⟩
    unfold _root_.GlobalTheory.FinWeil.Fixes
    intro a ha
    rw [map_smul, hu a ha]
  have horth' : ∀ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        γ ((Quotient.out p : ↥T.toAddSubgroup) : X) ((Quotient.out q : ↥A.toAddSubgroup) : X) =
      if ((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S then
        ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) else 0 := fun q => by
    rw [← finsum_eq_sum_of_fintype]
    exact horth _ (Quotient.out q).2
  have hsum : (∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
      ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
        γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
          W ((Quotient.out q : ↥A.toAddSubgroup) : X) v) =
      ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) • v := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hW.neg_right, ← hW.swap, horth']
    rw [Finset.sum_eq_single 0]
    · have h0 : ((Quotient.out (0 : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup) :
          ↥A.toAddSubgroup) : X) ∈ S :=
        AddSubgroup.mem_addSubgroupOf.mp
          ((QuotientAddGroup.eq_zero_iff _).mp (QuotientAddGroup.out_eq' 0))
      rw [if_pos h0, hfix _ h0.1 h0.2]
    · intro q _ hq
      have hqS : ¬ (((Quotient.out q : ↥A.toAddSubgroup) : X) ∈ S) := fun h => hq (by
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact AddSubgroup.mem_addSubgroupOf.mpr h)
      rw [if_neg hqS, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNne : ((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hidx
  have hv : v = (((T₀.relIndex T.toAddSubgroup : ℕ) : ℂ))⁻¹ •
      ∑ p : ↥T.toAddSubgroup ⧸ T₀.addSubgroupOf T.toAddSubgroup,
        ∑ q : ↥A.toAddSubgroup ⧸ S.addSubgroupOf A.toAddSubgroup,
          γ ((Quotient.out q : ↥A.toAddSubgroup) : X) (-((Quotient.out p : ↥T.toAddSubgroup) : X)) •
            W ((Quotient.out q : ↥A.toAddSubgroup) : X) v := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hNne, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ =>
    hz _ (T.neg_mem (Quotient.out p).2))

end GlobalTheory.FinWeil
end

open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ := by
  atlas_forward_decl GlobalTheory.FinWeil.span_translates_vacua
end

section
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private theorem eq_zero_of_sum_eigenvectors_eq_zero_of_injective {M ι α : Type} [AddCommGroup M] [Module ℂ M] (T : α → M →ₗ[ℂ] M)
    (χ : ι → α → ℂ) (hχ : Function.Injective χ) (s : Finset ι) (v : ι → M)
    (hv : ∀ i ∈ s, ∀ a, T a (v i) = χ i a • v i) (hsum : ∑ i ∈ s, v i = 0) : ∀ i ∈ s, v i = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at hsum
    have key : ∀ a, ∀ i ∈ s, (χ i a - χ j a) • v i = 0 := by
      intro a
      refine ih (fun i => (χ i a - χ j a) • v i) (fun i hi b => ?_) ?_
      · rw [map_smul, hv i (Finset.mem_insert_of_mem hi) b, smul_comm]
      · have h1 := congrArg (T a) hsum
        rw [map_add, map_sum, map_zero, hv j (Finset.mem_insert_self _ _)] at h1
        have h2 : v j = -∑ i ∈ s, v i := eq_neg_of_add_eq_zero_left hsum
        rw [Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi) a] at h1
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← Finset.smul_sum]
        have h3 : ∑ i ∈ s, χ i a • v i = -(χ j a • v j) := (neg_eq_of_add_eq_zero_right h1).symm
        rw [h3, h2, smul_neg, neg_neg, sub_self]
    have hs : ∀ i ∈ s, v i = 0 := by
      intro i hi
      have hne : χ i ≠ χ j := fun h => hj (hχ h ▸ hi)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      exact (smul_eq_zero.1 (key a i hi)).resolve_left (sub_ne_zero.2 ha)
    have hj0 : v j = 0 := by
      rw [Finset.sum_eq_zero hs, add_zero] at hsum; exact hsum
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hj0
    · exact hs i hi

open Classical in
open scoped BigOperators in
private theorem isHeis_apply_apply_eq_smul_of_fixes {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {a : X} (ha : a ∈ A) (x : X) :
    W a (W x e) = γ a x • W x e := by
  have hswap := hW.swap
  have hne := hW.ne_zero (w • x) a
  obtain ⟨-, hw, -, hadd, -, hsm, -, hmul⟩ := hW
  have h1 := hmul a x e
  have h2 := hmul x a e
  have hfix : W a e = e := he a ha
  rw [hfix] at h2
  have key : W (a + x) e = (γ (w • x) a)⁻¹ • W x e := by
    rw [h2, smul_smul, inv_mul_cancel₀ hne, one_smul, add_comm]
  rw [h1, key, smul_smul]
  congr 1
  rw [hsm w a x, hswap a (w • x), inv_inv, ← hadd, ← add_smul, add_comm (σ w) w, hw, one_smul]

open Classical in
open scoped BigOperators in
private theorem isHeis_sum_filter_quotient_eq_zero_of_sum_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) {ι : Type} (s : Finset ι) (c : ι → ℂ) (x : ι → X) (e : ι → M)
    (he : ∀ i, _root_.GlobalTheory.FinWeil.Fixes W A (e i)) (hsum : ∑ i ∈ s, c i • W (x i) (e i) = 0)
    (q : X ⧸ A.toAddSubgroup) :
    ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), c i • W (x i) (e i) = 0 := by
  classical
  let χ : X ⧸ A.toAddSubgroup → A → ℂ := fun q a => γ a (Quotient.out q)
  have hadd : ∀ x y z : X, γ x (y + z) = γ x y * γ x z := by
    obtain ⟨-, -, -, h, -⟩ := hW; exact h
  have hχ : Function.Injective χ := by
    intro q q' hqq
    have h1 : ∀ a ∈ A, γ a (Quotient.out q) = γ a (Quotient.out q') :=
      fun a ha => congrFun hqq ⟨a, ha⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    refine (hA _).2 fun a ha => ?_
    rw [hW.swap a, hadd, hW.neg_right, h1 a ha,
      inv_mul_cancel₀ (hW.ne_zero _ _), inv_one]
  have hval : ∀ (q' : X ⧸ A.toAddSubgroup) (y : X), (y : X ⧸ A.toAddSubgroup) = q' →
      ∀ a : A, γ a y = χ q' a := by
    intro q' y hy a
    have hz := QuotientAddGroup.out_eq' q'
    have hd : -(Quotient.out q') + y ∈ A.toAddSubgroup := QuotientAddGroup.eq.1 (hz.trans hy.symm)
    have hy' : y = Quotient.out q' + (-(Quotient.out q') + y) := by abel
    show γ a y = γ a (Quotient.out q')
    rw [hy', hadd, (hA a).1 a.2 _ hd, mul_one]
  have key := eq_zero_of_sum_eigenvectors_eq_zero_of_injective (fun a : A => W a) χ hχ (s.image fun i => (x i : X ⧸ A.toAddSubgroup))
    (fun q' => ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q'), c i • W (x i) (e i))
    (fun q' _ a => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, isHeis_apply_apply_eq_smul_of_fixes hW (he i) a.2, smul_comm,
        hval q' (x i) (Finset.mem_filter.1 hi).2 a])
    (by rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)]; exact hsum)
  by_cases hq : q ∈ s.image fun i => (x i : X ⧸ A.toAddSubgroup)
  · exact key q hq
  · refine Finset.sum_eq_zero fun i hi => absurd ?_ hq
    obtain ⟨his, hiq⟩ := Finset.mem_filter.1 hi
    rw [← hiq]
    exact Finset.mem_image_of_mem _ his

open Classical in
open scoped BigOperators in
private theorem eq_zero_of_isHeis_apply_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) (x : X) {v : M}
    (hv : W x v = 0) : v = 0 := by
  have hne := hW.ne_zero (w • -x) x
  obtain ⟨-, -, -, -, -, -, h0, hmul⟩ := hW
  have h := hmul (-x) x v
  rw [hv, map_zero, neg_add_cancel, h0] at h
  exact (smul_eq_zero.1 h.symm).resolve_left hne

open Classical in
open scoped BigOperators in
private theorem isHeis_apply_add_eq_inv_smul_of_fixes {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {d : X} (hd : d ∈ A) (x : X) :
    W (x + d) e = (γ (w • x) d)⁻¹ • W x e := by
  have hne := hW.ne_zero (w • x) d
  obtain ⟨-, -, -, -, -, -, -, hmul⟩ := hW
  have h := hmul x d e
  rw [he d hd] at h
  rw [h, smul_smul, inv_mul_cancel₀ hne, one_smul]

open Classical in
open scoped BigOperators in
private theorem isHeis_sum_map_eq_zero_of_sum_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (ρ : X →ₗ[R] X) (hρ : ∀ x y, γ (ρ x) (ρ y) = γ x y)
    (L : M →ₗ[ℂ] M) (hL : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W (A.map ρ) (L e))
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (x : ι → X) (e : ι → M)
    (he : ∀ i, _root_.GlobalTheory.FinWeil.Fixes W A (e i)) (hsum : ∑ i ∈ s, c i • W (x i) (e i) = 0) :
    ∑ i ∈ s, c i • W (ρ (x i)) (L (e i)) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => (x i : X ⧸ A.toAddSubgroup))
    (t := s.image fun i => (x i : X ⧸ A.toAddSubgroup))
    (fun i hi => Finset.mem_image_of_mem (fun i => (x i : X ⧸ A.toAddSubgroup)) hi)]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hfib := isHeis_sum_filter_quotient_eq_zero_of_sum_eq_zero hW hA s c x e he hsum q
  set x0 := Quotient.out q
  have hd : ∀ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), -x0 + x i ∈ A := by
    intro i hi
    have hz := QuotientAddGroup.out_eq' q
    exact QuotientAddGroup.eq.1 (hz.trans (Finset.mem_filter.1 hi).2.symm)
  have hxi : ∀ i, x i = x0 + (-x0 + x i) := fun i => by abel
  let u : M := ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
    (c i * (γ (w • x0) (-x0 + x i))⁻¹) • e i
  have hu : u = 0 := by
    apply eq_zero_of_isHeis_apply_eq_zero hW x0
    rw [← hfib, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul, mul_smul, ← isHeis_apply_add_eq_inv_smul_of_fixes hW (he i) (hd i hi), ← hxi]
  have hfixρ : ∀ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
      ρ (-x0 + x i) ∈ A.map ρ := fun i hi => Submodule.mem_map_of_mem (hd i hi)
  calc ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), c i • W (ρ (x i)) (L (e i))
      = ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
          W (ρ x0) ((c i * (γ (w • x0) (-x0 + x i))⁻¹) • L (e i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_smul, mul_smul]
        congr 1
        have h := isHeis_apply_add_eq_inv_smul_of_fixes hW (hL _ (he i)) (hfixρ i hi) (ρ x0)
        rw [← map_add, ← hxi, ← ρ.map_smul w x0, hρ] at h
        exact h
    _ = W (ρ x0) (L u) := by
        rw [map_sum, ← map_sum]
        congr 1
        simp only [u, map_sum, map_smul]
    _ = 0 := by rw [hu, map_zero, map_zero]

open Classical in
open scoped BigOperators in

theorem _root_.GlobalTheory.FinWeil.exists_weil_rep_of_vacua : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ A : Submodule R X,
    _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) →
    (∀ g, _root_.GlobalTheory.FinWeil.idx A (A.map (ρ g)) ≠ 0) →
    ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧
      ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) ∧
        ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e →
          Om g e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A hA hspan Γ _ ρ hρ hidx
  classical
  have hN : ∀ g, ∃ large₂ : M →ₗ[ℂ] M,
      (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e →
        large₂ e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e) ∧
      (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W (A.map (ρ g)) (large₂ e)) := by
    intro g
    have hB := _root_.GlobalTheory.FinWeil.selfDual_map_rep ρ (hρ) hA g
    obtain ⟨⟨n, f, hfB, hf⟩, hfix, -⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A (A.map (ρ g)) hB).2.1 (hidx g)
    refine ⟨(lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ g))))⁻¹ • ∑ i, W (f i), fun e he => ?_,
      fun e he => ?_⟩
    · have h1 := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ hB e he (Fin n) f hfB hf).1
      have h2 : _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e =
          (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ g))))⁻¹ •
            _root_.GlobalTheory.FinWeil.sumOp W A (A.map (ρ g)) e := rfl
      rw [h2, h1, LinearMap.smul_apply, LinearMap.sum_apply]
    · have h1 := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ hB e he (Fin n) f hfB hf).1
      have h3 := hfix e he
      intro b hb
      rw [LinearMap.smul_apply, LinearMap.sum_apply, ← h1, map_smul, h3 b hb]
  choose large₂ hLg hLfix using hN
  let F := {e : M // _root_.GlobalTheory.FinWeil.Fixes W A e}
  let src : ((X × F) →₀ ℂ) →ₗ[ℂ] M := Finsupp.linearCombination ℂ (fun p : X × F => W p.1 p.2.1)
  have hsurj : Function.Surjective src := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, ← hspan]
    congr 1
    ext m
    constructor
    · rintro ⟨⟨x, e⟩, rfl⟩; exact ⟨x, e.1, e.2, rfl⟩
    · rintro ⟨x, e, he, rfl⟩; exact ⟨(x, ⟨e, he⟩), rfl⟩
  let tgt : Γ → ((X × F) →₀ ℂ) →ₗ[ℂ] M := fun g =>
    Finsupp.linearCombination ℂ (fun p : X × F => W (ρ g p.1) (large₂ g p.2.1))
  have hker : ∀ g, LinearMap.ker src ≤ LinearMap.ker (tgt g) := by
    intro g f hf
    rw [LinearMap.mem_ker] at hf ⊢
    simp only [src, tgt, Finsupp.linearCombination_apply, Finsupp.sum] at hf ⊢
    exact isHeis_sum_map_eq_zero_of_sum_eq_zero hW hA (ρ g) (hρ g) (large₂ g) (hLfix g) f.support f
      Prod.fst (fun p => p.2.1) (fun p => p.2.2) hf
  let Om0 : Γ → M →ₗ[ℂ] M := fun g => ((LinearMap.ker src).liftQ (tgt g) (hker g)).comp
    (src.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hgen : ∀ g x e, _root_.GlobalTheory.FinWeil.Fixes W A e → Om0 g (W x e) = W (ρ g x) (large₂ g e) := by
    intro g x e he
    have hs : src (Finsupp.single (x, ⟨e, he⟩) 1) = W x e := by simp [src]
    have h1 : (src.quotKerEquivOfSurjective hsurj).symm (W x e) =
        Submodule.Quotient.mk (Finsupp.single (x, ⟨e, he⟩) 1) := by
      rw [LinearEquiv.symm_apply_eq, ← hs]; rfl
    simp only [Om0, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    simp [tgt]
  have hext : ∀ T T' : M →ₗ[ℂ] M,
      (∀ x e, _root_.GlobalTheory.FinWeil.Fixes W A e → T (W x e) = T' (W x e)) → T = T' := by
    intro T T' h
    apply LinearMap.ext_on hspan
    rintro m ⟨x, e, he, rfl⟩
    exact h x e he
  have hmul : ∀ (x y : X) (v : M), W x (W y v) = γ (w • x) y • W (x + y) v := by
    obtain ⟨-, -, -, -, -, -, -, h⟩ := hW; exact h
  have hW0 : ∀ v, W 0 v = v := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hW; exact h
  have hB : ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) :=
    fun g => _root_.GlobalTheory.FinWeil.selfDual_map_rep ρ hρ hA g
  have hinter : ∀ g x, (Om0 g).comp (W x) = (W (ρ g x)).comp (Om0 g) := by
    intro g x
    refine hext _ _ fun y e he => ?_
    simp only [LinearMap.comp_apply]
    rw [hmul, map_smul, hgen _ _ _ he, hgen _ _ _ he, hmul, map_add, ← (ρ g).map_smul, hρ]
  have hmapmul : ∀ g h, A.map (ρ (g * h)) = (A.map (ρ h)).map (ρ g) := by
    intro g h; rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  let Om : Γ →* Module.End ℂ M :=
    { toFun := Om0
      map_one' := by
        refine hext _ _ fun x e he => ?_
        have hA1 : A.map (ρ 1) = A := by rw [map_one, Module.End.one_eq_id, Submodule.map_id]
        rw [hgen _ _ _ he, hLg 1 e he]
        have h2 : _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ 1)) e =
            (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ 1))))⁻¹ •
              _root_.GlobalTheory.FinWeil.sumOp W A (A.map (ρ 1)) e := rfl
        obtain ⟨hi1, hs1⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A A hA).2.2 le_rfl
        rw [h2, hA1, hi1, hs1 e he, map_one lam, inv_one, one_smul, map_one ρ]
        rfl
      map_mul' := by
        intro g h
        refine hext _ _ fun x e he => ?_
        rw [hgen _ _ _ he, Module.End.mul_apply, hgen _ _ _ he]
        obtain ⟨⟨n, f, hfB, hf⟩, -, -⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A (A.map (ρ h)) (hB h)).2.1 (hidx h)
        obtain ⟨hsum1, hcard1⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ (hB h) e he (Fin n) f hfB hf
        have hLh : large₂ h e = (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ h))))⁻¹ • ∑ i, W (f i) e := by
          rw [hLg h e he, ← hsum1]; rfl
        have hv := hLfix g e he
        have hfB' : ∀ i, ρ g (f i) ∈ A.map (ρ (g * h)) := by
          intro i; rw [hmapmul]; exact Submodule.mem_map_of_mem (hfB i)
        have hf' : ∀ b ∈ A.map (ρ (g * h)), ∃! i, b - ρ g (f i) ∈ A.map (ρ g) := by
          intro b hb
          rw [hmapmul] at hb
          obtain ⟨b', hb', rfl⟩ := Submodule.mem_map.1 hb
          obtain ⟨i, hi, huniq⟩ := hf b' hb'
          refine ⟨i, ?_, fun j hj => huniq j ?_⟩
          · show (ρ g) b' - (ρ g) (f i) ∈ A.map (ρ g)
            rw [← map_sub]; exact Submodule.mem_map_of_mem hi
          · have hj' : (ρ g) b' - (ρ g) (f j) ∈ A.map (ρ g) := hj
            rw [← map_sub, _root_.GlobalTheory.FinWeil.mem_map_rep, _root_.GlobalTheory.FinWeil.rep_inv_apply] at hj'
            exact hj'
        obtain ⟨hsum2, hcard2⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW (A.map (ρ g)) (A.map (ρ (g * h)))
          (hB (g * h)) _ hv (Fin n) (fun i => ρ g (f i)) hfB' hf'
        have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A (A.map (ρ g))
          (A.map (ρ (g * h))) hA (hB g) (hB (g * h)) (hidx g) (hidx (g * h)) e he
        have h3 : _root_.GlobalTheory.FinWeil.normOp lam W (A.map (ρ g)) (A.map (ρ (g * h))) (large₂ g e) =
            (lam (_root_.GlobalTheory.FinWeil.idx (A.map (ρ g)) (A.map (ρ (g * h)))))⁻¹ •
              _root_.GlobalTheory.FinWeil.sumOp W (A.map (ρ g)) (A.map (ρ (g * h))) (large₂ g e) := rfl
        rw [hLg (g * h) e he, ← hcomp, ← hLg g e he, h3, hsum2, hcard2, ← hcard1, hLh]
        simp only [map_smul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmul (ρ h x) (f i) e, map_smul, hgen _ _ _ he, hmul, map_mul, Module.End.mul_apply,
          map_add, ← (ρ g).map_smul, hρ] }
  refine ⟨Om, fun g x v => ?_, fun g => ⟨hB g, fun e he => ?_⟩⟩
  · exact LinearMap.congr_fun (hinter g x) v
  · show Om0 g e = _
    have := hgen g 0 e he
    rw [hW0, map_zero, hW0] at this
    rw [this, hLg g e he]

end GlobalTheory.FinWeil
end

open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_representation_of_lattice_vacua : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ ∀ e, Fixes W A e → Om g e = normOp lam W A (A.map (ρ g)) e := by
  atlas_forward_decl GlobalTheory.FinWeil.exists_weil_rep_of_vacua
end

section
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma lam_idx_sq_eq_idx_of_fixed_ne_zero (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (lam : ℕ →* ℂ) (hlam : _root_.GlobalTheory.FinWeil.GoodNorm σ lam) {A A' : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (hA' : _root_.GlobalTheory.FinWeil.SelfDual γ A')
    (hidx : _root_.GlobalTheory.FinWeil.idx A A' ≠ 0) {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he0 : e ≠ 0) :
    lam (_root_.GlobalTheory.FinWeil.idx A A') ^ 2 = _root_.GlobalTheory.FinWeil.idx A A' := by
  have hAA := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A)
    (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)
  have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx
    (by rw [hAA.2]; simp) e he
  obtain ⟨hsym, hback⟩ := _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx
  have hlin : ∀ (c : ℂ) (v : M),
      _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v := by
    intro c v
    unfold _root_.GlobalTheory.FinWeil.sumOp
    simp only [map_smul]
    rw [smul_finsum]
  unfold _root_.GlobalTheory.FinWeil.normOp at hcomp
  rw [hAA.1, hAA.2, hsym, hlin, hback e he] at hcomp
  simp only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton, hW.zero, smul_smul] at hcomp
  have hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0 := hlam.1 _ hidx
  have hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ *
      (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_assoc, hcomp, sub_self]
  have h1 := (smul_eq_zero.1 hz).resolve_right he0
  field_simp at h1
  linear_combination -h1

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma mul_conj_eq_natCast_of_sq_eq (c : ℂ) (n : ℕ) (h : c ^ 2 = n) :
    c * starRingEnd ℂ c = n := by
  have hn : ‖c‖ ^ 2 = n := by rw [← norm_pow, h, Complex.norm_natCast]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  push_cast
  rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_vacuum_eq_zero
    (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x u v, B (W x u) (W x v) = B u v) {e e' : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he' : _root_.GlobalTheory.FinWeil.Fixes W A e') {z : X} (hz : z ∉ A) : B (W z e) e' = 0 := by
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hz ((hA z).2 h)
  have haz : γ a z ≠ 1 := fun h => hza (hW.swap_eq_one h)
  have key := hB a (W z e) e'
  rw [hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  have : (γ a z - 1) * B (W z e) e' = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_pair_eq (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hB : ∀ x u v, B (W x u) (W x v) = B u v) (x y : X) (e e' : M) :
    B (W x e) (W y e') = γ (w • -y) x * (starRingEnd ℂ) (γ (w • -y) y) * B (W (-y + x) e) e' := by
  rw [← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]
  simp
  ring

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForms_eq_of_eq_on_vacua (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤)
    (B₁ B₂ : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (h₁ : ∀ x u v, B₁ (W x u) (W x v) = B₁ u v)
    (h₂ : ∀ x u v, B₂ (W x u) (W x v) = B₂ u v)
    (hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ e e' = B₂ e e')
    (u v : M) : B₁ u v = B₂ u v := by
  have htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ (W z e) e' = B₂ (W z e) e' := by
    intro z e e' he he'
    by_cases hz : z ∈ A
    · rw [he z hz]
      exact hvac e e' he he'
    · rw [invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz,
        invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]
  have hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e},
      ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t := by
    rintro s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩
    rw [invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂,
      htr _ e e' he he']
  have hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s :=
    fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)
  have hflip : B₁.flip v = B₂.flip v :=
    LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])
  simpa using LinearMap.congr_fun hflip u

open Classical in
open scoped BigOperators in

theorem _root_.GlobalTheory.FinWeil.invForm_intertwiner : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam →
    ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → _root_.GlobalTheory.FinWeil.SelfDual γ (A.map φ) →
    _root_.GlobalTheory.FinWeil.idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) →
    (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map φ) e) →
    ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) →
    ∀ u v, B (T u) (T v) = B u v := by
  intro R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v
  obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx
  have hsum := fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu
  have hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B (T e) (T e') = B e e' := by
    intro e e' he he'
    by_cases he0 : e = 0
    · subst he0
      simp
    have hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n := by simpa using (hsum e he).2
    have hc2 := lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0
    rw [hn] at hc2
    have hcn := mul_conj_eq_natCast_of_sq_eq _ _ hc2
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hn ▸ hidx)
    have hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e := by
      intro e he
      rw [hTe e he]
      unfold _root_.GlobalTheory.FinWeil.normOp
      rw [hn, (hsum e he).1]
    have hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0 := by
      intro i j
      rw [← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i),
        hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel,
        hW.zero]
      split_ifs with hij
      · subst hij
        rw [neg_add_cancel, hW.zero]
      · apply invariantForm_translate_vacuum_eq_zero hW hA B hB he he'
        intro hmem
        apply hij
        obtain ⟨k, -, hk⟩ := hfu (f i) (hfB i)
        rw [hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]
    rw [hT' e he, hT' e' he']
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply,
      smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]
    have hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1 := by
      rw [← mul_inv, hcn, inv_mul_cancel₀ hn0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination B e e' * hinv
  have key := invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B
    (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v
  simpa using key

end GlobalTheory.FinWeil
end

open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by
  atlas_forward_decl GlobalTheory.FinWeil.invForm_intertwiner
end

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem invariantForm_translate_eq_zero (h : IsHeis σ w γ W) {P Q : X →ₗ[R] X} (hPP : ∀ x, P (P x) = P x)
    (hadj : ∀ x y, γ (P x) y = γ x (Q y)) {C : Submodule R X} (hC : SelfDual γ C) (hQC : ∀ a ∈ C, Q a ∈ C)
    (ℓ : M →ₗ[ℂ] ℂ) (hl : ∀ u m, ℓ (W (Q u) m) = ℓ m) {e : M} (he : Fixes W C e) {z : X} (hz : P z ∉ C) :
    ℓ (W (P z) e) = 0 := by
  have hex : ¬ ∀ a ∈ C, γ (P z) a = 1 := fun H => hz ((hC (P z)).2 H)
  push Not at hex
  obtain ⟨a, ha, hne⟩ := hex
  have hQa : W (Q a) e = e := he _ (hQC a ha)
  have hg : γ (P z) (Q a) = γ (P z) a := by rw [← hadj, hPP]
  have hc : W (Q a) (W (P z) e) = γ (Q a) (P z) • W (P z) e := by rw [h.comm, hQa]
  have key := hl a (W (P z) e)
  rw [hc, map_smul, smul_eq_mul] at key
  have hs : γ (Q a) (P z) ≠ 1 := by
    rw [h.swap, hg]
    intro h1
    exact hne (inv_eq_one.1 h1)
  by_contra h0
  exact hs (mul_right_cancel₀ h0 (key.trans (one_mul _).symm))

end

theorem invariantForm_normOp_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  intro R X M _ _ _ _ _ σ w γ W h lam A hA hspan φ hφ hφA hidx T hT hTe P Q hPP hQQ hPQ hQP hadj hPA hQA hφP hφQ hφr
  have hQadj : ∀ u v, γ (Q u) v = γ u (P v) := fun u v => by
    rw [h.swap, ← hadj, ← h.swap]
  have hPr : ∀ u y, γ (P u) (y - P y - Q y) = 1 := fun u y => by
    rw [hadj, map_sub, map_sub, hQP, hQQ, sub_zero, sub_self, h.zero_right]
  have hQr : ∀ u y, γ (Q u) (y - P y - Q y) = 1 := fun u y => by
    rw [hQadj, map_sub, map_sub, hPP, hPQ, sub_self, sub_zero, h.zero_right]
  have hrP : ∀ u y, γ (y - P y - Q y) (P u) = 1 := fun u y => by
    rw [h.swap, hPr, inv_one]
  have hsm : ∀ y : X, w • (y - P y - Q y) = w • y - P (w • y) - Q (w • y) := fun y => by
    simp only [smul_sub, map_smul]

  have hsplit : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ (y : X) (v : M),
      γ (w • Q y) (y - Q y) * ℓ (W y v) = ℓ (W (y - P y - Q y) (W (P y) v)) := by
    intro ℓ hl y v
    have e1 := hl y (W (y - Q y) v)
    rw [h.comp, show Q y + (y - Q y) = y by abel, map_smul, smul_eq_mul] at e1
    rw [e1, h.comp, hsm, hrP, one_smul, show y - P y - Q y + P y = y - Q y by abel]
  have hinvρ : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ y : X,
      ∀ u m, (ℓ.comp (W (y - P y - Q y))) (W (Q u) m) = (ℓ.comp (W (y - P y - Q y))) m := by
    intro ℓ hl y u m
    simp only [LinearMap.comp_apply]
    rw [h.comm, map_smul, smul_eq_mul, h.swap, hQr, inv_one, one_mul, hl]
  have hinvT : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) →
      ∀ u m, (ℓ.comp T) (W (Q u) m) = (ℓ.comp T) m := by
    intro ℓ hl u m
    simp only [LinearMap.comp_apply]
    rw [hT, hφQ, hl]

  have hterm : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ∀ b ∈ A.map φ, ℓ (W b e) = ℓ (W (P b) e) := by
    intro ℓ hl e he b hb
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hb
    have hQb : Q (φ a) ∈ A.map φ := by
      rw [← hφQ]; exact Submodule.mem_map_of_mem (hQA a ha)
    have hd : φ a - Q (φ a) ∈ A.map φ := Submodule.sub_mem _ hb hQb
    have hr : φ a - P (φ a) - Q (φ a) ∈ A := by
      rw [hφr]; exact Submodule.sub_mem _ (Submodule.sub_mem _ ha (hPA a ha)) (hQA a ha)
    have h1 : W (Q (φ a)) (W (φ a - Q (φ a)) e) = W (φ a) e := by
      rw [h.comp, h.iso hφA (Submodule.smul_mem _ w hQb) hd, one_smul,
        show Q (φ a) + (φ a - Q (φ a)) = φ a by abel]
    have h2 : W (P (φ a)) (W (φ a - P (φ a) - Q (φ a)) e) = W (φ a - Q (φ a)) e := by
      rw [h.comp, ← map_smul P w (φ a), hPr, one_smul,
        show P (φ a) + (φ a - P (φ a) - Q (φ a)) = φ a - Q (φ a) by abel]
    rw [← h1, hl, ← h2, he _ hr]
  obtain ⟨k, f, hf, ht⟩ := exists_transversal_of_idx_ne_zero A (A.map φ) hidx

  have hE : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ℓ (T e) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ e := by
    intro ℓ hl e he
    rw [hTe e he]
    unfold normOp
    rw [(sumOp_eq_sum_transversal h A (A.map φ) hφA e he (Fin k) f hf ht).1, map_smul, map_sum,
      smul_eq_mul, mul_assoc]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm ℓ hl e he (f i) (hf i)]
    by_cases hm : P (f i) ∈ A
    · simp [hm, he _ hm]
    · rw [invariantForm_translate_eq_zero h hPP hadj hA hQA ℓ hl he hm]
      simp [hm]

  have hmain : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ x e, Fixes W A e →
      ℓ (T (W x e)) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ (W x e) := by
    intro ℓ hl x e he
    have hs0 := h.ne_zero (w • Q x) (x - Q x)
    have hA1 := hsplit ℓ hl x e
    have hB1 := hsplit ℓ hl (φ x) (T e)
    rw [hφr, ← hφQ, ← hφP, ← map_smul φ w (Q x), ← map_sub φ x (Q x), hφ, ← hT, ← hT] at hB1
    by_cases hp : P x ∈ A
    · rw [he _ hp] at hA1 hB1
      have h3 := hE (ℓ.comp (W (x - P x - Q x))) (hinvρ ℓ hl x) e he
      simp only [LinearMap.comp_apply] at h3
      rw [h3, ← hA1] at hB1
      apply mul_left_cancel₀ hs0
      rw [hB1]
      ring
    · have z1 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvρ ℓ hl x) he hp
      have z2 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvT _ (hinvρ ℓ hl x)) he hp
      simp only [LinearMap.comp_apply] at z1 z2
      rw [z1] at hA1
      rw [z2] at hB1
      rw [(mul_eq_zero.1 hA1).resolve_left hs0, (mul_eq_zero.1 hB1).resolve_left hs0, mul_zero]
  refine ⟨(Finset.univ.filter (fun i => P (f i) ∈ A)).card, ?_, ?_⟩
  · obtain ⟨i, hi, -⟩ := ht 0 (Submodule.zero_mem _)
    refine Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hPA _ ?_⟩⟩
    simpa using A.neg_mem hi
  · intro ℓ hl m
    have hle : (⊤ : Submodule ℂ M) ≤ LinearMap.ker (ℓ.comp T - ((lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ)) • ℓ) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, e, he, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hmain ℓ hl x e he, sub_self]
    have hm := hle (Submodule.mem_top (x := m))
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul] at hm
    exact sub_eq_zero.1 hm

end GlobalTheory.FinWeil
end

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  atlas_forward_decl GlobalTheory.FinWeil.invariantForm_normOp_eq
end

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem intertwiner_fixes_of_local_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (hTe : ∀ e, Fixes W A e → T e = e) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ x, φ (x - P x) = x - P x)
    (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : T m = m := by
  have hsm : ∀ (c : ℂ) e, Fixes W A e → Fixes W A (c • e) := fun c e he a ha => by rw [map_smul, he a ha]
  have key : ∀ {ι : Type} (x : ι → X) (s : Finset ι) (e : ι → M), (∀ i, Fixes W A (e i)) →
      (∀ a ∈ A, W (P a) (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i)) →
      T (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i) := by
    intro ι x s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro e he hfix
      by_cases hall : ∀ i ∈ s, P (x i) ∈ A
      · rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 := h.comp (x i - P (x i)) (P (x i)) (e i)
        rw [he i _ (hall i hi), sub_add_cancel] at h1
        have h2 : T (W (x i - P (x i)) (e i)) = W (x i - P (x i)) (e i) := by rw [hT, hφ, hTe _ (he i)]
        rw [h1, map_smul] at h2
        exact smul_right_injective M (h.ne_zero _ _) h2
      · push Not at hall
        obtain ⟨j, hj, hjA⟩ := hall
        rw [hA] at hjA
        push Not at hjA
        obtain ⟨a, ha, hz⟩ := hjA
        have hz' : γ (P a) (x j) ≠ 1 := by
          intro h0
          rw [hP] at h0
          exact hz (h.swap_eq_one h0)
        set z := γ (P a) (x j) with hzdef
        have hact : ∀ i, W (P a) (W (x i) (e i)) = γ (P a) (x i) • W (x i) (e i) := fun i => by
          rw [h.comm, he i _ (hPA a ha)]
        have hsum : (1 - z) • ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s.erase j, W (x i) ((γ (P a) (x i) - z) • e i) := by
          rw [Finset.sum_erase s (by simp [hzdef]), sub_smul, one_smul]
          have h4 : ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) := by
            rw [← hfix a ha, map_sum]
            exact Finset.sum_congr rfl fun i _ => hact i
          calc _ = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) - ∑ i ∈ s, z • W (x i) (e i) := by
                rw [← h4, Finset.smul_sum]
            _ = _ := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sub_smul]
        have h3 := ih (s.erase j) (Finset.erase_ssubset hj) (fun i => (γ (P a) (x i) - z) • e i)
          (fun i => hsm _ _ (he i)) (fun b hb => by rw [← hsum, map_smul, hfix b hb])
        rw [← hsum, map_smul] at h3
        exact smul_right_injective M (sub_ne_zero.2 hz'.symm) h3
  have hmem : m ∈ Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} := by rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  choose x e he hge using fun i => (g i).2
  have hm' : m = ∑ i, W (x i) (c i • e i) := by
    rw [← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hge i]
  rw [hm'] at hm ⊢
  exact key x Finset.univ _ (fun i => hsm _ _ (he i)) hm

end GlobalTheory.FinWeil
end

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_fixes_of_local_vacuum' : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M), (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = e) → ∀ P : X →ₗ[R] X, (∀ x y, γ (P x) y = γ x (P y)) → (∀ a ∈ A, P a ∈ A) → (∀ x, φ (x - P x) = x - P x) → ∀ m : M, (∀ a ∈ A, W (P a) m = m) → T m = m := by
  atlas_forward_decl GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIdem

open GlobalTheory.SplitIdem

section Local

variable (F : Type) [Field F] [NumberField F]

theorem sqrt_mem (d : ℕ) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (hy : y * y = -(d : Fv F v)) :
    y ∈ v.adicCompletionIntegers F := by
  have h : y * y ∈ v.adicCompletionIntegers F := by
    rw [hy]; exact neg_mem (natCast_mem _ d)
  rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers F) y with h1 | h1
  · exact h1
  · by_cases h0 : y = 0
    · rw [h0]; exact zero_mem _
    · have := mul_mem h h1
      rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

theorem exists_sqrt_adele (d : ℕ) : ∃ s ι : Af F, ∀ v,
    (evalV F v ι = 1 ∧ evalV F v s * evalV F v s = -(d : Fv F v)) ∨
    (evalV F v ι = 0 ∧ evalV F v s = 0 ∧ ∀ y : Fv F v, y * y ≠ -(d : Fv F v)) := by
  classical
  refine ⟨⟨fun v => if h : ∃ y : Fv F v, y * y = -(d : Fv F v) then h.choose else 0,
      Filter.Eventually.of_forall fun v => ?_⟩,
    ⟨fun v => if ∃ y : Fv F v, y * y = -(d : Fv F v) then 1 else 0,
      Filter.Eventually.of_forall fun v => ?_⟩, fun v => ?_⟩
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · simp only [h, dif_pos]; exact sqrt_mem F d v _ h.choose_spec
    · simp only [h, dif_neg, not_false_iff]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = -(d : Fv F v)
    · left
      refine ⟨if_pos h, ?_⟩
      have e : ∀ x : Fv F v, x = h.choose → x * x = -(d : Fv F v) := fun x hx => hx ▸ h.choose_spec
      exact e _ (dif_pos h)
    · right
      exact ⟨if_neg h, dif_neg h, fun y hy => h ⟨y, hy⟩⟩

theorem pair_mul (α β : Af F) : pairA F 0 α * pairA F 0 β = pairA F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

theorem pair_mul' (α : Af F) (b : AF F) : pairA F 0 α * b = pairA F 0 (α * sndA F b) :=
  Prod.ext (zero_mul _) rfl

theorem pair_neg (α : Af F) : -pairA F 0 α = pairA F 0 (-α) :=
  Prod.ext neg_zero rfl

theorem place_ext {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h0 : ∀ v', v' ≠ v → evalV F v' α = 0)
    {x y : Af F} (h : evalV F v x = evalV F v y) : α * x = α * y := by
  refine af_ext F fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, map_mul, h]
  · rw [map_mul, map_mul, h0 w hw, zero_mul, zero_mul]

end Local

theorem star_delta (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  rw [star_eq_conj, D.host.conj_sqrtMinusD]

theorem d_ne_zero (D : D7) : D.host.d ≠ 0 := D.host.hyp.2.1.pos.ne'

theorem tensor_decomp {F A E : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E] (δ : E)
    (h : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • δ) (z : A ⊗[F] E) :
    ∃ a b : A, z = algebraMap A (A ⊗[F] E) a + algebraMap A (A ⊗[F] E) b * ((1 : A) ⊗ₜ[F] δ) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨u, w, rfl⟩ := h x
    refine ⟨u • a, w • a, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩

theorem tensor_inj {F A E : Type} [Field F] [CommRing A] [Algebra F A] [Field E] [Algebra F E] :
    Function.Injective (algebraMap A (A ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := A) (B := E) (algebraMap F E).injective

theorem tensor_sq {F A E : Type} [Field F] [CommRing A] [Algebra F A] [Field E] [Algebra F E] (δ : E) (n : ℕ)
    (h : δ ^ 2 = -(n : E)) : ((1 : A) ⊗ₜ[F] δ) * ((1 : A) ⊗ₜ[F] δ) = -(n : A ⊗[F] E) := by
  have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E) h
  rw [pow_two, map_mul, map_neg, map_natCast] at h
  exact h

theorem field_decomp (D : D7) (x : D.host.E) :
    ∃ u w : D.host.F, x = u • (1 : D.host.E) + w • D.host.sqrtMinusD := by
  have hδ : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have := D.host.sqrtMinusD_sq
    rw [h] at this
    apply d_ne_zero D
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination this
    exact_mod_cast h2
  have h2 : star (2 : D.host.E) = 2 := star_ofNat 2
  obtain ⟨u, hu⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    change star _ = _
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨w, hw⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    change star _ = _
    rw [star_div₀, star_sub, star_star, star_mul', h2, star_delta]
    field_simp
    ring)
  refine ⟨u, w, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, hu, hw]
  field_simp
  ring

theorem exists_half_abstract {F T T' : Type} [Field F] [NumberField F] [CommRing T] [CommRing T']
    (j : AF F →+* T) (c : T →+* T) (p : T →+* T') (δ : T) (n : ℕ) (hn0 : n ≠ 0) (hinj : Function.Injective j)
    (hcj : ∀ a, c (j a) = j a) (hcδ : c δ = -δ) (hδ2 : δ * δ = -(n : T))
    (hdec : ∀ z, ∃ a b, z = j a + j b * δ) (hinf : ∀ α, p (j (pairA F 0 α)) = 0) :
    ∃ ε : T, ε * ε = ε ∧ ε * c ε = 0 ∧ p ε = 0 ∧
      (∀ e, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, (∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧
          ∀ v', v' ≠ v → evalV F v' α = 0) ∧ e + c e = j η) →
        (ε * e = e ∧ ε * c e = 0) ∨ (ε * e = 0 ∧ ε * c e = c e)) ∧
      ∀ v η, ((∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧ ∀ v', v' ≠ v → evalV F v' α = 0) ∧
        ¬ ∃ e : T, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, (∃ α : Af F, η = pairA F 0 α ∧ evalV F v α = 1 ∧
          ∀ v', v' ≠ v → evalV F v' α = 0) ∧ e + c e = j η) ∧ e + c e = j η) → j η * ε = 0 := by
  obtain ⟨s, ι, hsι⟩ := exists_sqrt_adele F n
  obtain ⟨h, hh⟩ : ∃ h : AF F, h * (2 * n) = 1 := by
    have hd : (2 * n : F) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hn0)
    have := congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_natCast, map_ofNat, map_one] at this
    exact ⟨_, this⟩
  have hH : j h * (2 * n) = 1 := by
    have := congrArg j hh
    rwa [map_mul, map_mul, map_natCast, map_ofNat, map_one] at this
  have hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h <;> simp [h.1]
  have hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h
    · simp [h.1]
    · simp [h.2.1]
  have hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = -(j (pairA _ 0 ι) * n) := by
    rw [← map_natCast j, ← map_mul, ← map_mul, ← map_neg, pair_mul, pair_mul', pair_neg]
    congr 2
    refine af_ext _ fun w => ?_
    rw [map_mul, map_neg, map_mul, map_natCast, map_natCast]
    rcases hsι w with h | h
    · rw [h.1, h.2, one_mul]
    · simp [h.2.1, h.1]
  obtain ⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * n - j (pairA _ 0 s) * δ) := ⟨_, rfl⟩
  have hcε : c ε = j h * (j (pairA _ 0 ι) * n + j (pairA _ 0 s) * δ) := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]; ring
  have hinfε : p ε = 0 := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]; simp
  generalize hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε
  generalize hS : j (pairA _ 0 s) = S at hIS hSS hε hcε
  generalize hd : (n : T) = d at hH hSS hε hcε hδ2
  generalize hHH : j h = H at hH hε hcε
  have h2 : ε * c ε = 0 := by
    rw [hcε, hε]
    linear_combination H * H * d * d * hII - H * H * δ * δ * hSS + H * H * I * d * hδ2
  have h3 : ε + c ε = I := by
    rw [hcε, hε]
    linear_combination I * hH
  have h4 : I * ε = ε := by
    rw [hε]
    linear_combination H * d * hII - H * δ * hIS
  have h1 : ε * ε = ε := by
    linear_combination ε * h3 - h2 + h4
  refine ⟨ε, h1, h2, hinfε, ?_, ?_⟩
  · rintro e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩
    obtain ⟨a, b, hab⟩ := hdec e
    have hce : c e = j a - j b * δ := by
      rw [hab, map_add, map_mul, hcj, hcj, hcδ]; ring
    have he4 : c e * c e = c e := by rw [← map_mul, he1]
    obtain ⟨B, hB⟩ : ∃ B : AF F, B = 2 * n * b := ⟨_, rfl⟩
    have hjB : j B = -δ * (e - c e) := by
      rw [hB, map_mul, map_mul, map_ofNat, map_natCast, hd, hce]
      linear_combination 2 * j b * hδ2 + δ * hab
    have hB1 : pairA _ 0 α * B = B := hinj (by
      rw [map_mul, ← he3, hjB]
      linear_combination -δ * he1 + δ * he4)
    have hB2 : B * B = -(pairA _ 0 α * n) := hinj (by
      rw [map_mul, map_neg, map_mul, map_natCast, hd, ← he3, hjB]
      linear_combination δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)
    have hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = -(n : Fv F v) := by
      rw [← map_mul, ← map_mul, hB2, map_neg, map_neg, map_mul, map_mul, map_natCast, map_natCast]
      change -(evalV _ v α * _) = _
      rw [hα1, one_mul]
    rcases hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩
    swap
    · exact absurd hB3 (hn _)
    have hNI : (e + c e) * I = e + c e := by
      rw [he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
    have hcc : c (c ε) = ε := by
      rw [hcε, hε, ← hHH, ← hI, ← hS, ← hd, map_mul, map_add, map_mul, map_mul, hcj, hcj, hcj, hcδ, map_natCast]; ring
    rcases mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp
    · right
      have : j B = (e + c e) * S := by
        rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]
      have h5 : c e = (e + c e) * ε := by
        rw [hε]
        linear_combination -(c e) * hH - H * d * hNI - H * δ * this + H * δ * hjB - H * (e - c e) * hδ2
      constructor
      · linear_combination -e * h5 + (1 - ε) * he2 - ε * he1
      · linear_combination -(c e) * h5 + (1 - ε) * he4 - ε * he2
    · left
      have : j B = -((e + c e) * S) := by
        rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg,
          place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]
      have h5 : e = (e + c e) * ε := by
        rw [hε]
        linear_combination -e * hH - H * d * hNI + H * δ * this - H * δ * hjB + H * (e - c e) * hδ2
      constructor
      · linear_combination -e * h5 + (1 - ε) * he1 - ε * he2
      · linear_combination -(c e) * h5 + (1 - ε) * he2 - ε * he4
  · rintro v η ⟨⟨α, rfl, hα1, hα0⟩, hn⟩
    rcases hsι v with ⟨hι, -⟩ | ⟨hι, -, -⟩
    · exfalso
      have hNI : j (pairA _ 0 α) * I = j (pairA _ 0 α) := by
        rw [← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
      have hNN : j (pairA _ 0 α) * j (pairA _ 0 α) = j (pairA _ 0 α) := by
        rw [← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hα1, map_one]), mul_one]
      have hsum : j (pairA _ 0 α) * ε + c (j (pairA _ 0 α) * ε) = j (pairA _ 0 α) := by
        rw [map_mul, hcj, ← mul_add, h3, hNI]
      refine hn ⟨j (pairA _ 0 α) * ε, ⟨?_, ?_, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩, hsum⟩
      · rw [mul_mul_mul_comm, hNN, h1]
      · rw [map_mul, hcj, mul_mul_mul_comm, h2, mul_zero]
    · have hNI : j (pairA _ 0 α) * I = 0 := by
        rw [← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 0) (by rw [hι, map_zero]), mul_zero]
        exact map_zero j
      rw [← h4, ← mul_assoc, hNI, zero_mul]

theorem exists_half_idem : ∀ D : D7, ∃ ε : AE D, ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0 := by
  intro D
  have hcA : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := fun _ _ => rfl
  exact exists_half_abstract (algebraMap (AF D.host.F) (AE D)) (cA D) (infPart D)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.sqrtMinusD) D.host.d (d_ne_zero D) tensor_inj
    (fun a => (hcA a 1).trans (congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_one _)))
    ((hcA 1 _).trans ((congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) (star_delta D)).trans
      (TensorProduct.tmul_neg _ _)))
    (tensor_sq _ _ D.host.sqrtMinusD_sq) (tensor_decomp _ (field_decomp D))
    (fun _ => TensorProduct.zero_tmul (Ainf D.host.F) (1 : D.host.E))

end GlobalTheory.HalfIdem

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent : ∀ D : D7, ∃ ε : AE D, ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0 := by
  atlas_forward_decl GlobalTheory.HalfIdem.exists_half_idem
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  first | exact @GlobalTheory.SplitDetCharacter.exists_character | exact GlobalTheory.SplitDetCharacter.exists_character | (intros; apply GlobalTheory.SplitDetCharacter.exists_character <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  first | exact @GlobalTheory.LatNhds.eventually_actO | exact GlobalTheory.LatNhds.eventually_actO | (intros; apply GlobalTheory.LatNhds.eventually_actO <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  first | exact @GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | exact GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | (intros; apply GlobalTheory.ThetaMeanSquareForm.exists_invariant_form <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  first | exact @GlobalTheory.SplitIndex.not_dvd_relIndex | exact GlobalTheory.SplitIndex.not_dvd_relIndex | (intros; apply GlobalTheory.SplitIndex.not_dvd_relIndex <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_unitaryPairAction : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  first | exact @GlobalTheory.SymplOInv.symplO_actO | exact GlobalTheory.SymplOInv.symplO_actO | (intros; apply GlobalTheory.SymplOInv.symplO_actO <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem gamF_rhoF (p : GA D S × GA D T) (x y : XF S T) :
    gamF ψ S T (rhoF S T p x) (rhoF S T p y) = gamF ψ S T x y := by
  rw [gamF, gamF, coe_rhoF, coe_rhoF, GlobalTheory.T.symplecticForm_unitaryPairAction]

theorem phase_rhoF (w : 𝓞 D.host.E) (p : GA D S × GA D T) (x : XF S T) :
    phase ψ w (rhoF S T p x) = phase ψ w x := by
  rw [phase, phase, coe_rhoF, ← actO_smul, symplOH, symplOH, GlobalTheory.T.symplecticForm_unitaryPairAction]

structure IsLatRep (hψ : IsCharAF D.host.F ψ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (lam : ℕ →* ℂ)
    (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)) : Prop where
  hw : w + sgO D w = 1
  sd : SelfDual (gamF ψ S T) (latF S T ΛS ΛT)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e ∧ m = opF hψ S T w x e} = ⊤
  fin : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0
  op : ∀ p x v, Om p (opF hψ S T w x v) = opF hψ S T w (rhoF S T p x) (Om p v)
  sd' : ∀ p, SelfDual (gamF ψ S T) ((latF S T ΛS ΛT).map (rhoF S T p))
  vac : ∀ p e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e →
    Om p e = normOp lam (opF hψ S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) e

theorem exists_isLatRep (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {lam : ℕ →* ℂ}
    (hlam : GoodNorm (sgO D) lam) : ∃ w Om, IsLatRep hψ.1 ΛS ΛT w lam Om := by
  obtain ⟨w, hw⟩ := exists_w D
  have H := isHeis_opF hψ.1 S T hw
  have hA := selfDual_latF (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨hlev, hmov⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT)
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (smooth_theta hψ.1 hS hT hw hA hlev)
  have hidx : ∀ p, idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T p)) ≠ 0 := fun p => by
    obtain ⟨N, hN, h⟩ := hmov p.1 p.2
    refine idx_latF_ne_zero hS hT _ hN ?_
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoF S T) gamF_rhoF hidx
  exact ⟨w, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2⟩

namespace IsLatRep

variable {hψ : IsCharAF D.host.F ψ} {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
  {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ ΛS ΛT w lam Om)
include h

theorem fix_vac {p : GA D S × GA D T} (hp : ∀ a ∈ latF S T ΛS ΛT, rhoF S T p a ∈ latF S T ΛS ΛT) (e : thetaSub ψ S T)
    (he : Fixes (opF hψ S T w) (latF S T ΛS ΛT) e) : Om p e = e := by
  rw [h.vac p e he]
  exact normOp_of_le (isHeis_opF hψ S T h.hw) lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he

theorem real_triv {g : GA D S} {k : GA D T} (hg : g ∈ GinfC S) (hk : k ∈ GinfC T) (f : thetaSub ψ S T) :
    Om (g, k) f = f := by
  have : Om (g, k) = LinearMap.id := by
    refine LinearMap.ext_on h.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    rw [h.op, rhoF_real hg hk, h.fix_vac (fun a ha => by rwa [rhoF_real hg hk]) e he, LinearMap.id_apply]
  rw [this, LinearMap.id_apply]

theorem comm (L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T) (hL : ∀ x v, L (opF hψ S T w x v) = opF hψ S T w x (L v))
    (p : GA D S × GA D T) (f : thetaSub ψ S T) : Om p (L f) = L (Om p f) := by
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on h.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opF hψ S T w) (latF S T ΛS ΛT) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, h.op, h.op, hL, h.vac p e he, h.vac p _ he',
      normOp_comm (isHeis_opF hψ S T h.hw) lam (h.sd' p) (h.fin p) L hL he]
  exact LinearMap.congr_fun this f

theorem heis_fin (p : GA D S × GA D T) (x : XF S T) (f f' : thetaSub ψ S T)
    (hf : (f' : WO S T → ℂ) = heisO ψ S T x f) :
    (Om p f' : WO S T → ℂ) = heisO ψ S T (actO S T p.1 p.2 x) (Om p f) := by
  have h1 : opF hψ S T w x f = phase ψ w x • f' := Subtype.ext (by rw [coe_opF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (h.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opF, phase_rhoF, coe_rhoF] at h2
  exact smul_right_injective _ (phase_ne_zero w x) h2

theorem eventually_fix (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (f : thetaSub ψ S T) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), Om p f = f := by
  have H := isHeis_opF hψ S T h.hw
  have hgen := GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT hS hT
  obtain ⟨hlev, -⟩ := GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT hS hT hgen
  obtain ⟨h1, h2⟩ := GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice D S T ΛS ΛT hS hT hgen
  have hf : f ∈ Submodule.span ℂ
      {m | ∃ x e, Fixes (opF hψ S T w) (latF S T ΛS ΛT) e ∧ m = opF hψ S T w x e} := by
    rw [h.span]; trivial
  induction hf using Submodule.span_induction with
  | mem _ hm =>
    obtain ⟨x, e, he, rfl⟩ := hm
    obtain ⟨N, hN, hNU⟩ := hlev _ (GlobalTheory.FinTranslate.isOpen_annSub hψ (XF.fin (w • x)))
    filter_upwards [h1, h2 x x.fin N hN] with p hp hp'
    obtain ⟨l, hl, hl'⟩ := hp'
    have e1 : rhoF S T p x = x + N • XF.mk l (latO_fin hl) := XF.ext hl'
    have e2 : gamF ψ S T (w • x) (N • XF.mk l (latO_fin hl)) = 1 := by
      have e3 : ψ (symplOH S T (w • x : XF S T) (N • l)) = 1 := (hNU l hl).2
      rw [gamF, ← symplOH_add_self, AddChar.map_add_eq_mul, XF.coe_nsmul, XF.coe_mk, e3, one_mul]
    have e4 := H.comp x (N • XF.mk l (latO_fin hl)) e
    rw [he _ (nsmul_mem (show XF.mk l (latO_fin hl) ∈ latF S T ΛS ΛT from hl) N), e2, one_smul] at e4
    rw [h.op, h.fix_vac (fun a ha => hp a ha) e he, e1, ← e4]
  | zero => exact Filter.Eventually.of_forall fun p => map_zero _
  | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]
  | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]

theorem cont (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (f : thetaSub ψ S T) (u : WO S T) :
    Continuous fun p => (Om p f : WO S T → ℂ) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WO S T → ℂ) u) ?_
  filter_upwards [h1.eventually (h.eventually_fix hS hT f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

theorem unit (hlam : GoodNorm (sgO D) lam) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (p : GA D S × GA D T) (f : thetaSub ψ S T) :
    ∫⁻ u in 𝓕, ‖(Om p f : WO S T → ℂ) u‖ₑ ^ 2 ∂μ = ∫⁻ u in 𝓕, ‖(f : WO S T → ℂ) u‖ₑ ^ 2 ∂μ := by
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form D ψ S T hψ (thetaSub ψ S T) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB', hB', GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opF hψ S T h.hw) (fun x y => hψ.2.1 _) lam hlam _ h.sd h.span (rhoF S T p)
    (gamF_rhoF p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) B]
  intro x u v
  have h1 : ∀ u : thetaSub ψ S T, opF hψ S T w x u =
      phase ψ w x • ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ x.fin u.2⟩ := fun u => rfl
  have h2 : phase ψ w x * (starRingEnd ℂ) (phase ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phase ψ w x‖ = 1 from hψ.2.1 _]; simp
  rw [h1, h1, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB x u v _ _ rfl rfl

theorem split
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {e : AE D} (he : IsSplitIdem D e) {g : GA D S} {k : GA D T} (hg : SuppAt e S g) (hk : SuppAt e T k) :
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f : thetaSub ψ S T, ℓ (Om (g, k) f) = (r : ℂ) * ℓ f := by
  have he' := isSplitIdem_conj he
  have hm : ∀ (a b : AE D) (x : XF S T), mulF S T a (mulF S T b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hc : ∀ (a : AE D) (x : XF S T), rhoF S T (g, k) (mulF S T a x) = mulF S T a (rhoF S T (g, k) x) :=
    fun a x => XF.ext (actO_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opF hψ S T h.hw) lam _ h.sd h.span (rhoF S T (g, k)) (gamF_rhoF _)
    (h.sd' _) (h.fin _) (Om (g, k)) (h.op _) (h.vac _) (mulF S T e) (mulF S T (cA D e))
    (fun x => by rw [hm, he.1, mulF_apply]) (fun x => by rw [hm, he'.1, mulF_apply])
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul])
    (fun a ha => idem_smul_mem he.1 _ ha) (fun a ha => idem_smul_mem he'.1 _ ha) (hc e) (hc _)
    (fun x => XF.ext (by
      have := off_smul_actO hg hk (x : WO S T)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := h.fin (g, k)
  have hl := hsq _ hi (by
    rw [idx_latF_eq] at hi ⊢
    refine GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace D S T e he _ _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _) ?_ ?_ ?_ hi
    · rintro a ha _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨a • x, GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hx, rfl⟩, actO_smul g k a x⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.fin
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      show (1 - (e + cA D e)) • actO S T g k x ∈ _
      rw [off_smul_actO hg hk, sub_smul, add_smul, one_smul]
      exact sub_mem hx (add_mem (idem_smul_mem he.1 _ hx) (idem_smul_mem he'.1 _ hx)))
  refine ⟨(Real.sqrt (idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (thetaSub ψ S T).subtype) (fun u m => by
    have h2 : IsHalf (cA D e) (mulF S T (cA D e) u : WO S T) := isHalf_smul he'.1 _
    show ℓ (opF hψ S T w (mulF S T (cA D e) u) m : WO S T → ℂ) = ℓ m
    rw [coe_opF, phase_half he' w h2, one_smul]
    exact h1 _ h2 _ m.2) f
  rw [hl] at this
  push_cast
  exact this

theorem inert {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D S} {k : GA D T}
    (hg : SuppPl η S g) (hk : SuppPl η T k)
    (hst : ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), actO S T g k u ∈ (latO S T ΛS ΛT fun w => w = v))
    (f : thetaSub ψ S T) (hf : ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f) : Om (g, k) f = f := by
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have hP : ∀ a ∈ latF S T ΛS ΛT, mulF S T (algebraMap (AF D.host.F) (AE D) η) a ∈ latF S T ΛS ΛT :=
    fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hv.1) _ ha
  obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
  refine GlobalTheory.T.intertwiner_fixes_of_local_vacuum' (isHeis_opF hψ S T h.hw) _ h.sd h.span (rhoF S T (g, k)) (Om (g, k)) (h.op _)
    (h.fix_vac fun a ha => ?_) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap]) hP (fun x => XF.ext ?_) f
    fun a ha => Subtype.ext ?_
  · have e1 : actO S T g k a = actO S T g k (algebraMap (AF D.host.F) (AE D) η • (a : WO S T)) +
        (a - algebraMap (AF D.host.F) (AE D) η • (a : WO S T)) := by
      have := hoff (a : WO S T)
      rw [sub_smul, sub_smul, one_smul, one_smul] at this
      rw [← this, actO_smul, add_sub_cancel]
    show actO S T g k a ∈ latO S T ΛS ΛT fun _ => True
    rw [e1]
    exact add_mem (GlobalTheory.PlaceModel.latO_le_top _ (hst _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha)))
      (sub_mem ha (hP a ha))
  · have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
        (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
      rw [sub_smul, one_smul]; rfl
    rw [coe_rhoF, e1, actO_smul, hoff]
  · have e1 : mulF S T (algebraMap (AF D.host.F) (AE D) η) a = 2 • (b • a) := by
      rw [mulF_apply, ← hb', two_mul, add_smul, two_nsmul]
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    rw [coe_opF, coe_mulF, hf _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hv.1 ha), e1, phase_two h.sd w e2, one_smul]

end IsLatRep

theorem IsLatRep.Heisenberg₂ (hψ : IsStdChar D ψ (-1)) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ.1 ΛS ΛT w lam Om)
    {g : GA D S} {k : GA D T} (hg : g ∈ GfC S) (hk : k ∈ GfC T) (u : WO S T) (f : thetaSub ψ S T) :
    ∃ f' : thetaSub ψ S T, (f' : WO S T → ℂ) = heisO ψ S T u f ∧
      (Om (g, k) f' : WO S T → ℂ) = heisO ψ S T (actO S T g k u) (Om (g, k) f) := by
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (heisL ψ S T (realIdem D • u)).restrict
    fun _ hf => GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (real_smul_real u) hf
  have hL : ∀ m, (L m : WO S T → ℂ) = heisO ψ S T (realIdem D • u) m := fun _ => rfl
  have hdec : ∀ z : WO S T, z = realIdem D • z + (1 - realIdem D) • z := fun z => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let f₁ : thetaSub ψ S T := ⟨_, GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_smul_fin u) f.2⟩
  refine ⟨L f₁, ?_, ?_⟩
  · rw [hL, ← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin u)), ← hdec]
  · rw [h.comm L (fun x v => Subtype.ext (by
        rw [hL, coe_opF, coe_opF, hL, heisO_smul, heisO_comm, symplO_real_fin S T (real_smul_real u) x.fin,
          AddChar.map_zero_eq_one, one_smul])), hL,
      h.heis_fin (g, k) (XF.mk _ (fin_smul_fin u)) f f₁ rfl, XF.coe_mk, actO_smul,
      ← heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin _)),
      ← smul_actO (real_smul_mt hg) (real_smul_mt hk) u, ← hdec]

theorem exists_isFinWeil (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (χS χT : (AE D)ˣ →* Circle)
    (hχS : IsHeckeChar D χS) (hχT : IsHeckeChar D χT) (hrS : ResEta D χS S.rank) (hrT : ResEta D χT T.rank) :
    ∃ om, IsFinWeil ψ S T ΛS ΛT χS χT om := by
  obtain ⟨lam, hlam, hsq⟩ := exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D
  obtain ⟨c, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε S χT _ hχT hrT
  obtain ⟨d, d1, d2, d3, d4⟩ := GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar D ε hε T χS _ hχS hrS
  let z : GA D S × GA D T → Circle := fun p => (c p.1)⁻¹ * d p.2
  have z1 : z 1 = 1 := by simp [z]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := (c1.comp continuous_fst).inv.mul (d1.comp continuous_snd)
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_, fun v η hv g k hg hk hst f hf hfix => ?_⟩
  · rw [ho p f hf]
    exact (thetaSub ψ S T).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (h.cont hS hT ⟨f, hf⟩ u)
  · rw [← h.unit hlam μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, h.real_triv hg hk, show z (g, k) = 1 by simp [z, c2 g hg, d2 k hk], Circle.coe_one, one_smul]
  · obtain ⟨f', h1, h2⟩ := h.Heisenberg₂ hψ hg hk u ⟨f, hf⟩
    rw [ho _ f hf, heisO_smul, ← h2, ← h1]
    exact hom _ f'
  · obtain ⟨r, hr, h1⟩ := h.split hsq he hg hk
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacO χS χT x y by simp only [z, splitFacO, c4 e he g x hg hx, d4 e he k y hk hy]]
    ring
  · rw [ho _ f hf, h.inert hv hg hk (fun u hu => (hst u).1 hu) ⟨f, hf⟩ hfix,
      show z (g, k) = 1 by simp [z, c3 v η hv g hg, d3 v η hv k hk], Circle.coe_one, one_smul]

end GlobalTheory.FinWeilO

end
end
