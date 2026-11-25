module

import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  apply GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound.isHomogeneous_of_isMultiHomogIdeal <;> assumption

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) :=
  HilbDegBound.isMultiHomogIdeal_sup_span hI hs


omit [Fintype K] [DecidableEq K] in
theorem colon_span_eq_of_isPrime {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext x
  rw [Ideal.mem_colon_span_singleton]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩


omit [Fintype K] [DecidableEq K] in
theorem ringKrullDim_sup_span_add_one_le {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P s) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n :=
  HilbDegBound.lt_of_add_one_le_natCast h

end Lemmas

theorem totalDegree_add_card_le_ringKrullDim (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u})
    (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) :
    ∀ I : Ideal (MRing ι F), IsMultiHomogIdeal I → ringKrullDim (MRing ι F ⧸ I) < n →
      ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
      ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I) := by
  induction n with
  | zero =>
    intro I _ hlt p hp hp0
    have hsub : Subsingleton (MRing ι F ⧸ I) := by
      refine not_nontrivial_iff_subsingleton.1 fun hn => ?_
      exact absurd hlt (not_lt.mpr (by simpa using
        ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ I)))
    have hz : ∀ m, hilbFn I m = 0 := fun m => by
      unfold hilbFn
      split_ifs
      · rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      · rfl
    exact absurd (hU K _ p 0 hp (Filter.Eventually.of_forall fun m => by simp [hz])) hp0
  | succ n ih =>
    have prime : ∀ P : Ideal (MRing ι F), P.IsPrime → IsMultiHomogIdeal P →
        ringKrullDim (MRing ι F ⧸ P) < (n + 1 : ℕ) → ∀ p : MvPolynomial K ℚ,
        EventuallyPoly (hilbFn P) p → p ≠ 0 →
        ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P) := by
      intro P hPp hPh hlt p hp hp0
      by_cases hrel : IsRelevant P
      swap
      · exact absurd (hU K _ p 0 hp ((hZ F K ι P hrel).mono fun m hm => by simp [hm])) hp0
      have hge := hD F K ι P ⟨hPp, hPh, hrel⟩
      choose i hi using hrel
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim (MRing ι F ⧸ P) = N := by
        generalize ringKrullDim (MRing ι F ⧸ P) = x at hge hlt
        induction x using WithBot.recBotCoe with
        | bot => exact absurd hge (not_le.mpr (WithBot.bot_lt_coe _))
        | coe a =>
          induction a using ENat.recTopCoe with
          | top => exact absurd hlt (by simp)
          | coe a => exact ⟨a, rfl⟩
      have hKN : Fintype.card K ≤ N := by exact_mod_cast hN ▸ hge
      have hdiff : ∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < N - Fintype.card K) ∧
          EventuallyPoly (diffStep (Pi.single k 1) (hilbFn P)) q := by
        intro k
        have hs : IsMultiHomog (X ⟨k, i k⟩ : MRing ι F) (Pi.single k 1) :=
          isWeightedHomogeneous_X _ _ _
        have hJ := isMultiHomogIdeal_sup_span hPh hs
        obtain ⟨q, hq⟩ := h1 F K ι _ hJ
        refine ⟨q, ?_, ?_⟩
        · refine (eq_or_ne q 0).imp_right fun hq0 => ?_
          have hdrop := hN ▸ ringKrullDim_sup_span_add_one_le (P := P) (hi k)
          have hNn : N ≤ n := by
            rw [hN] at hlt
            exact Nat.lt_succ_iff.1 (by exact_mod_cast hlt)
          have hb := ih _ hJ (lt_of_add_one_le_natCast (hdrop.trans (by exact_mod_cast hNn)))
            q hq hq0
          have h' : ((q.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ N :=
            le_trans (by gcongr) hdrop
          have h'' : q.totalDegree + Fintype.card K + 1 ≤ N := by exact_mod_cast h'
          omega
        · refine hq.mono fun m hm => ?_
          have e := h2 F K ι P hPh (Pi.single k 1) _ hs m
          rw [colon_span_eq_of_isPrime hPp (hi k)] at e
          have ec : (fun k' => ((Pi.single k 1 : K → ℕ) k' : ℤ)) = (Pi.single k 1 : K → ℤ) := by
            ext k'
            simp [Pi.single_apply]
          rw [ec] at e
          simp only [diffStep]
          rwa [e]
      obtain ⟨p', hp'deg, hp'⟩ := h3 K (hilbFn P) (N - Fintype.card K) hdiff
      obtain rfl := hU K _ p p' hp hp'
      rw [hN]
      exact_mod_cast (show p.totalDegree + Fintype.card K ≤ N by omega)
    intro I hI hlt p hp hp0
    obtain ⟨r, Q, c, hQ, hsum, -, -⟩ := h4 F K ι I hI
    choose pj hpj using fun j => h1 F K ι (Q j) (hQ j).2.1
    choose q hq hqdeg hq0 using fun j => hS K _ (pj j) (fun k => (c j k : ℤ)) (hpj j)
    have hsumP : EventuallyPoly (hilbFn I) (∑ j, q j) := by
      filter_upwards [Filter.eventually_all.mpr hq, hsum] with m hm hm'
      rw [hm', map_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => hm j
    have hpq := hU K _ p _ hp hsumP
    have hDQ : ∀ j, q j ≠ 0 → (((q j).totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ I) := by
      intro j hj
      have hle := ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hQ j).2.2)
        (Ideal.Quotient.factor_surjective _)
      have hb := prime (Q j) (hQ j).1 (hQ j).2.1 (hle.trans_lt hlt) (pj j) (hpj j)
        fun h => hj (hq0 j h)
      refine le_trans ?_ (hb.trans hle)
      exact_mod_cast Nat.add_le_add_right (hqdeg j) _
    classical
    set T := Finset.univ.filter fun j => q j ≠ 0 with hT
    have hpT : p = ∑ j ∈ T, q j := by rw [hpq, hT, Finset.sum_filter_ne_zero]
    have hTne : T.Nonempty := Finset.nonempty_of_sum_ne_zero (hpT ▸ hp0 : ∑ j ∈ T, q j ≠ 0)
    obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image T (fun j => (q j).totalDegree) hTne
    have hdeg : p.totalDegree ≤ (q j).totalDegree := hpT ▸ totalDegree_finsetSum_le hjmax
    refine le_trans ?_ (hDQ j (Finset.mem_filter.mp hjT).2)
    exact_mod_cast Nat.add_le_add_right hdeg _

theorem HilbDegreeBound.proof (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  refine ⟨fun _ p hp hp0 => ?_, fun hrel => hZ F K ι I hrel⟩
  have key := fun n => totalDegree_add_card_le_ringKrullDim h1 h2 h3 h4 hU hS hZ hD F K ι n I hI
  unfold relDim
  generalize hx : ringKrullDim (MRing ι F ⧸ I) = x at key
  induction x using WithBot.recBotCoe with
  | bot =>
    have := key 0 (WithBot.bot_lt_coe _) p hp hp0
    exact absurd this (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe N =>
      have := key (N + 1) (by exact_mod_cast Nat.lt_succ_self N) p hp hp0
      have hle : p.totalDegree + Fintype.card K ≤ N := by exact_mod_cast this
      show ((p.totalDegree : ℕ) : WithBot (WithTop ℤ)) ≤
        (((N : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
      have : (p.totalDegree : ℤ) ≤ (N : ℤ) - Fintype.card K := by omega
      exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.FieldNumbers
