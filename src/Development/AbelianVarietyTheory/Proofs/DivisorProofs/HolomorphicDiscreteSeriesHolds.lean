import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModule
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKType
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactFiniteAdelesAwayPBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup

section
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.SignInnerAdjoint

theorem sgn_sq_one {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε a b : ℂ) = 1 := by
  unfold Formalism.REAL.sgn; split_ifs <;> norm_num

theorem sgn_symm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
  unfold Formalism.REAL.sgn; split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem inner_E_right {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (a b : Fin n) (w y : V) :
    ⟪w, E a b y⟫_ℂ = (Formalism.REAL.sgn ε a b : ℂ) * ⟪E b a w, y⟫_ℂ := by
  rw [hU b a w y, sgn_symm, ← mul_assoc, sgn_sq_one, one_mul]

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (l : List (Fin n × Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ∀ w x : V,
      ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ =
        c * ⟪((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w, x⟫_ℂ := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun w x => by simp⟩
  | cons p t ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨(Formalism.REAL.sgn ε p.1 p.2 : ℂ) * c, mul_ne_zero ?_ hc, fun w x => ?_⟩
    · intro h0; have := sgn_sq_one ε p.1 p.2; rw [h0] at this; simp at this
    · simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.map_nil, List.prod_append, List.prod_nil, mul_one, Module.End.mul_apply,
        Prod.fst_swap, Prod.snd_swap] at h ⊢
      rw [inner_E_right hU, h, mul_assoc]

end GlobalTheory.SignInnerAdjoint

theorem GlobalTheory.SignInnerAdjoint.main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  intro n ε V _ _ E hU l w x hne
  obtain ⟨c, hc, h⟩ := GlobalTheory.SignInnerAdjoint.word_adj hU l
  rw [h] at hne
  have h2 := right_ne_zero_of_mul hne
  intro h3; exact h2 (inner_eq_zero_symm.mp h3)
end

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  atlas_forward_decl GlobalTheory.SignInnerAdjoint.main
end

section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_map_root_eq_sum_count {n : ℕ} (l : List (Fin n × Fin n)) :
    (l.map fun p : Fin n × Fin n => root p.1 p.2).sum
      = ∑ a, ∑ b, (l.count (a, b) : ℝ) • root a b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.count_cons, Nat.cast_add, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨x, y⟩ := p
    simp only [beq_iff_eq, Prod.mk.injEq]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp

theorem root_word_count_letters : ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = false ∧ ε p.2 = true) → μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = Λ + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε μ Λ l hl hsum
  refine ⟨fun a b => l.count (b, a), ?_, ?_⟩
  · intro a b h
    have hm : (b, a) ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨(hl _ hm).2, (hl _ hm).1⟩
  · rw [sum_map_root_eq_sum_count] at hsum
    have key : ∑ a, ∑ b, ((l.count (b, a) : ℕ) : ℝ) • root a b
        = - ∑ a, ∑ b, ((l.count (a, b) : ℕ) : ℝ) • root a b := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have : root b a = - root a b := by
        unfold root; abel
      rw [this, smul_neg]
    rw [key, ← hsum]; abel

end GlobalTheory
end

section
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kType_weight_in_cone_over_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε H _ _ σ D E lam hP hC hDS hK μ S hS
  have hcomp : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hI : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨w, hw0, -, hwH⟩ := hK.hw μ S hS
  have key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype,
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 := by
    by_contra hne
    let Q : Submodule ℂ D :=
      { carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) →
          ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0}
        add_mem' := by
          intro a b ha hb l hl
          rw [map_add, inner_add_right, ha l hl, hb l hl, add_zero]
        zero_mem' := by
          intro l hl
          rw [map_zero, inner_zero_right]
        smul_mem' := by
          intro c a ha l hl
          rw [map_smul, inner_smul_right, ha l hl, mul_zero] }
    have hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype := by
      intro T hT y hy
      have hTD := (GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT).1
      refine ⟨⟨y, hTD hy⟩, ?_, rfl⟩
      intro l hl
      by_contra h
      exact hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩
    have hlow : lowKSub ε lam σ ≤ Q.map D.subtype := sSup_le hT
    have hspan := GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hP hC hDS hK
    have hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤
        (ℂ ∙ w)ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨l, hl, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨x', hx', hxx⟩ := hlow hx
      have : x' = x := Subtype.ext hxx
      subst this
      exact hx' l hl
    rw [hspan] at hle
    have hw : w ∈ (ℂ ∙ w)ᗮ := hle Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hw
    exact hw0 hw
  obtain ⟨T, hT, x, hx, l, hl, hne⟩ := key
  have hadj := GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero n ε D E hK.unit l w x hne
  obtain ⟨-, hfd, hstab, hhw⟩ := GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT
  have hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [List.mem_reverse] at hq
    exact ⟨(hl q hq).2, (hl q hq).1⟩
  have hKU : KUnit ε E := fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z
  obtain ⟨l', -, hl'ty, hsum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw
    μ w hwH false true _ hl' x hx hadj
  exact GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum
end

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  atlas_forward_decl GlobalTheory.kType_weight_in_cone_over_lowK
end

section
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExistsStep

theorem kModExists_holds : CompanionTheory.D.LK.KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists CompanionTheory.D.DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs CompanionTheory.D.DSIC.hKFinStab
    CompanionTheory.D.DSIC.hStabLink CompanionTheory.D.DSIC.hHWofType CompanionTheory.D.DSIC.hTypeOfHW

end GlobalTheory.CompanionTheory.KModExistsStep
end

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kFiniteModule_irreducible_unitary : CompanionTheory.D.LK.KModExists := by
  atlas_forward_decl GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds
end

section
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem raisingSpan_eq_span_words : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  intro n ε H _ _ σ D E hK S hSD
  set Y : Set D := {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hY
  have hcmp := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK

  have hstab : ∀ a b, ε a = true → ε b = false → ∀ y ∈ Submodule.span ℂ Y, E a b y ∈ Submodule.span ℂ Y := by
    intro a b ha hb y hy
    have hle : Submodule.span ℂ Y ≤ (Submodule.span ℂ Y).comap (E a b) := by
      rw [Submodule.span_le]
      rintro z ⟨l, hl, x, hx, rfl⟩
      apply Submodule.subset_span
      refine ⟨(a, b) :: l, ?_, x, hx, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨ha, hb⟩
        · exact hl p hp
      · simp [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hle hy
  apply le_antisymm
  · rw [raisingSpan, Submodule.span_le]
    rintro w ⟨l, hl, v, hv, rfl⟩
    have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) →
        ∃ y ∈ Submodule.span ℂ Y, (y : H) = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v := by
      intro l
      induction l with
      | nil =>
        intro _
        refine ⟨⟨v, hSD hv⟩, Submodule.subset_span ⟨[], by simp, ⟨v, hSD hv⟩, hv, by simp⟩, rfl⟩
      | cons Z l ih =>
        intro hl
        obtain ⟨y, hy, hyv⟩ := ih (fun Z' hZ' => hl Z' (List.mem_cons_of_mem _ hZ'))
        have hZ := hl Z List.mem_cons_self
        refine ⟨∑ a, ∑ b, Z a b • E a b y, ?_, ?_⟩
        · refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
          by_cases h : ε a = true ∧ ε b = false
          · exact Submodule.smul_mem _ _ (hstab a b h.1 h.2 y hy)
          · rw [hZ a b h, zero_smul]
            exact Submodule.zero_mem _
        · rw [List.foldr_cons, ← hyv, hcmp Z y]
    obtain ⟨y, hy, hyv⟩ := key l hl
    exact ⟨y, hy, hyv⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨l, hl, x, hx, rfl⟩, rfl⟩
    have key : ∀ l : List (Fin n × Fin n),
        (((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x : D) : H) =
          (l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ)).foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) (x : H) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.map_cons, List.foldr_cons, ← ih, hcmp, List.prod_cons, Module.End.mul_apply]
        congr 1
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
        · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [Matrix.single_apply, Ne.symm ha]
        · simp
    refine Submodule.subset_span ⟨l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ), ?_, (x : H), hx, key l⟩
    intro Z hZ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hZ
    exact single_mem_pPlus (hl p hp).1 (hl p hp).2 1

end GlobalTheory.HolDS
end

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  atlas_forward_decl GlobalTheory.HolDS.raisingSpan_eq_span_words
end

section
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HdSmooth

theorem kFinite_smoothVec : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  intro n ε H _ _ _ _ σ hU hI v hv
  have h := (GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hU hI v hv).smoothVec (P := 1)
    (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  simpa [inG] using h

end GlobalTheory.HdSmooth
end

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  atlas_forward_decl GlobalTheory.HdSmooth.kFinite_smoothVec
end

section
open Matrix GlobalTheory.HolDS

namespace GlobalTheory.HolDS

theorem holomorphicDiscreteSeries_holds : GlobalTheory.Published.HolomorphicDiscreteSeries := by
  intro n ε lam hHC hHol H _ _ σ hDS
  obtain ⟨hc, hnt, hU, hI, -⟩ := id hDS
  haveI := hc
  haveI := hnt
  obtain ⟨D, E, hK⟩ := GlobalTheory.T.exists_kFiniteModule_irreducible_unitary n ε H σ hU hI
  have low := GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed n ε H σ D E lam hHC hHol hDS hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun μ S hS => GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType n ε H σ D E lam hHC hHol hDS hK μ S hS
  · exact fun v hv => GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep n ε H σ hU hI v hv
  · intro Z hZ v hv
    have hvD : v ∈ D := low.1 hv
    have hx : (⟨v, hvD⟩ : D) ∈ (Formalism.MainNotions.S.lowKSub ε lam σ).comap D.subtype := hv
    have h := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK Z ⟨v, hvD⟩
    simp only at h
    rw [h]
    have h0 : (∑ a, ∑ b, Z a b • E a b ⟨v, hvD⟩ : D) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : ε a = false ∧ ε b = true
      · rw [low.2.2.2 b a hab.2 hab.1 _ hx, smul_zero]
      · rw [hZ a b hab, zero_smul]
    rw [h0]
    rfl
  · intro v
    rw [GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod n ε H σ D E hK _ low.1, GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hHC hHol hDS hK,
      Submodule.map_top, Submodule.range_subtype]
    exact (hK.mem v).symm

end GlobalTheory.HolDS
end
