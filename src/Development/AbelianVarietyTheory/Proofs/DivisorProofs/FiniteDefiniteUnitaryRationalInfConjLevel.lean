import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.BCT.FinPart.norm_emb_entry_le_one
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NumFin

theorem finite_bdd_denom_conj_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  intro E _ _ d hd
  have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  set S := {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} with hS
  have hF := NumberField.Embeddings.finite_of_norm_le E ℂ (d : ℝ)
  have himg : (fun z : E => (d : E) * z) '' S ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ)} := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((d : E) * z) fun w => by
        have h := hz1 w
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        convert h using 2
        rw [← map_natCast (algebraMap E (w.adicCompletion E)) d, ← map_mul]
        rfl
      show IsIntegral ℤ ((d : E) * z)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      calc (d : ℝ) * ‖φ z‖ ≤ (d : ℝ) * 1 := by gcongr; exact hz2 φ
        _ = d := mul_one _
  have hinj : Set.InjOn (fun z : E => (d : E) * z) S := fun a _ b _ h => mul_left_cancel₀ hd0 h
  exact Set.Finite.of_finite_image (hF.subset himg) hinj

end GlobalTheory.NumFin
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  atlas_forward_decl GlobalTheory.NumFin.finite_bdd_denom_conj_le_one
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

theorem exists_nat_denom {ι : Type} [Fintype ι] (a : ι → Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (k : ι) (w : Pl E),
      (d : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
  choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)
  refine ⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩
  have h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
    have := h k w
    rwa [show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast] at this
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) h'

theorem cLoc_val (k : finU E n) (w : Pl E) (i j : Fin n) :
    (cLoc w (k : UA E n)).val i j = pLoc E w ((FinPart.pU k).val i j) := rfl

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU E n, ∃ d : ℕ, 0 < d ∧ ∀ g : finU E n, (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ _ n S hS x
  obtain ⟨D₁, hD₁, h₁⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2
  obtain ⟨D₂, hD₂, h₂⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2
  have key : ∀ (h : finU E n) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n →
      ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
    intro h w hk i j
    have e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU E n) : UA E n) * ((x⁻¹ : finU E n) : UA E n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₁ (i, a) w
    have e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₂ (b, j) w
    have e3 := GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b
    have e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a *
        (cLoc w ((x⁻¹ * h * x : finU E n) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j) =
        ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU E n) : UA E n)).val a b *
        ((D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j) := by
      push_cast; ring
    rw [e4]
    exact mul_mem (mul_mem e1 e3) e2
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩
  rcases GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw
  · exact key g w (hg w hw) i j
  · have hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU E n) : UA E n) ∈
        GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) n := by
      have : (x⁻¹ * g⁻¹ * x : finU E n) = (x⁻¹ * g * x)⁻¹ := by group
      rw [this, Subgroup.coe_inv, map_inv]
      exact (GlobalTheory.LFun.KGL _ n).inv_mem (hg _ hw)
    have h1 := key g⁻¹ _ hinv j i
    have e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w
        ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU E n) : UA E n)).val j i) := by
      rw [GlobalTheory.BCT.LocCpt.cLoc_eq_invT]
      show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
        (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _
      rw [← map_inv, ← map_inv, Subgroup.coe_inv]
      rfl
    rw [e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1

end GlobalTheory.BCT.StabDenom
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU E n, ∃ d : ℕ, 0 < d ∧ ∀ g : finU E n, (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  atlas_forward_decl GlobalTheory.BCT.StabDenom.exists_denom
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_finPt (γ : UE E n) (w : Pl E) (i j : Fin n) :
    (cLoc w ((finPt γ : finU E n) : UA E n)).val i j = algebraMap E (w.adicCompletion E) ((γ : GL (Fin n) E).val i j) :=
  congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)

theorem cLoc_conj_mem_KGL {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (x g : finU E n)
    (hg : g ∈ (globLev S K').map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
  intro w hw
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hg
  have e' : x⁻¹ * g * x = k := by
    rw [← e]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e']
  have hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1 := by
    simpa [globLev, Subgroup.mem_iInf] using hk
  obtain ⟨a, ha, hae⟩ := hk' w hw
  rw [← hae]
  exact Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)

end GlobalTheory.BCT.StabFin

open GlobalTheory.BCT.StabFin in

theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  intro E _ _ _ _ n _ S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
end
end
