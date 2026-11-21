import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.LastRowMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development

section
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem rowExists : RowExists := by
  intro F _ _ n r hr
  obtain ⟨k, hk⟩ : ∃ k, r k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA
  have hAtri : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.mpr (Fin.le_last j))
    rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]
  have hdetA : A.det = r k := by
    rw [Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]
    · rw [hA, Matrix.updateRow_self]
      simp [hσ]
    · intro i _ hi
      rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := A.submatrix id σ with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, Matrix.det_permute', hdetA]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  refine ⟨hunit.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]

end

end PI.GGMirBoundW
end

section
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem addChar_sum {F : Type} [Field F] (ψ₀ : AddChar F ℂ) {m : ℕ} (g : Fin m → F) :
    ψ₀ (∑ i, g i) = ∏ i, ψ₀ (g i) := by
  have h : ∀ s : Finset (Fin m), ψ₀ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ₀ (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  exact h _

theorem charSum_one {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) (a : F) :
    ∑ t : F, ψ₀ (a * t) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp [AddChar.map_zero_eq_one]
  · rw [show (∑ t : F, ψ₀ (a * t)) = ∑ t : F, ψ₀ t from
        Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun t => rfl)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem charSum {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) {m : ℕ} (ν : Fin m → F) :
    ∑ c : Fin m → F, ψ₀ (∑ i, ν i * c i) = if ν = 0 then (Fintype.card F : ℂ) ^ m else 0 := by
  have hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t) := by
    first
      | exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm
      | (rw [Finset.prod_univ_sum]; simp)
  simp_rw [addChar_sum ψ₀]
  rw [hps]
  simp_rw [charSum_one ψ₀ hψ]
  split_ifs with hν
  · subst hν
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hν (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem charOrth : CharOrth := by
  intro F _ _ m ψ₀ hψ r s
  have h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i) := by
    intro x
    rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]
    rfl
  simp_rw [h]
  rw [charSum ψ₀ hψ (r - s)]
  simp only [sub_eq_zero]

theorem sepLemma : SepLemma := by
  intro W _ _ X R ι _ _ _ T χ χ' N hN horth f hf hind
  have hf' : ∀ x (q : R × ι), T x (f q) = χ q.1 x • f q := fun x q => hf x q.1 q.2
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  obtain ⟨s, i⟩ := p
  have h1 : ∑ x, χ' s x • T x (∑ q, g q • f q) = 0 := by
    rw [hg]
    simp
  have h2 : ∑ x, χ' s x • T x (∑ q, g q • f q) =
      ∑ q, (if q.1 = s then N * g q else 0) • f q := by
    simp_rw [map_sum, map_smul, hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have ho := horth q.1 s
    calc ∑ x, χ' s x * (g q * χ q.1 x) = g q * ∑ x, χ q.1 x * χ' s x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = _ := by
          rw [ho]
          split_ifs <;> ring
  have h3 : ∑ q : R × ι, (if q.1 = s then N * g q else 0) • f q = N • ∑ j, g (s, j) • f (s, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp [Finset.smul_sum, smul_smul]
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [h2, h3] at h1
  have key : ∑ j, g (s, j) • f (s, j) = 0 := (smul_eq_zero.mp h1).resolve_left hN
  exact (Fintype.linearIndependent_iff.mp (hind s)) (fun j => g (s, j)) key i

end

end PI.GGMirBoundW
end

section
namespace PI.GGMirBoundW

open Finset Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

theorem card_nonzero (F : Type) [Field F] [Fintype F] (m : ℕ) :
    Fintype.card {r : Fin m → F // r ≠ 0} = Fintype.card F ^ m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]

theorem stepOf : StepOf := by
  intro hB hC hJ hR hO hS F _ _ n IH ψ₀ hψ V _ _ π ℓ hℓ hW

  let π' : Representation ℂ (GL (Fin (n + 1)) F) V := π.comp (E F (n + 1))
  have hW' : IsWhit ψ₀ π' ℓ := by
    intro u hu v
    have h := hW (E F (n + 1) u) (hB F (n + 1) u hu).1 v
    simp only [psiU] at h ⊢
    rw [(hB F (n + 1) u hu).2] at h
    exact h
  obtain ⟨p, hpL, hpI⟩ := IH ψ₀ hψ V π' ℓ hℓ hW'
  let R := {r : Fin (n + 1) → F // r ≠ 0}
  choose g hg using fun r : R => hR F n r.1 r.2
  let A : R × Fin (D F (n + 1)) → GL (Fin (n + 1)) F := fun q => p q.2 * g q.1
  have hArow : ∀ q j, (A q : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j := by
    intro q j
    show ((p q.2 * g q.1 : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j
    rw [lastRow_mul (hpL q.2), hg]
  let f : R × Fin (D F (n + 1)) → Module.Dual ℂ V := fun q => ℓ ∘ₗ π (E F (n + 1) (A q))

  have hf : ∀ (x : Fin (n + 1) → F) (r : R) (i : Fin (D F (n + 1))),
      (π (col x)).dualMap (f (r, i)) = (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x • f (r, i) := by
    intro x r i
    ext v
    show ℓ (π (E F (n + 1) (A (r, i))) (π (col x) v)) = ψ₀ (r.1 ⬝ᵥ x) * ℓ (π (E F (n + 1) (A (r, i))) v)
    rw [← Module.End.mul_apply, ← map_mul, hJ F (n + 1) (A (r, i)) x, map_mul, Module.End.mul_apply,
      hW _ (hC F n _).1, psiU, (hC F n _).2]
    congr 2
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hArow]

  have hblock : ∀ r : R, LinearIndependent ℂ (fun i => f (r, i)) := by
    intro r
    have he : (fun i => f (r, i)) = (π (E F (n + 1) (g r))).dualMap ∘ (fun i => ℓ ∘ₗ π' (p i)) := by
      funext i
      ext v
      show ℓ (π (E F (n + 1) (p i * g r)) v) = ℓ (π (E F (n + 1) (p i)) (π (E F (n + 1) (g r)) v))
      rw [map_mul, map_mul, Module.End.mul_apply]
    rw [he]
    refine hpI.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective ?_))
    intro v
    refine ⟨π (E F (n + 1) (g r))⁻¹ v, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hN : ((Fintype.card F : ℂ) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  have horth : ∀ r s : R, ∑ x : Fin (n + 1) → F, (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x *
      (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) s x = if r = s then (Fintype.card F : ℂ) ^ (n + 1) else 0 := by
    intro r s
    rw [hO F (n + 1) ψ₀ hψ r.1 s.1]
    exact if_congr Subtype.val_inj rfl rfl
  have hind := hS (Module.Dual ℂ V) (Fin (n + 1) → F) R (Fin (D F (n + 1)))
    (fun x => (π (col x)).dualMap) (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x)))
    _ hN (fun r s => by convert horth r s) f hf hblock
  have hcard : Fintype.card (Fin (D F (n + 1 + 1))) = Fintype.card (R × Fin (D F (n + 1))) := by
    rw [Fintype.card_fin, Fintype.card_prod, card_nonzero, Fintype.card_fin, D, D,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), mul_comm]
  let e : Fin (D F (n + 1 + 1)) ≃ R × Fin (D F (n + 1)) := Fintype.equivOfCardEq hcard
  refine ⟨fun k => E F (n + 1) (A (e k)), fun k => lastRowE_E _, ?_⟩
  exact hind.comp e e.injective

end

end PI.GGMirBoundW
end

section
namespace PI.GGMirBoundW

theorem mirabolicBound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma

end PI.GGMirBoundW
end
