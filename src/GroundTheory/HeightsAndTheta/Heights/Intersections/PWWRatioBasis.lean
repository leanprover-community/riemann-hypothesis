import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StWWRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.StMobiusAlgIndep

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]

theorem RatioField.map_mem [CharZero Ω] [CharZero Φ] {S : Set Ω} {L : IntermediateField ℚ Φ}
    (hS : ∀ w ∈ S, algebraMap Ω Φ w ∈ L) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    algebraMap Ω Φ z ∈ L := by
  have hle : (IntermediateField.adjoin ℚ S).map (algebraMap Ω Φ).toRatAlgHom ≤ L := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  exact hle ((IntermediateField.mem_map _).mpr ⟨z, hz, rfl⟩)

theorem RatioField.isAlgebraic_map [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {z : Ω} (hz : IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) z)
    {s : Set Φ} (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  let ψ := (algebraMap Ω Φ).toRatAlgHom
  have ht' : AlgebraicIndependent ℚ (ψ ∘ t) := ht.map' (algebraMap Ω Φ).injective
  have h4 : IsAlgebraic (Algebra.adjoin ℚ (Set.range (ψ ∘ t))) (ψ z) := by
    by_contra h
    have h3 : AlgebraicIndependent ℚ (fun o : Option (Fin d) => o.elim z t) := by
      refine AlgebraicIndependent.of_comp ψ ?_
      convert (ht'.option_iff_transcendental (ψ z)).mpr h using 1
      funext o
      cases o <;> rfl
    exact (ht.option_iff_transcendental z).mp h3 (IntermediateField.isAlgebraic_adjoin_iff.mp hz)
  have hsub : Set.range (ψ ∘ t) ⊆ s := by
    rintro _ ⟨n, rfl⟩
    exact hs n
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (h4.tower_top_of_subalgebra_le (Algebra.adjoin_mono hsub))

theorem RatioField.isAlgebraic_map_adjoin [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {S : Set Ω}
    (hS : ∀ w ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) w) {s : Set Φ}
    (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  have h := RatioField.map_mem (L := (algebraicClosure (IntermediateField.adjoin ℚ s) Φ).restrictScalars ℚ)
    (fun w hw => (IntermediateField.mem_restrictScalars ℚ).mpr
      (mem_algebraicClosure_iff.mpr (RatioField.isAlgebraic_map ht (hS w hw) hs))) hz
  exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp h)

variable {E κ : Type*} [AddCommGroup E] [Module Ω E]

theorem RatioField.lineVal_cramer (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (k₀ k₁ k : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) (a : Φ) :
    T.lineVal e (φ k) a =
      algebraMap Ω Φ ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₀) a +
        algebraMap Ω Φ ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₁) a := by
  have hlin : φ k = ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₀ +
      ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₁ := by
    refine b.ext fun q => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hφ, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hg]
    fin_cases q <;> simp <;> ring
  rw [hlin]
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem RatioField.det_ne_zero (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (hX : X ≠ 0) (k₀ k₁ : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) :
    φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
  have hval : ∀ k q, φ k (b q) = e.repr (b q) 0 * φ k (e 0) + e.repr (b q) 1 * φ k (e 1) := by
    intro k q
    conv_lhs => rw [← e.sum_repr (b q)]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul]
  intro h
  apply hg
  have hX2 : X * X ≠ 0 := mul_ne_zero hX hX
  apply (mul_right_injective₀ hX2).eq_iff.mp
  have h00 := hval k₀ 0
  have h01 := hval k₀ 1
  have h10 := hval k₁ 0
  have h11 := hval k₁ 1
  rw [hφ] at h00 h01 h10 h11
  linear_combination (X * g k₀ 0) * h11 + (e.repr (b 1) 1 * φ k₁ (e 1) + e.repr (b 1) 0 * φ k₁ (e 0)) * h00 -
    (X * g k₀ 1) * h10 - (e.repr (b 0) 1 * φ k₁ (e 1) + e.repr (b 0) 0 * φ k₁ (e 0)) * h01 +
    -(e.repr (b 0) 0 * e.repr (b 1) 1 - e.repr (b 0) 1 * e.repr (b 1) 0) * h

end

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem WWRatioBasis.proof (hM : MobiusAlgIndep.Statement) : WWRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF hxt hδ hδF hφ hgF hg ha
  obtain ⟨hden, hr⟩ := hM Ω Φ 2 a (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1)) ha
    (RatioField.det_ne_zero e b φ g (x i₀) hx k₀ k₁ hφ hg)
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  set W := T.wwCoord x δ e φ (a 0) (a 1)
  let c : ∀ k, T.wwIdx ι ν κ k := fun k => T.WBlk.casesOn (motive := fun k => T.wwIdx ι ν κ k) k i₀ l₀ k₀ k₀
  let r : Fin 2 → Φ := fun j => T.lineVal e (φ k₁) (a j) / T.lineVal e (φ k₀) (a j)
  let t' : Fin (d + 2) → Φ := fun n => Sum.elim (fun m => algebraMap Ω Φ (t m)) r (finSumFinEquiv.symm n)
  have ht'n : ∀ m, algebraMap Ω Φ (t m) ∈ Set.range t' := fun m =>
    ⟨finSumFinEquiv (Sum.inl m), by simp [t']⟩
  have hr' : ∀ j, r j ∈ Set.range t' := fun j => ⟨finSumFinEquiv (Sum.inr j), by simp [t']⟩
  have hrC : ∀ j, r j ∈ coneRatios W c := fun j => by
    fin_cases j
    exacts [⟨⟨.line0, k₁⟩, rfl⟩, ⟨⟨.line1, k₁⟩, rfl⟩]

  have hline : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ j k, T.lineVal e (φ k) (a j) / T.lineVal e (φ k₀) (a j) ∈ L := by
    intro L hF hrL j k
    have hgF' : ∀ k q, g k q ∈ F := hgF
    rw [RatioField.lineVal_cramer e b φ g (x i₀) k₀ k₁ k hφ hg, add_div, mul_div_assoc,
      mul_div_assoc, div_self (show T.lineVal e (φ k₀) (a j) ≠ 0 from hden j)]
    refine L.add_mem (L.mul_mem (hF _ ?_) (L.one_mem)) (L.mul_mem (hF _ ?_) (hrL j)) <;>
      exact F.div_mem (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))
        (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))

  have hcases : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ y ∈ coneRatios W c, y ∈ L := by
    rintro L hF hrL _ ⟨⟨blk, i⟩, rfl⟩
    cases blk
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (hδF i)
    · exact hline L hF hrL 0 i
    · exact hline L hF hrL 1 i
  refine ⟨c, t', fun k => ?_, ?_, fun n => ?_, fun y hy => ?_⟩
  · cases k
    exacts [(map_ne_zero _).mpr hx, (map_ne_zero _).mpr hδ, hden 0, hden 1]
  · have hti : AlgebraicIndependent ℚ fun m => algebraMap Ω Φ (t m) :=
      ht.map' (f := (algebraMap Ω Φ).toRatAlgHom) (algebraMap Ω Φ).injective
    refine (algebraicIndependent_equiv' (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)) ?_).mpr
      (hti.sumElim_of_tower (S := Ω) (by rintro _ ⟨m, rfl⟩; exact ⟨t m, rfl⟩) hr)
    funext n
    simp only [Function.comp, Equiv.trans_apply, t']
    cases finSumFinEquiv.symm n <;> rfl
  · have hbase : ∀ z ∈ F, algebraMap Ω Φ z ∈ IntermediateField.adjoin ℚ (coneRatios W c) :=
      fun z hz => RatioField.map_mem (S := Set.range fun j => x j / x i₀) (fun w hw => by
        obtain ⟨j, rfl⟩ := hw
        exact IntermediateField.subset_adjoin _ _ ⟨⟨.base, j⟩, by simp [W, c, T.wwCoord, map_div₀]⟩) hz
    obtain ⟨m | j, rfl⟩ := finSumFinEquiv.surjective n
    · simpa [t'] using hbase _ (htF m)
    · simpa [t'] using IntermediateField.subset_adjoin _ _ (hrC j)
  · have hL := hcases ((algebraicClosure (IntermediateField.adjoin ℚ (Set.range t')) Φ).restrictScalars ℚ)
      (fun z hz => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (RatioField.isAlgebraic_map_adjoin (S := Set.range fun j => x j / x i₀) ht
          (fun w hw => by obtain ⟨j, rfl⟩ := hw; exact hxt j) ht'n hz)))
      (fun j => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (isAlgebraic_algebraMap (⟨r j, IntermediateField.subset_adjoin _ _ (hr' j)⟩ :
          IntermediateField.adjoin ℚ (Set.range t'))))) y hy
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp hL)

end

end GroundTheory.Heights₂.Heights.Inter
end
