import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

section Gen

variable {K : Type} [Field K] [NumberField K]

def hosEquiv : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv w := by cases w; rfl
  right_inv p := rfl



end Gen

section Deg

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]




end Deg


end PI.DvRows
end
end

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

def Adapted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∃ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) ∧
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e ∧
      Submodule.span K (Set.range u) = U ∧
      (∀ i, Fin.append u z i ∈ cutE A e A.L) ∧
      LinearIndependent K y ∧ (∀ i, y i ∈ lamSub A e h U) ∧
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) ∧
      (cutE A e A.L).FG ∧ (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K (cutE A e A.L : Set A.V) = Submodule.span K (Set.range (Fin.append u z)) ∧
      Submodule.span K ((cutE A e A.L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) A.V) : Set A.V) =
        Submodule.span K (Set.range u)





end PI.DvRows
end
end

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma exists_smul_mem_of_span {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ M := by
  obtain ⟨s, hs, hsx⟩ := span_le_locS M hx
  exact ⟨s, nonZeroDivisors.ne_zero hs, hsx⟩

lemma mem_span_of_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) {x : V} (s : 𝓞 K) (hs : s ≠ 0)
    (hsx : s • x ∈ M) : x ∈ Submodule.span K (M : Set V) := by
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h0; exact hs (IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero]))
  have : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

lemma extend_family {V : Type} [AddCommGroup V] [Module K V] {k m : ℕ} (u : Fin k → V) (t : Fin m → V)
    (hu : LinearIndependent K u) :
    ∃ (d : ℕ) (z : Fin d → V), LinearIndependent K (Fin.append u z) ∧ (∀ i, ∃ j, z i = t j) ∧
      Set.range u ∪ Set.range t ⊆ Submodule.span K (Set.range (Fin.append u z)) := by
  classical
  let v : Fin k ⊕ Fin m → V := Sum.elim u t
  have hs : LinearIndepOn K v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hu
  obtain ⟨b, -, hsb, hspan, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let T : Finset (Fin m) := Finset.univ.filter (fun j => Sum.inr j ∈ b)
  let en : Fin T.card ↪o Fin m := T.orderEmbOfFin rfl
  have hen : ∀ i, en i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  let g : Fin (k + T.card) → Fin k ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ en)
  have hg : Function.Injective g := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;> intro hij <;>
      simp [g, Fin.append_left, Fin.append_right] at hij ⊢
    · exact hij
    · exact hij
  have hrange : Set.range g = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · simp only [g, Fin.append_left]; exact hsb ⟨i', rfl⟩
      · simp only [g, Fin.append_right, Function.comp]
        have := hen i'
        simpa [T] using this
    · intro hx
      rcases x with x | x
      · exact ⟨Fin.castAdd _ x, by simp [g]⟩
      · have hxT : x ∈ T := by simp [T, hx]
        obtain ⟨i, hi⟩ : ∃ i, en i = x := by
          have := T.range_orderEmbOfFin rfl
          have hx' : x ∈ Set.range (T.orderEmbOfFin rfl) := by rw [this]; exact hxT
          exact hx'
        exact ⟨Fin.natAdd _ i, by simp [g, hi]⟩
  have hvg : v ∘ g = Fin.append u (t ∘ en) := by
    funext i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp [g, v]
    · simp [g, v]
  refine ⟨T.card, t ∘ en, ?_, fun i => ⟨en i, rfl⟩, ?_⟩
  · rw [← hvg, ← linearIndepOn_range_iff hg, hrange]
    exact hli
  · have h1 : v '' b = Set.range (Fin.append u (t ∘ en)) := by
      rw [← hvg, Set.range_comp, hrange]
    rw [← h1]
    intro x hx
    apply hspan
    rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨Sum.inl i, Set.mem_univ _, rfl⟩
    · exact ⟨Sum.inr j, Set.mem_univ _, rfl⟩


end PI.DvRows
end
end
