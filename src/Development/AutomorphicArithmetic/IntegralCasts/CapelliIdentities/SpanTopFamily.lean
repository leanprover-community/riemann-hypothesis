module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  let φ : (n → E) →ₛₗ[ι] (n → K) :=
    { toFun := fun v j => ι (v j)
      map_add' := fun _ _ => funext fun _ => map_add ι _ _
      map_smul' := fun _ _ => funext fun _ => map_mul ι _ _ }
  let N := Submodule.span K
    (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K))
  have hle : (⊤ : Submodule E (n → E)) ≤ N.comap φ := by
    rw [← hL, Submodule.span_le]
    exact fun x hx => Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine N.sum_mem fun i _ => N.smul_mem _ ?_
  have e : φ (Pi.single i 1) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [φ]
    · simp [φ, hj]
  exact e ▸ hle Submodule.mem_top
