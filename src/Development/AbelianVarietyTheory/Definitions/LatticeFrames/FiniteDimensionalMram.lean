module

public import Mathlib
public import Formalism.LocalRingCardinality.DataAmbForm

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions Module

theorem rank_map_field {K L : Type} [Field K] [Field L] (f : K →+* L) {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n K) : (A.map f).rank = A.rank := by
  classical
  letI := f.toAlgebra
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hL : LinearIndependent L (fun i => algebraMap K L ∘ (A.col ∘ a) i) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have hs : Submodule.span L (Set.range (A.map f).col) =
      Submodule.span L (Set.range (fun i => algebraMap K L ∘ (A.col ∘ a) i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : A.col j ∈ Submodule.span K (Set.range (A.col ∘ a)) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hj
      refine (Submodule.mem_span_range_iff_exists_fun L).2 ⟨fun i => f (c i), ?_⟩
      funext r
      have := congrArg f (congrFun hc r)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this ⊢
      exact this
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨a i, rfl⟩
  rw [hs, ← hspan, finrank_span_eq_card hL, finrank_span_eq_card hli]

section Member

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)

variable (A : ColumnsAtT R C) (P : PeriodMap R C)

end Member

variable (D : D7) (Am : AmbForm D (RowSide.sharp D)) (u : D.what₂.Word)

def dU : ℕ := (D.mem u).A.du

end GlobalTheory.Core.Rk

end
