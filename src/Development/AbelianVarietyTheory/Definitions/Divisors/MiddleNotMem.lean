import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

def twoPhase (x : Matrix (n ⊕ Fin 2) (n' ⊕ Fin 3) k) (x' : Matrix (n'' ⊕ Fin 1) (n ⊕ Fin 2) k) : k :=
  ch x + ch x' + ∑ r, x' (.inr 0) (.inl r) * x (.inl r) (.inr 1)



theorem heis_mem (ρ : ℕ) (u β : n → k) : rowE (2 * ρ) ρ u ∈ symN k n (2 * ρ) ∧ colE (2 * ρ) (ρ + 1) β ∈ symN k n (2 * ρ) := by
  rw [symN_even]
  exact ⟨Subgroup.mem_sup_right (RootEx.Model.rowE_mem ρ u), Subgroup.mem_sup_left (RootEx.Model.colE_mem ρ β)⟩


theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

theorem elt_one (J : G.Level) :
    (Reps.through hs J fun _ => 1).elt (fun _ => DoubleCoset.mk _ _ 1) = 1 := by
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    rw [Reps.elt, onColumn_apply]
    cases j with
    | zero => rfl
    | succ j => simp [Reps.through]
  · simp [Reps.elt, onColumn, hi]

omit [MeasurableSpace k] [BorelSpace k] in

theorem moved_one (keep : Bool) (T : G.Args → ℂ) : moved G keep 1 T = T := by
  funext z
  have : charFactor G 1 = 1 := by simp [charFactor]
  cases keep <;> simp [moved, Grid.pathAct_one, this]



end GlobalTheory.FunObj.UnfModel
