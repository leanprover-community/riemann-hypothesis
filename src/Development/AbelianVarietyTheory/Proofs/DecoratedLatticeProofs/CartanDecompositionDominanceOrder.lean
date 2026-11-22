module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PosIffLtCard

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalInduct

def psum {N : ℕ} (ν : Fin N → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i

def pot {N : ℕ} (ν : Fin N → ℤ) : ℤ := ∑ j ∈ Finset.range (N + 1), psum ν j

theorem psum_succ {N : ℕ} (ν : Fin N → ℤ) (i : Fin N) : psum ν (i + 1) = psum ν i + ν i := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin N => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter (fun j : Fin N => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem pot_lt {N : ℕ} {μ ν : Fin N → ℤ} (h : ∀ j, psum μ j ≤ psum ν j) (hne : μ ≠ ν) : pot μ < pot ν := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ ν i := by
    by_contra h'; push_neg at h'; exact hne (funext h')
  have hiN := i.isLt
  have : ∃ j ∈ Finset.range (N + 1), psum μ j < psum ν j := by
    by_contra h'; push_neg at h'
    have e1 : psum μ i = psum ν i := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    have e2 : psum μ (i + 1) = psum ν (i + 1) := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    rw [psum_succ, psum_succ, e1] at e2
    exact hi (by linarith)
  obtain ⟨j, hj, hlt⟩ := this
  exact Finset.sum_lt_sum (fun j _ => h j) ⟨j, hj, hlt⟩

theorem pot_nonneg {N : ℕ} {ν : Fin N → ℤ} (h : ∀ i, 0 ≤ ν i) : 0 ≤ pot ν :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ => h i

theorem pos_iff_lt {N : ℕ} {e : Fin N → ℤ} (ha : Antitone e) (i : Fin N) :
    0 < e i ↔ (i : ℕ) < (Finset.univ.filter fun j => 0 < e j).card := by
  first
  | exact @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | (apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card ..)

theorem nonneg_of_dom {N : ℕ} {ν e : Fin N → ℤ} (hν : Antitone ν) (he : ∀ i, 0 ≤ e i)
    (hle : ∀ j, psum ν j ≤ psum e j) (hsum : ∑ i, ν i = ∑ i, e i) (i : Fin N) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  have sν := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) ν
  have se := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) e
  have tν : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), ν j < 0 := by
    refine Finset.sum_neg (fun j hj => ?_) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact lt_of_le_of_lt (hν (Fin.le_def.2 hj)) hneg
  have te : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), e j :=
    Finset.sum_nonneg fun j _ => he j
  have := hle i
  unfold psum at this
  linarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.ZonalInduct
