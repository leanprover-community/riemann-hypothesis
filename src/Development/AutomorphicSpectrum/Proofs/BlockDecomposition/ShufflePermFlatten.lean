import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import BuildAid.ForwardExisting

section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.Comb

theorem interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm_flatten {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)

end GlobalTheory.CompanionTheory.Comb
end

open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_flatten_of_shuffle : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten
