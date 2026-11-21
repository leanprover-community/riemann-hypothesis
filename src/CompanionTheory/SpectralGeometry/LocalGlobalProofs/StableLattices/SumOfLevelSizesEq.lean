import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import BuildAid.ForwardExisting

section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.SumSz

theorem sum_sz_eq_card : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  intro n M lev h
  have key := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M)))
    (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  unfold sz
  congr 1
  ext a
  simp [Fin.ext_iff]

end GlobalTheory.CompanionTheory.RgCOBlock.SumSz
end

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_of_level_sizes_eq : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card
