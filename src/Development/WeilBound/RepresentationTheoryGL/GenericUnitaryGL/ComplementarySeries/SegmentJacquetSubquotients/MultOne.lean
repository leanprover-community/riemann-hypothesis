import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.MultOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagSM (l d : ℕ) : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d) :=
  ⟨fun i j => if i = j then d else 0, fun i => by simp, fun j => by simp⟩

theorem entry_le {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (i j : Fin l) : b.1 i j ≤ d := by
  calc b.1 i j ≤ ∑ j, b.1 i j :=
        Finset.single_le_sum (f := b.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = d := by simpa using b.2.1 i

theorem isSmooth_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _


theorem isIrreducible_piTensor_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ l)).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => isIrreducible_segTerm σ a)
    fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (isSmooth_segTerm σ a)
      (isIrreducible_segTerm σ a) φ hφ

theorem hasFiniteLength_segTerm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    HasFiniteLength (segTerm σ.ρ l a) :=
  (⟨_, segTerm σ.ρ l a, isSmooth_segTerm σ a, isIrreducible_segTerm σ a⟩ :
    IrrRep (GL (Fin d) k)).hasFiniteLength


theorem exists_other {d l : ℕ} (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    {i j : Fin l} (h : b.1 i j < d) : ∃ j', j' ≠ j ∧ 0 < b.1 i j' := by
  by_contra hc
  push Not at hc
  have h2 := b.2.1 i
  simp only [Fintype.card_fin] at h2
  rw [Finset.sum_eq_single j (fun j' _ hj' => Nat.le_zero.1 (hc j' hj')) (by simp)] at h2
  omega


end PositivityTheory.Pf1.SegRepC.MultOne

end
