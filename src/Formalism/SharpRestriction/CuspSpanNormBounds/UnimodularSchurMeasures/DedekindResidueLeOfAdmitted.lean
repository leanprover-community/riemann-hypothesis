import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.CoveringRadius2

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

theorem qt_finrank (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    Module.finrank ℚ E = 2 * Formalism.HermitianLatticesTheory.fDeg E := by
  have := h.1
  have h1 := NumberField.IsTotallyComplex.finrank E
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem qt_bound_eq (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) (C : ℝ) :
    (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E =
      (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  rw [qt_finrank E h]
  push_cast
  rfl

theorem residue_admitted_of_known (hQ : Formalism.HermitianLatticeCounting.S7.DedekindZetaResidueBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C := by
  obtain ⟨C, hC, h⟩ := hQ
  refine ⟨C, hC, fun D E _ _ _ hE => ⟨dedekindZeta_residue E, tendsto_sub_one_mul_dedekindZeta_nhdsGT E, ?_⟩⟩
  rw [abs_of_pos (dedekindZeta_residue_pos E), ← qt_bound_eq E hE C]
  refine h E ?_
  rw [qt_finrank E hE]
  have : 0 < Formalism.HermitianLatticesTheory.fDeg E := Fintype.card_pos
  omega


section Cover

variable {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L] [IsZLattice ℝ L]

def qt_basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ (EuclideanSpace ℝ (Fin N)) :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L





end Cover




end Formalism.MainNotions.LeviCoordinates
