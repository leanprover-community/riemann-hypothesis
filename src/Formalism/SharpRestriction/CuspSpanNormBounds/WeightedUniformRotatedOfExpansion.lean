module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.RotatedPoints

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.S.Pv.Frames

section R

variable (D : D7)

variable {D}

theorem weighted_bound_rotated_of_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : Formalism.MainNotions.BesselShellMomentBounds.OnePlace D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : Formalism.MainNotions.OnePlaceEstimates.ConclusionB3 D Aw Ch Cg (CK + 6) := by
  exact Formalism.MainNotions.BesselShellMomentBounds.theorem_B_weighted_bound_one_place (D := D) hCg hO

variable (D)

def PlaceOKR (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec ∧
    Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T'

variable {D}

end R

def WeightedBoundRotatedUniform : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.ConclusionB3 D Aw Ch Cg Cb

end Formalism.MainNotions.RotatedPoints
