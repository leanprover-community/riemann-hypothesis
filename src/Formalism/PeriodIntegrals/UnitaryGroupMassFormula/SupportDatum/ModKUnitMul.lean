import Mathlib
import Formalism.PeriodIntegrals.SupportParts

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CokDetL : Prop := ∀ (R : Type) [CommRing R] (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) R),
  Z.det ∈ nonZeroDivisors R → Z'.det ∈ nonZeroDivisors R →
  Nonempty (((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) →
  ∃ u : Rˣ, Z'.det = u * Z.det

def DetForm : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (T T' : ℕ),
  ∃ C : Option D.host.E → (D.s.atP p).Ep, ∀ (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)), modPt δ T T' p w = some a →
    a.mat.det = (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) * C (kind w)

theorem uLow_det {E : Type} [CommRing E] {n : ℕ} (x : Loc.IL n → E) : (Loc.uLow x).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => ?_)]
  · simp [Loc.uLow]
  · have hij' : i < j := hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt hij'), dif_neg (not_lt.2 hij'.le)]

theorem uUp_det {E : Type} [CommRing E] {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) :
    (Loc.uUp w y).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => ?_)]
  · simp [Loc.uUp]
  · have hij' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt hij'), dif_neg (fun h => absurd h.1 (not_lt.2 hij'.le))]






end PI.SupportDatumW
