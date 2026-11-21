import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false
noncomputable section

open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.FlagZ.Loc

theorem isUnit_submatrix_castLE_of_upper {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (b : Matrix (Fin N) (Fin N) R) (hb : ∀ i j : Fin N, j < i → b i j = 0) (hu : IsUnit b) :
    IsUnit (b.submatrix (Fin.castLE hl) (Fin.castLE hl)) := by
  have h1 : b.BlockTriangular id := fun i j h => hb i j h
  have h2 : (b.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id :=
    fun i j h => hb _ _ h
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h1,
    IsUnit.prod_univ_iff] at hu
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular h2, IsUnit.prod_univ_iff]
  exact fun i => hu _




end GlobalTheory.FlagZ.Loc
