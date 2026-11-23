module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem isUnit_map_of_mul_eq_smul {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (g : R →+* D)
    (M M' : Matrix (Fin d) (Fin d) R) (r : R) (h : M * M' = r • (1 : Matrix (Fin d) (Fin d) R)) (hr : IsUnit (g r)) :
    IsUnit (M.map g) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 : M.map g * M'.map g = g r • (1 : Matrix (Fin d) (Fin d) D) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hr.pow d)

theorem wseed_F_frob_XZ_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  intro l _ K bk τ d ρ s Ψ Z hΨ hZ
  have hl := isUnit_l_disc l (X : bk.S) bk.ρ₀
  rw [Matrix.map_mul]
  refine IsUnit.mul ?_ (IsUnit.mul ?_ ?_)
  · refine isUnit_map_of_mul_eq_smul _ s.F s.F' _ s.F_mul ?_
    rw [map_pow, map_natCast]
    exact hl.pow _
  · have e : Ψ.comp (toDisc l (X : bk.S) bk.ρ₀) = (toDisc l (X : bk.S) bk.ρ₀).comp (frobS l bk.a) :=
      RingHom.ext hΨ.ext
    rw [Matrix.map_map, show (⇑Ψ ∘ ⇑(toDisc l (X : bk.S) bk.ρ₀)) = ⇑(Ψ.comp (toDisc l (X : bk.S) bk.ρ₀)) from rfl, e]
    refine isUnit_map_of_mul_eq_smul _ s.X s.X' _ s.X_mul ?_
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
    exact (hl.pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  · exact hZ.map (Ψ.mapMatrix)

end GlobalTheory.BKLim

end
