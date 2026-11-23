module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiCoordRescaleLocal

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (q : D.X → (FractionRing R)ˣ) (y : D.X),
    PsiUnitOn D y Set.univ → ∀ s : R, (q y : FractionRing R) = algebraMap R (FractionRing R) s →
      ∃ u : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.PolDeg.rescale D q) y (u * s) := by
  intro R _ _ _ D q y h s hs
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord D y v := by
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D y j hj
    obtain ⟨t, ht, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 t
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤)
        GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 ht
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  have h2 : Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D q) y (s * (v : R)) := by
    obtain ⟨x, ⟨j, hj, hj', rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y v).1 hv
    refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) y (s * (v : R))).2
      ⟨q y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j hj, ⟨j, hj, hj', ?_⟩, ?_⟩
    · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
      rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
      congr 1
      ext
      show (q y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
        (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q y : FractionRing R)))
      rw [CategoryTheory.Functor.map_id]
      exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
    · rw [Units.val_mul, hs, e, map_mul]
  refine ⟨v, ?_⟩
  rw [mul_comm]
  exact h2

end GlobalTheory.PsiCoordRescaleLocal
