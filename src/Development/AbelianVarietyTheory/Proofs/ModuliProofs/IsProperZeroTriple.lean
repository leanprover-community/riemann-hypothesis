module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  haveI : IsIso (PSpace.str R 0) := by
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      rw [GlobalTheory.ProjSpace.opensRange_chartι, ← GlobalTheory.ProjSpace.iSup_chart R 0]
      apply le_antisymm (le_iSup _ 0)
      apply iSup_le
      intro i
      rw [Subsingleton.elim i 0]
    haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0 ≫ PSpace.str R 0) := by
      rw [GlobalTheory.ProjSpace.chartι_str]
      exact inferInstanceAs (IsIso (Spec.map
        (MvPolynomial.isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
    exact IsIso.of_isIso_comp_left (GlobalTheory.ProjSpace.chartι R 0 0) _
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Point

end
