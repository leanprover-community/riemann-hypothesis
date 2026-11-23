module

public import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionAtPoint
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section OverF

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω]

omit [DecidableEq F] [PerfectField F] in
theorem app_eq_of_eq {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (φ : Isogeny E E')
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {P P' : (E.baseChange L).toAffine.Point}
    (h : P = P') (hP : IsGenPt E P) (hP' : IsGenPt E P') : φ.app P hP = φ.app P' hP' := by
  subst h
  rfl

theorem pointHomOver_comp {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E''.IsElliptic] (ψ : Isogeny E' E'') (φ : Isogeny E E') (R : E.toAffine.Point) :
    pointHomOver Ω (ψ.comp φ) R = pointHomOver Ω ψ (pointHomOver Ω φ R) := by
  apply constMap_injective E'' E.toAffine.FunctionField
  set R' := pointHomOver Ω φ R
  have hX' := isGenPt_genericPoint_add_constMap E' R'
  have e0 := app_genericPoint_add_constMap Ω φ R
  have h1 := app_genericPoint_add_constMap Ω (ψ.comp φ) R

  have e : φ.1 + constMap E' E.toAffine.FunctionField R' =
      Point.map φ.comap (genericPoint E' + constMap E' E'.toAffine.FunctionField R') := by
    rw [map_add (f := _), Isogeny.map_comap_genericPoint, map_constMap]
  have hY : IsGenPt E' (φ.1 + constMap E' E.toAffine.FunctionField R') := by
    rw [e]
    exact isGenPt_map E' φ.comap hX'
  have h2 : ψ.app (φ.1 + constMap E' E.toAffine.FunctionField R') hY =
      Point.map φ.comap (ψ.1 + constMap E'' E'.toAffine.FunctionField (pointHomOver Ω ψ R')) := by
    rw [← app_genericPoint_add_constMap Ω ψ R', Isogeny.map_app]
    exact app_eq_of_eq ψ e _ _
  rw [Isogeny.app_comp, app_eq_of_eq ψ e0 _ hY, h2, map_add (f := _), map_constMap, ← Isogeny.comp_val,
    add_right_inj] at h1
  exact h1.symm

theorem pointHomOver_congr {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E₁.IsElliptic] [E₁'.IsElliptic] (φ : Isogeny E E') (hE : E = E₁) (hE' : E' = E₁')
    (R : E.toAffine.Point) :
    pointHomOver Ω (φ.congr hE hE') (pointCongr hE R) = pointCongr hE' (pointHomOver Ω φ R) := by
  subst hE hE'
  rw [Isogeny.congr_rfl]
  rfl

end OverF

section Frobenius

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime] [CharP F p]

omit [PerfectField F] [E.IsElliptic] in
theorem frobeniusPoint_constMap {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (R : E.toAffine.Point) :
    frobeniusPoint E p L (constMap E L R) =
      constMap (frobeniusTwist E p) L (pointMapRing (frobenius F p) E R) := by
  rcases R with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := pointMapRing_some (frobenius F p) E h
    rw [e]
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Algebra.ofId_apply, frobenius_def, map_pow]

theorem pointHomOver_frobeniusIsogeny (R : E.toAffine.Point) :
    pointHomOver Ω (frobeniusIsogeny E p) R = pointMapRing (frobenius F p) E R := by
  have : CharP E.toAffine.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p
  apply constMap_injective (frobeniusTwist E p) E.toAffine.FunctionField
  have hX := isGenPt_genericPoint_add_constMap E R
  have h1 := app_genericPoint_add_constMap Ω (frobeniusIsogeny E p) R
  rw [frobeniusIsogeny_app, frobeniusPoint_add, frobeniusPoint_constMap] at h1
  have h2 : frobeniusPoint E p E.toAffine.FunctionField (genericPoint E) = (frobeniusIsogeny E p).1 :=
    rfl
  rw [h2, add_right_inj] at h1
  exact h1.symm

end Frobenius

end

end GroundTheory.Global
