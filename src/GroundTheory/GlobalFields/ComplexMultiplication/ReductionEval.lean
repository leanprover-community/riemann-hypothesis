module

public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionLift
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Transport

theorem pointCongr_pointCongr {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (P : V₁.toAffine.Point) :
    pointCongr h₂ (pointCongr h₁ P) = pointCongr (h₁.trans h₂) P := by
  subst h₁; subst h₂; rfl

theorem pointMapRing_pointCongr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    pointMapRing f V₂ (pointCongr h P) =
      pointCongr (congrArg (fun V => V.map f) h) (pointMapRing f V₁ P) := by
  subst h; rfl

theorem pointMapRing_congr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    {f g : F →+* L} (h : f = g) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = pointCongr (by rw [h]) (pointMapRing g V P) := by
  subst h; rfl

theorem pointMapRing_pointMapRing {F L L' : Type*} [Field F] [Field L] [Field L'] [DecidableEq F]
    [DecidableEq L] [DecidableEq L'] (f : F →+* L) (g : L →+* L') (V : WeierstrassCurve F)
    (P : V.toAffine.Point) :
    pointMapRing g (V.map f) (pointMapRing f V P) = pointMapRing (g.comp f) V P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem map_eq_pointCongr_pointMapRing {R F₁ F₂ : Type*} [CommRing R] [Field F₁] [Field F₂]
    [Algebra R F₁] [Algebra R F₂] [DecidableEq F₁] [DecidableEq F₂] (V : WeierstrassCurve R)
    (σ : F₁ →ₐ[R] F₂) (P : (V.baseChange F₁).toAffine.Point) :
    Point.map σ P = pointCongr (by
        show V.map (σ.toRingHom.comp (algebraMap R F₁)) = V.map (algebraMap R F₂)
        exact congrArg V.map σ.comp_algebraMap) (pointMapRing σ.toRingHom (V.baseChange F₁) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (pointCongr _)).symm
  · rw [Point.map_some]
    obtain ⟨h', e⟩ := pointMapRing_some σ.toRingHom (V.baseChange F₁) h
    rw [e, pointCongr_some, Point.some.injEq]
    exact ⟨rfl, rfl⟩

theorem reducePoint_pointCongr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type*) [Field K] [Algebra 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
    {V₁ V₂ : WeierstrassCurve 𝒪} (h : V₁ = V₂) (P : (curveK K V₁).Point) :
    reducePoint K V₂ (pointCongr (congrArg (fun V => V.map (algebraMap 𝒪 K)) h) P) =
      pointCongr (congrArg (fun V => V.map (residue 𝒪)) h) (reducePoint K V₁ P) := by
  subst h; rfl

end Transport

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  (M : Type*) [Field M] [Algebra Λ M] [IsFractionRing Λ M] [Algebra K M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [IsDomain Λ]
  [IsDiscreteValuationRing Λ] [IsLocalHom j] [IsFractionRing Λ M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)] in
theorem map_baseChange_eq_map_of
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c)) :
    (W'.baseChange K).baseChange M = (W'.map j).map (algebraMap Λ M) := by
  show W'.map ((algebraMap K M).comp (algebraMap 𝒪 K)) = W'.map ((algebraMap Λ M).comp j)
  congr 1
  exact RingHom.ext hjM

variable {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
  (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem map_fieldEvalRed_eq :
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).map
      (fieldEvalRed W j hxy hx) = (W'.map j).map (residue Λ) := by
  show W'.map (((fieldEvalRed W j hxy hx).comp (algebraMap (ResidueField 𝒪) _)).comp
    (residue 𝒪)) = W'.map ((residue Λ).comp j)
  congr 1
  refine RingHom.ext fun c => ?_
  simp [fieldEvalRed_algebraMap, ResidueField.map_residue]

variable [W'.IsElliptic]

theorem reducePoint_genEval
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c))
    (hR : ((W.baseChange K).baseChange M).toAffine.Nonsingular (algebraMap Λ M x)
      (algebraMap Λ M y))
    (hRg : IsGenPt (W.baseChange K) (Point.some _ _ hR))
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reducePoint M (W'.map j) (pointCongr (map_baseChange_eq_map_of K W' j M hjM)
        (Point.map (genEval (W.baseChange K) _ hRg) Q)) =
      pointCongr (map_fieldEvalRed_eq W W' j hxy hx)
        (pointMapRing (fieldEvalRed W j hxy hx) _ (reduceFF K W W' Q)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  set σ := genEval (W.baseChange K) _ hRg
  have hσ : σ.toRingHom.comp (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
    apply comp_algebraMap_gaussLift
    · intro c
      show σ (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, σ.commutes, hjM]
    · exact genEval_genX _ _ hRg
    · exact genEval_genY _ _ hRg
  have c0 : (gaussCurve W W').map (gaussLift W j hxy hx) = W'.map j := by
    show W'.map ((gaussLift W j hxy hx).comp (algebraMap 𝒪 (gaussRing W))) = W'.map j
    exact congrArg W'.map (RingHom.ext (gaussLift_algebraMap_base W j hxy hx))
  set Q₀ := pointCongr (gaussCurve_map_functionField K W W').symm Q with hQ₀
  have hQ : Q = pointCongr (gaussCurve_map_functionField K W W') Q₀ := by
    rw [hQ₀, pointCongr_pointCongr]; rfl
  have key := reducePoint_pointMapRing (W.baseChange K).toAffine.FunctionField M hσ
    (gaussCurve W W') Q₀
  have lhs : pointCongr (map_baseChange_eq_map_of K W' j M hjM) (Point.map σ Q) =
      pointCongr (congrArg (fun V => V.map (algebraMap Λ M)) c0)
        (pointCongr (map_curveK_eq _ M hσ (gaussCurve W W')) (pointMapRing σ.toRingHom _ Q₀)) := by
    rw [map_eq_pointCongr_pointMapRing, hQ, pointMapRing_pointCongr, pointCongr_pointCongr,
      pointCongr_pointCongr, pointCongr_pointCongr]
  rw [lhs, reducePoint_pointCongr, key, pointMapRing_congr (residueField_map_gaussLift W j hxy hx),
    ← pointMapRing_pointMapRing]
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [pointMapRing_pointCongr]
  erw [pointCongr_pointCongr, pointCongr_pointCongr, pointCongr_pointCongr]
  · rfl
  · exact c0

end Eval

end

end GroundTheory.Global
