module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (f : G ⟶ G) [IsMonHom f] : IsTan (w ≫ f) := by
  unfold IsTan at hw ⊢
  rw [← Category.assoc, hw]
  first
  | simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def tvec (c : Fin n → R) : sp (R₀ := R) (DualNumber R) ⟶ G := spMap (dualLift c) ≫ x 1

include hx in
theorem isTan_tvec (c : Fin n → R) : IsTan (tvec (x := x) c) := isTan_dualLift hx c

private lemma sp_tangent_ext {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (hw' : IsTan w')
    (h : tcoord hx w hw = tcoord hx w' hw') : w = w' := by
  rw [tcoord_spec hx w hw, h, ← tcoord_spec hx w' hw']

theorem tcoord_tvec (c : Fin n → R) : tcoord hx (tvec (x := x) c) (isTan_tvec hx c) = c :=
  (exists_coord hx (tvec (x := x) c) (isTan_tvec hx c)).unique (tcoord_spec hx _ _) rfl

include hx in
theorem tvec_add (c c' : Fin n → R) : tvec (x := x) (c + c') = tvec (x := x) c * tvec (x := x) c' := by
  refine sp_tangent_ext hx (isTan_tvec hx (c + c')) (isTan_mul (isTan_tvec hx c) (isTan_tvec hx c')) ?_
  rw [tcoord_mul hx (isTan_tvec hx c) (isTan_tvec hx c'), tcoord_tvec, tcoord_tvec, tcoord_tvec]

include hx in
theorem tvec_smul (a : R) (c : Fin n → R) : tvec (x := x) (a • c) = spMap (scaleD a) ≫ tvec (x := x) c := by
  refine sp_tangent_ext hx (isTan_tvec hx (a • c)) (isTan_scale a (isTan_tvec hx c)) ?_
  rw [tcoord_scale hx a (isTan_tvec hx c), tcoord_tvec, tcoord_tvec]

theorem tcoord_congr {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (h : w = w') (hw : IsTan w) (hw' : IsTan w') :
    tcoord hx w hw = tcoord hx w' hw' := by
  subst h
  rfl

def tmap (f : G ⟶ G) [IsMonHom f] : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun c := tcoord hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)
  map_add' c c' := by
    have e : tvec (x := x) (c + c') ≫ f = (tvec (x := x) c ≫ f) * (tvec (x := x) c' ≫ f) := by
      rw [tvec_add hx, Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
    show tcoord hx _ _ = tcoord hx _ _ + tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_mul (isTan_comp (isTan_tvec hx c) f) (isTan_comp (isTan_tvec hx c') f)),
      tcoord_mul hx]
  map_smul' a c := by
    have e : tvec (x := x) (a • c) ≫ f = spMap (scaleD a) ≫ (tvec (x := x) c ≫ f) := by
      rw [tvec_smul hx, Category.assoc]
    show tcoord hx _ _ = a • tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_scale a (isTan_comp (isTan_tvec hx c) f)), tcoord_scale hx]

theorem tvec_tmap (f : G ⟶ G) [IsMonHom f] (c : Fin n → R) : tvec (x := x) (tmap hx f c) = tvec (x := x) c ≫ f :=
  (tcoord_spec hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)).symm

end ReciprocityTheory.ChartRestriction.G.Chart
