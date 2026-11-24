module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_sec_of_eff {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (h : Eff (cls N hN)) :
    ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  obtain ⟨N', hN', hc, σ, j, hj⟩ := h
  obtain ⟨w, hw⟩ := (cls_eq_iff hN' hN).1 hc
  let e : LB.Sec N' ≃ₗ[Γ(X, ⊤)] LB.Sec N :=
    (SecOn.topEquiv N').symm ≪≫ₗ SecOn.congr hN' hN w hw ⊤ ≪≫ₗ SecOn.topEquiv N
  have hσ : σ ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have he : e σ ≠ 0 := by
    intro h0
    exact hσ (e.injective (h0.trans (map_zero e).symm))
  by_contra hne
  push_neg at hne
  exact he (HighTwist.sec_eq_zero _ (hne (e σ)))

end GlobalTheory.EffBound
