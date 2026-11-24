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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_nsmul_sub_eff : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  intro R _ Y f _ H m s M hH hM hs
  have hD : (dual M).IsLB := isLB_dual hM
  obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero R Y f H m s (dual M) hH hD hs
  refine ⟨(max t₀ 0).toNat, ?_⟩
  have hc : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  obtain ⟨σ, i, hσ⟩ := ht _ hc
  have key := eff_of_sec _ (isLB_tw hD hH _) σ i hσ
  have e : cls (tw (dual M) H ((max t₀ 0).toNat : ℤ)) (isLB_tw hD hH _) =
      cls (dual M) hD - cls (pw H (-((max t₀ 0).toNat : ℤ))) (isLB_pw hH _) :=
    cls_div hD (isLB_pw hH _) (isLB_tw hD hH _)
  rw [e, cls_pw hH, cls_dual hM hD, neg_zsmul, natCast_zsmul] at key
  convert key using 1
  abel
end GlobalTheory.EffBound
