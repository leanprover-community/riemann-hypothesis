module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (tens L M) hN).2 hT

end GlobalTheory.AV
