module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticUniformization

theorem exists_analyticIso_of_isAnalyticUniformization (Λ : Submodule ℤ ℂ)
    (E : WeierstrassCurve ℂ) (f : ℂ →+ E.toAffine.Point)
    (hf : GroundTheory.Global.Elliptic.IsAnalyticUniformization Λ f) :
    ∃ ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point,
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := by
  let φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point :=
    QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz
  have hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z := fun z => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hφ] at hx
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)
  have hsurj : Function.Surjective φ := fun P => by
    obtain ⟨z, rfl⟩ := hf.surjective P
    exact ⟨QuotientAddGroup.mk z, hφ z⟩
  let ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point :=
    AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := fun z => rfl
  refine ⟨ξ, fun z hz => ?_, hξ⟩
  have hz0 : f z ≠ 0 := fun h => hz ((hf.map_eq_zero_iff z).1 h)
  obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz0
  refine ⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩
  obtain ⟨h, hw⟩ := hw
  exact ⟨h, (hξ w).trans hw⟩

end GlobalTheory.CompanionTheory.EllipticUniformization
